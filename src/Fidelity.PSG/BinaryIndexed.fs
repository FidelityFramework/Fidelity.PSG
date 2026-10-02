namespace Fidelity.PSG

open BAREWire.Encoding
open BAREWire.Memory

/// Schema-generated composites use fixed-width directories. Strict BARE
/// scalar encodings are the leaves; no recursive stream scan locates a child.
module internal BinaryIndexed =
    let result = BinaryRuntime.result

    type Fragment =
        | Leaf of byte array
        | Branch of size: int * children: Fragment list

    let size = function Leaf bytes -> bytes.Length | Branch(size, _) -> size

    type WriteState = {
        Offset: int
        Depth: int
        Remaining: int
        Limits: BinaryLimits
        Children: Fragment list
        Parents: Fragment list list
    }

    type Location = { Offset: uint64; Length: uint64 }
    type Directory = { Children: Location array; Next: int }
    type ReadState = {
        Source: ByteSource
        Offset: int
        Depth: int
        Remaining: int
        Limits: BinaryLimits
        Current: Directory
        Parents: Directory list
    }

    let initialWrite limits : WriteState =
        { Offset = 0; Depth = 0; Remaining = limits.MaxValues; Limits = limits; Children = []; Parents = [] }

    let initialRead limits source (location: Location) : ReadState =
        { Source = source; Offset = int location.Offset; Depth = 0; Remaining = limits.MaxValues
          Limits = limits; Current = { Children = [|location|]; Next = 0 }; Parents = [] }

    let malformed (state: ReadState) reason = Error(BinaryError.Malformed(state.Offset, reason))

    let private sourceRead source (location: Location) =
        if location.Length > uint64 System.Int32.MaxValue then Error(BinaryError.LimitExceeded("MaxBytes", 0))
        else
            ByteSource.read location.Offset (int location.Length) source
            |> Result.mapError (function
                | SourceError.OutOfBounds -> BinaryError.Malformed(int location.Offset, "Indexed extent is outside the byte source")
                | SourceError.Unavailable reason -> BinaryError.SourceUnavailable(location.Offset, reason))

    let private reserve bytes (state: WriteState) =
        if state.Remaining <= 0 then Error(BinaryError.LimitExceeded("MaxValues", state.Offset))
        elif bytes < 0 || bytes > state.Limits.MaxBytes - state.Offset then Error(BinaryError.LimitExceeded("MaxBytes", state.Offset))
        else Ok { state with Offset = state.Offset + bytes; Remaining = state.Remaining - 1 }

    let enterWrite (state: WriteState) = result {
        if state.Depth >= state.Limits.MaxDepth then return! Error(BinaryError.LimitExceeded("MaxDepth", state.Offset))
        else
            let! state = reserve (8 + if state.Depth = 0 then 0 else 16) state
            return { state with Depth = state.Depth + 1; Parents = state.Children :: state.Parents; Children = [] }
    }

    let leaveWrite (state: WriteState) =
        let children = List.rev state.Children
        let fragment = Branch(8 + 16 * children.Length + (children |> List.sumBy size), children)
        { state with Depth = state.Depth - 1; Children = fragment :: List.head state.Parents; Parents = List.tail state.Parents }

    let private writeLeaf (writer: BinaryRuntime.WriteState -> 'a -> Result<BinaryRuntime.WriteState, BinaryError>) (state: WriteState) value = result {
        let primitive : BinaryRuntime.WriteState =
            { Data = None; Offset = 0; Depth = 0; Remaining = state.Remaining; Limits = state.Limits }
        let! measured = writer primitive value
        let overhead = if state.Depth = 0 then 0 else 16
        let! reserved = reserve (overhead + measured.Offset) state
        let data = Array.zeroCreate measured.Offset
        let! written = writer { primitive with Data = Some data } value
        return { reserved with Remaining = written.Remaining; Children = Leaf data :: state.Children }
    }

    let private nextLocation (state: ReadState) =
        if state.Current.Next >= state.Current.Children.Length then malformed state "The directory has fewer fields than its schema"
        else
            let location = state.Current.Children[state.Current.Next]
            Ok(location, { state with Offset = int location.Offset; Current = { state.Current with Next = state.Current.Next + 1 } })

    /// Validate the local directory, including exact contiguous partitioning.
    /// This checks no child payload and grants no whole-revision integrity.
    type private DirectoryShape = Exact of int | Maximum of int | Collection

    let private readDirectory shape limits remaining source (location: Location) = result {
        let minimum = match shape with Exact fields -> fields | Maximum _ | Collection -> 1
        if remaining < minimum then return! Error(BinaryError.LimitExceeded("MaxValues", int location.Offset))
        elif location.Length < 8UL || location.Length > uint64 limits.MaxBytes then
            return! Error(BinaryError.Malformed(int location.Offset, "Invalid directory extent"))
        else
            let! header = sourceRead source { location with Length = 8UL }
            let count, _ = Decoder.readU32 header 0
            let reserved, _ = Decoder.readU32 header 4
            if reserved <> 0u then return! Error(BinaryError.Malformed(int location.Offset, "Nonzero directory reserved word"))
            elif remaining < 0 || uint64 count > uint64 remaining then return! Error(BinaryError.LimitExceeded("MaxValues", int location.Offset))
            elif (match shape with Exact expected -> count <> uint32 expected | Maximum maximum -> count = 0u || uint64 count > uint64 maximum | Collection -> count = 0u) then
                return! Error(BinaryError.Malformed(int location.Offset, "Directory arity disagrees with its schema"))
            elif (match shape with Collection -> uint64 count > uint64 limits.MaxCollectionLength + 1UL | _ -> false) then
                return! Error(BinaryError.LimitExceeded("MaxCollectionLength", int location.Offset))
            elif uint64 count > (location.Length - 8UL) / 16UL then
                return! Error(BinaryError.Malformed(int location.Offset, "Directory count exceeds its extent"))
            else
                let tableSize = 16 * int count
                let! table = sourceRead source { Offset = location.Offset + 8UL; Length = uint64 tableSize }
                let dataStart = location.Offset + 8UL + uint64 tableSize
                let finish = location.Offset + location.Length
                let rec rows index expected accumulated =
                    if index = int count then
                        if expected <> finish then Error(BinaryError.Malformed(int expected, "Directory leaves unclaimed bytes"))
                        else Ok(List.rev accumulated |> List.toArray)
                    else
                        let offset, _ = Decoder.readU64 table (index * 16)
                        let length, _ = Decoder.readU64 table (index * 16 + 8)
                        if offset <> expected || offset > finish || length > finish - offset then
                            Error(BinaryError.Malformed(int location.Offset, "Directory offsets overlap, skip bytes, wrap, or leave the parent extent"))
                        else rows (index + 1) (offset + length) ({Offset = offset; Length = length} :: accumulated)
                return! rows 0 dataStart []
    }

    let fixedDirectory fields limits remaining source location = readDirectory (Exact fields) limits remaining source location
    let collectionDirectory limits remaining source location = readDirectory Collection limits remaining source location

    let private enterReadWith shape (state: ReadState) = result {
        if state.Remaining <= 0 then return! Error(BinaryError.LimitExceeded("MaxValues", state.Offset))
        elif state.Depth >= state.Limits.MaxDepth then return! Error(BinaryError.LimitExceeded("MaxDepth", state.Offset))
        else
            let! location, parent = nextLocation state
            let! children = readDirectory shape state.Limits (state.Remaining - 1) state.Source location
            return { parent with Depth = state.Depth + 1; Remaining = state.Remaining - 1
                                 Current = { Children = children; Next = 0 }; Parents = parent.Current :: parent.Parents }
    }

    let enterReadFields fields state = enterReadWith (Exact fields) state
    let enterReadCases maximum state = enterReadWith (Maximum maximum) state

    let finishRead value (state: ReadState) =
        if state.Current.Next <> state.Current.Children.Length then malformed state "The directory has more fields than its schema"
        else
            Ok(value, { state with Depth = state.Depth - 1; Current = List.head state.Parents; Parents = List.tail state.Parents })

    let private readLeaf requiredValues maxBytes limitName (reader: BinaryRuntime.ReadState -> Result<'a * BinaryRuntime.ReadState, BinaryError>) (state: ReadState) = result {
        if state.Remaining < requiredValues then return! Error(BinaryError.LimitExceeded("MaxValues", state.Offset))
        else
            let! location, after = nextLocation state
            if location.Length > uint64 maxBytes then
                if limitName = "" then return! malformed after "Scalar extent exceeds its fixed representation"
                else return! Error(BinaryError.LimitExceeded(limitName, int location.Offset))
            else
                let! data = sourceRead state.Source location
                let primitive : BinaryRuntime.ReadState =
                    { Data = data; Offset = 0; Depth = 0; Remaining = state.Remaining; Limits = state.Limits }
                let! value, consumed = reader primitive
                if consumed.Offset <> data.Length then return! malformed after "Scalar leaf has trailing bytes"
                else return value, { after with Remaining = consumed.Remaining }
    }

    let writeU8 state value = writeLeaf BinaryRuntime.writeU8 state value
    let readU8 state = readLeaf 1 1 "" BinaryRuntime.readU8 state
    let writeU16 state value = writeLeaf BinaryRuntime.writeU16 state value
    let readU16 state = readLeaf 1 2 "" BinaryRuntime.readU16 state
    let writeU32 state value = writeLeaf BinaryRuntime.writeU32 state value
    let readU32 state = readLeaf 1 4 "" BinaryRuntime.readU32 state
    let writeU64 state value = writeLeaf BinaryRuntime.writeU64 state value
    let readU64 state = readLeaf 1 8 "" BinaryRuntime.readU64 state
    let writeI32 state value = writeLeaf BinaryRuntime.writeI32 state value
    let readI32 state = readLeaf 1 4 "" BinaryRuntime.readI32 state
    let writeI64 state value = writeLeaf BinaryRuntime.writeI64 state value
    let readI64 state = readLeaf 1 8 "" BinaryRuntime.readI64 state
    let writeF64 state value = writeLeaf BinaryRuntime.writeF64 state value
    let readF64 state = readLeaf 1 8 "" BinaryRuntime.readF64 state
    let writeBool state value = writeLeaf BinaryRuntime.writeBool state value
    let readBool state = readLeaf 1 1 "" BinaryRuntime.readBool state
    let writeChar state value = writeLeaf BinaryRuntime.writeChar state value
    let readChar state = readLeaf 1 2 "" BinaryRuntime.readChar state
    let writeString state value = writeLeaf BinaryRuntime.writeString state value
    let readString (state: ReadState) = readLeaf 2 (state.Limits.MaxStringBytes + 10) "MaxStringBytes" BinaryRuntime.readString state
    let writeBigInteger state value = writeLeaf BinaryRuntime.writeBigInteger state value
    let readBigInteger (state: ReadState) = readLeaf 3 (state.Limits.MaxBigIntegerBytes + 11) "MaxBigIntegerBytes" BinaryRuntime.readBigInteger state
    let writeDecimal state value = writeLeaf BinaryRuntime.writeDecimal state value
    let readDecimal state = readLeaf 4 16 "" BinaryRuntime.readDecimal state
    let writeUInt state value = writeLeaf BinaryRuntime.writeUInt state value
    let readUInt state = readLeaf 1 10 "" BinaryRuntime.readUInt state
    let writeTag state value = writeLeaf BinaryRuntime.writeTag state value
    let readTag state = readLeaf 1 10 "" BinaryRuntime.readTag state

    let writeOption writer state value = result {
        let! state = enterWrite state
        match value with
        | None -> return! writeU8 state 0uy |> Result.map leaveWrite
        | Some value ->
            let! state = writeU8 state 1uy
            return! writer state value |> Result.map leaveWrite
    }
    let readOption reader state = result {
        let! state = enterReadCases 2 state
        let! tag, state = readU8 state
        match tag with
        | 0uy -> return! finishRead None state
        | 1uy ->
            let! value, state = reader state
            return! finishRead (Some value) state
        | _ -> return! malformed state "Invalid optional tag"
    }
    let writeResult okWriter errorWriter state value = result {
        let! state = enterWrite state
        match value with
        | Ok value ->
            let! state = writeU8 state 0uy
            return! okWriter state value |> Result.map leaveWrite
        | Error value ->
            let! state = writeU8 state 1uy
            return! errorWriter state value |> Result.map leaveWrite
    }
    let readResult okReader errorReader state = result {
        let! state = enterReadCases 2 state
        let! tag, state = readU8 state
        match tag with
        | 0uy ->
            let! value, state = okReader state
            return! finishRead (Ok value) state
        | 1uy ->
            let! value, state = errorReader state
            return! finishRead (Error value) state
        | _ -> return! malformed state "Invalid result tag"
    }
    let writeList writer state values = result {
        let! state = enterWrite state
        if List.length values > state.Limits.MaxCollectionLength then
            return! Error(BinaryError.LimitExceeded("MaxCollectionLength", state.Offset))
        else
            let! state = writeUInt state (uint64 values.Length)
            let rec loop state = function
                | [] -> Ok(leaveWrite state)
                | value :: rest -> writer state value |> Result.bind (fun state -> loop state rest)
            return! loop state values
    }
    let readList reader state = result {
        let! state = enterReadWith Collection state
        let! count, state = readUInt state
        if count > uint64 state.Limits.MaxCollectionLength then return! Error(BinaryError.LimitExceeded("MaxCollectionLength", state.Offset))
        elif count <> uint64 (state.Current.Children.Length - 1) then return! malformed state "Collection count disagrees with its directory"
        else
            let rec loop count state values =
                if count = 0UL then finishRead (List.rev values) state
                else reader state |> Result.bind (fun (value, state) -> loop (count - 1UL) state (value :: values))
            return! loop count state []
    }
    let writeArray writer (state: WriteState) values =
        if isNull values then Error(BinaryError.Malformed(state.Offset, "Null array"))
        elif Array.length values > state.Limits.MaxCollectionLength then Error(BinaryError.LimitExceeded("MaxCollectionLength", state.Offset))
        else writeList writer state (Array.toList values)
    let readArray reader state = readList reader state |> Result.map(fun (values, state) -> List.toArray values, state)
    let writeSet writer (state: WriteState) values =
        if Set.count values > state.Limits.MaxCollectionLength then Error(BinaryError.LimitExceeded("MaxCollectionLength", state.Offset))
        else writeList writer state (Set.toList values)
    let readSet reader state = result {
        let! values, state = readList reader state
        if values |> List.pairwise |> List.exists(fun (left, right) -> compare left right >= 0) then
            return! malformed state "Set members are duplicated or not in canonical order"
        else return Set.ofList values, state
    }
    let writeMap keyWriter valueWriter (state: WriteState) values =
        let entry state (key, value) = result {
            let! state = enterWrite state
            let! state = keyWriter state key
            let! state = valueWriter state value
            return leaveWrite state
        }
        if Map.count values > state.Limits.MaxCollectionLength then Error(BinaryError.LimitExceeded("MaxCollectionLength", state.Offset))
        else writeList entry state (Map.toList values)
    let readMap keyReader valueReader state =
        let entry state = result {
            let! state = enterReadFields 2 state
            let! key, state = keyReader state
            let! value, state = valueReader state
            return! finishRead (key, value) state
        }
        result {
            let! values, state = readList entry state
            if values |> List.pairwise |> List.exists(fun ((left, _), (right, _)) -> compare left right >= 0) then
                return! malformed state "Map keys are duplicated or not in canonical order"
            else return Map.ofList values, state
        }

    let fragment (state: WriteState) =
        match state.Children, state.Parents, state.Depth with
        | [root], [], 0 when size root = state.Offset -> Ok root
        | _ -> Error(BinaryError.Malformed(state.Offset, "Incomplete generated write"))

    /// All offsets are relative to byte zero of the revision, never addresses.
    let rec writeFragment data offset fragment =
        match fragment with
        | Leaf bytes -> Encoder.writeBytesRaw data offset bytes |> ignore
        | Branch(_, children) ->
            Encoder.writeU32 data offset (uint32 children.Length) |> ignore
            Encoder.writeU32 data (offset + 4) 0u |> ignore
            let rec rows index position = function
                | [] -> ()
                | child :: rest ->
                    Encoder.writeU64 data (offset + 8 + index * 16) (uint64 position) |> ignore
                    Encoder.writeU64 data (offset + 16 + index * 16) (uint64 (size child)) |> ignore
                    writeFragment data position child
                    rows (index + 1) (position + size child) rest
            rows 0 (offset + 8 + 16 * children.Length) children
