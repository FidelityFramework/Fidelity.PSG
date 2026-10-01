namespace Fidelity.PSG

open BAREWire.Encoding

/// Bounded, owned byte extents and immutable cursor/budget threading. The only
/// writes are BAREWire writes to the output allocated by this encode operation.
module internal BinaryRuntime =
    type ResultBuilder() =
        member _.Bind(value, next) = Result.bind next value
        member _.Return(value) = Ok value
        member _.ReturnFrom(value) = value
    let result = ResultBuilder()

    type WriteState = {
        Data: byte array option
        Offset: int
        Depth: int
        Remaining: int
        Limits: BinaryLimits
    }
    type ReadState = {
        Data: byte array
        Offset: int
        Depth: int
        Remaining: int
        Limits: BinaryLimits
    }

    let validate (limits: BinaryLimits) =
        [ "MaxBytes", limits.MaxBytes > 0 && limits.MaxBytes <= System.Int32.MaxValue / 4
          "MaxCollectionLength", limits.MaxCollectionLength >= 0
          "MaxDepth", limits.MaxDepth > 0 && limits.MaxDepth <= 256
          "MaxStringBytes", limits.MaxStringBytes >= 0 && limits.MaxStringBytes <= limits.MaxBytes
          "MaxBigIntegerBytes", limits.MaxBigIntegerBytes >= 0 && limits.MaxBigIntegerBytes <= limits.MaxBytes
          "MaxValues", limits.MaxValues > 0 ]
        |> List.tryFind (snd >> not)
        |> function Some (name, _) -> Error (BinaryError.InvalidLimits name) | None -> Ok ()

    let private spendWrite (state: WriteState) =
        if state.Remaining <= 0 then Error (BinaryError.LimitExceeded("MaxValues", state.Offset))
        else Ok { state with Remaining = state.Remaining - 1 }
    let private spendRead (state: ReadState) =
        if state.Remaining <= 0 then Error (BinaryError.LimitExceeded("MaxValues", state.Offset))
        else Ok { state with Remaining = state.Remaining - 1 }

    let enterWrite (state: WriteState) = result {
        let! state = spendWrite state
        if state.Depth >= state.Limits.MaxDepth then
            return! Error (BinaryError.LimitExceeded("MaxDepth", state.Offset))
        else return { state with Depth = state.Depth + 1 }
    }
    let enterRead (state: ReadState) = result {
        let! state = spendRead state
        if state.Depth >= state.Limits.MaxDepth then
            return! Error (BinaryError.LimitExceeded("MaxDepth", state.Offset))
        else return { state with Depth = state.Depth + 1 }
    }
    let leaveWrite (state: WriteState) = { state with Depth = state.Depth - 1 }
    let leaveRead (state: ReadState) = { state with Depth = state.Depth - 1 }
    let malformed (state: ReadState) reason = Error (BinaryError.Malformed(state.Offset, reason))

    let private write size encoder value (state: WriteState) = result {
        let! state = spendWrite state
        if size < 0 || size > state.Limits.MaxBytes - state.Offset then
            return! Error (BinaryError.LimitExceeded("MaxBytes", state.Offset))
        else
            // The first pass measures exactly. The second writes into that
            // exact extent; capacity is never a silent growth policy.
            let next =
                match state.Data with
                | None -> state.Offset + size
                | Some data -> encoder data state.Offset value
            if next <> state.Offset + size then
                return! Error (BinaryError.Malformed(state.Offset, "Encoder extent disagrees with its declared size"))
            else return { state with Offset = next }
    }
    let private read decoder (state: ReadState) = result {
        let! state = spendRead state
        let value, next = decoder state.Data state.Offset
        if Cursor.isFault next then return! malformed state "Truncated or malformed BARE value"
        else return value, { state with Offset = next }
    }
    let rec private uintSize (value: uint64) = if value < 128UL then 1 else 1 + uintSize (value >>> 7)
    let writeU8 state value = write 1 Encoder.writeU8 value state
    let readU8 state = read Decoder.readU8 state
    let writeU16 state value = write 2 Encoder.writeU16 value state
    let readU16 state = read Decoder.readU16 state
    let writeU32 state value = write 4 Encoder.writeU32 value state
    let readU32 state = read Decoder.readU32 state
    let writeU64 state value = write 8 Encoder.writeU64 value state
    let readU64 state = read Decoder.readU64 state
    let writeI32 state value = write 4 Encoder.writeI32 value state
    let readI32 state = read Decoder.readI32 state
    let writeI64 state value = write 8 Encoder.writeI64 value state
    let readI64 state = read Decoder.readI64 state
    let writeF64 state value = write 8 Encoder.writeF64 value state
    let readF64 state = read Decoder.readF64 state
    let writeBool state value = write 1 Encoder.writeBool value state
    let readBool state = read Decoder.readBool state
    let writeChar state (value: char) = writeU16 state (uint16 value)
    let readChar state = readU16 state |> Result.map (fun (value, state) -> char value, state)
    let writeUInt state value = write (uintSize value) Encoder.writeUInt value state
    let readUInt (state: ReadState) =
        read Decoder.readUInt state |> Result.bind (fun (value, after) ->
            if after.Offset - state.Offset <> uintSize value then malformed state "Noncanonical unsigned integer"
            else Ok(value, after))
    let writeTag state (value: int) = writeUInt state (uint64 value)
    let readTag state = readUInt state |> Result.bind (fun (value, state) ->
        if value > uint64 System.Int32.MaxValue then malformed state "Union tag exceeds int32"
        else Ok(int value, state))

    let writeRaw (state: WriteState) (bytes: byte array) = write bytes.Length Encoder.writeBytesRaw bytes state
    let readRaw count state = read (fun data offset -> Decoder.readBytesRaw data offset count) state
    let private writeBytes limitName limit (state: WriteState) (bytes: byte array) = result {
        if bytes.Length > limit then return! Error (BinaryError.LimitExceeded(limitName, state.Offset))
        else
            let! state = writeUInt state (uint64 bytes.Length)
            return! writeRaw state bytes
    }
    let private readBytes limitName limit (state: ReadState) = result {
        let! length, state = readUInt state
        if length > uint64 limit then return! Error (BinaryError.LimitExceeded(limitName, state.Offset))
        elif length > uint64 (Cursor.remaining state.Data state.Offset) then return! malformed state "Truncated byte extent"
        else return! readRaw (int length) state
    }

    let writeString (state: WriteState) (value: string) =
        if isNull value then Error (BinaryError.Malformed(state.Offset, "Null string"))
        elif value.Length > state.Limits.MaxStringBytes then Error (BinaryError.LimitExceeded("MaxStringBytes", state.Offset))
        else
            let bytes = Text.toUtf8 value
            if Text.ofUtf8 bytes <> value then Error (BinaryError.Malformed(state.Offset, "String contains an unpaired UTF-16 surrogate"))
            else writeBytes "MaxStringBytes" state.Limits.MaxStringBytes state bytes
    let readString (state: ReadState) = result {
        let! bytes, after = readBytes "MaxStringBytes" state.Limits.MaxStringBytes state
        let value = Text.ofUtf8 bytes
        if Text.toUtf8 value <> bytes then return! malformed state "Malformed UTF-8"
        else return value, after
    }

    let writeBigInteger (state: WriteState) (value: bigint) =
        if value.GetByteCount() > state.Limits.MaxBigIntegerBytes + 1 then
            Error (BinaryError.LimitExceeded("MaxBigIntegerBytes", state.Offset))
        else
            let sign = if value.IsZero then 0uy elif value.Sign > 0 then 1uy else 2uy
            let bytes = if value.IsZero then [||] else (bigint.Abs value).ToByteArray(isUnsigned = true, isBigEndian = false)
            result {
                let! state = writeU8 state sign
                return! writeBytes "MaxBigIntegerBytes" state.Limits.MaxBigIntegerBytes state bytes
            }
    let readBigInteger (state: ReadState) = result {
        let! sign, afterSign = readU8 state
        let! bytes, after = readBytes "MaxBigIntegerBytes" state.Limits.MaxBigIntegerBytes afterSign
        if sign > 2uy || (sign = 0uy && bytes.Length <> 0) || (sign <> 0uy && (bytes.Length = 0 || bytes[bytes.Length - 1] = 0uy)) then
            return! malformed state "Noncanonical signed-magnitude integer"
        else
            let magnitude = System.Numerics.BigInteger(bytes, isUnsigned = true, isBigEndian = false)
            return (if sign = 2uy then -magnitude else magnitude), after
    }
    let writeDecimal state (value: decimal) =
        let bits = System.Decimal.GetBits value
        result {
            let! state = writeI32 state bits[0]
            let! state = writeI32 state bits[1]
            let! state = writeI32 state bits[2]
            return! writeI32 state bits[3]
        }
    let readDecimal (state: ReadState) = result {
        let! lo, state = readI32 state
        let! mid, state = readI32 state
        let! hi, state = readI32 state
        let! flags, state = readI32 state
        if flags &&& 0x7F00FFFF <> 0 || ((flags >>> 16) &&& 255) > 28 then
            return! malformed state "Invalid decimal flags"
        else return System.Decimal([|lo; mid; hi; flags|]), state
    }

    let writeOption writer state value = result {
        let! state = enterWrite state
        return!
            match value with
            | None -> writeU8 state 0uy |> Result.map leaveWrite
            | Some value -> result {
                let! state = writeU8 state 1uy
                let! state = writer state value
                return leaveWrite state
              }
    }
    let readOption reader state = result {
        let! state = enterRead state
        let! tag, state = readU8 state
        return!
            match tag with
            | 0uy -> Ok(None, leaveRead state)
            | 1uy -> reader state |> Result.map (fun (value, state) -> Some value, leaveRead state)
            | _ -> malformed state "Invalid optional tag"
    }
    let writeResult okWriter errorWriter state value = result {
        let! state = enterWrite state
        return!
            match value with
            | Ok value -> result {
                let! state = writeU8 state 0uy
                let! state = okWriter state value
                return leaveWrite state
              }
            | Error value -> result {
                let! state = writeU8 state 1uy
                let! state = errorWriter state value
                return leaveWrite state
              }
    }
    let readResult okReader errorReader state = result {
        let! state = enterRead state
        let! tag, state = readU8 state
        return!
            match tag with
            | 0uy -> okReader state |> Result.map (fun (value, state) -> Ok value, leaveRead state)
            | 1uy -> errorReader state |> Result.map (fun (value, state) -> Error value, leaveRead state)
            | _ -> malformed state "Invalid result tag"
    }

    let writeList writer (state: WriteState) values = result {
        let! state = enterWrite state
        let count = List.length values
        if count > state.Limits.MaxCollectionLength then return! Error (BinaryError.LimitExceeded("MaxCollectionLength", state.Offset))
        else
            let! state = writeUInt state (uint64 count)
            let rec loop state = function
                | [] -> Ok(leaveWrite state)
                | value :: rest ->
                    match writer state value with
                    | Error error -> Error error
                    | Ok state -> loop state rest
            return! loop state values
    }
    let readList reader (state: ReadState) = result {
        let! state = enterRead state
        let! count, state = readUInt state
        if count > uint64 state.Limits.MaxCollectionLength then return! Error (BinaryError.LimitExceeded("MaxCollectionLength", state.Offset))
        elif count > uint64 state.Remaining then return! Error (BinaryError.LimitExceeded("MaxValues", state.Offset))
        else
            let rec loop remaining state accumulated =
                if remaining = 0UL then Ok(List.rev accumulated, leaveRead state)
                else
                    match reader state with
                    | Error error -> Error error
                    | Ok(value, state) -> loop (remaining - 1UL) state (value :: accumulated)
            return! loop count state []
    }
    let writeArray writer state values = writeList writer state (Array.toList values)
    let readArray reader state = readList reader state |> Result.map (fun (values, state) -> List.toArray values, state)

    let writeSet writer state values = writeList writer state (Set.toList values)
    let readSet reader state = result {
        let! values, state = readList reader state
        let rec ordered = function
            | first :: (second :: _ as rest) -> compare first second < 0 && ordered rest
            | _ -> true
        if not (ordered values) then return! malformed state "Set members are duplicated or not in canonical order"
        else return Set.ofList values, state
    }
    let writeMap keyWriter valueWriter state values =
        let writeEntry state (key, value) = result {
            let! state = keyWriter state key
            return! valueWriter state value
        }
        writeList writeEntry state (Map.toList values)
    let readMap keyReader valueReader state =
        let readEntry state = result {
            let! key, state = keyReader state
            let! value, state = valueReader state
            return (key, value), state
        }
        result {
            let! values, state = readList readEntry state
            let rec ordered = function
                | (first, _) :: (((second, _) :: _) as rest) -> compare first second < 0 && ordered rest
                | _ -> true
            if not (ordered values) then return! malformed state "Map keys are duplicated or not in canonical order"
            else return Map.ofList values, state
        }
