namespace Fidelity.PSG

open BAREWire.Encoding
open BAREWire.Memory

/// Complete, position-independent revision images. The same generated reader
/// reads an owned array or a stable host byte source; neither settles semantics.
module Binary =
    type Limits = BinaryLimits
    type Error = BinaryError

    [<Literal>]
    let FormatVersion = BinaryGenerated.Format
    [<Literal>]
    let ContractFingerprint = BinaryGenerated.Fingerprint
    [<Literal>]
    let private HeaderSize = 64

    /// An envelope and sorted node index have been checked. A View is NOT a
    /// complete integrity verdict, proof receipt, or current-source authority.
    /// The supplying host keeps bytes stable and owns the source's lifetime.
    type View = private {
        Source: ByteSource
        Limits: Limits
        Root: BinaryIndexed.Location
        Nodes: (NodeId * BinaryIndexed.Location) array
    }

    let private magic = [|70uy;80uy;83uy;71uy;73uy;68uy;88uy;50uy|] // FPSGIDX2
    let private malformed at reason = Result.Error(BinaryError.Malformed(at, reason))
    let private readSource source offset length =
        ByteSource.read offset length source
        |> Result.mapError(function
            | SourceError.OutOfBounds -> BinaryError.Malformed(int offset, "Extent is outside the byte source")
            | SourceError.Unavailable reason -> BinaryError.SourceUnavailable(offset, reason))

    let private readAt (reader: BinaryIndexed.ReadState -> Result<'a * BinaryIndexed.ReadState, Error>) limits source location =
        reader (BinaryIndexed.initialRead limits source location)
        |> Result.bind(fun (value, state) ->
            if state.Depth <> 0 || not state.Parents.IsEmpty || state.Current.Next <> 1 then
                malformed state.Offset "Incomplete generated read"
            else Ok value)

    /// Encode a complete, structurally valid image. All references in its
    /// directories are uint64 offsets from the start of this image, never addresses.
    let encode (limits: Limits) (revision: Revision) : Result<byte array, Error> = BinaryRuntime.result {
        let! () = BinaryRuntime.validate limits
        if isNull (box revision) then return! malformed 0 "Null revision"
        elif limits.MaxBytes < HeaderSize then return! Error(BinaryError.LimitExceeded("MaxBytes", 0))
        else
            let payloadLimits = { limits with MaxBytes = limits.MaxBytes - HeaderSize }
            let! planned = BinaryGenerated.writeRevision (BinaryIndexed.initialWrite payloadLimits) revision
            let! fragment = BinaryIndexed.fragment planned
            let failures = Integrity.check revision
            if not failures.IsEmpty then return! Error(BinaryError.InvalidRevision failures)
            else
                let bytes = Array.zeroCreate (HeaderSize + BinaryIndexed.size fragment)
                Encoder.writeBytesRaw bytes 0 magic |> ignore
                Encoder.writeU32 bytes 8 FormatVersion |> ignore
                Encoder.writeI32 bytes 12 BinaryGenerated.Schema |> ignore
                Encoder.writeBytesRaw bytes 16 (System.Convert.FromHexString ContractFingerprint) |> ignore
                Encoder.writeU64 bytes 48 (uint64 HeaderSize) |> ignore
                Encoder.writeU64 bytes 56 (uint64 bytes.Length) |> ignore
                BinaryIndexed.writeFragment bytes HeaderSize fragment
                return bytes
    }

    /// Check the envelope and complete sorted node index, without reading node
    /// bodies or sibling fact tables. Use readRevision for complete integrity.
    let openSource (limits: Limits) (source: ByteSource) : Result<View, Error> = BinaryRuntime.result {
        let! () = BinaryRuntime.validate limits
        let length = ByteSource.length source
        if length > uint64 limits.MaxBytes then return! Error(BinaryError.LimitExceeded("MaxBytes", 0))
        elif length < uint64 HeaderSize then return! malformed 0 "Truncated indexed revision header"
        else
            let! header = readSource source 0UL HeaderSize
            if header[..7] <> magic then return! malformed 0 "Unknown indexed revision magic"
            else
                let format, _ = Decoder.readU32 header 8
                let schema, _ = Decoder.readI32 header 12
                let rootOffset, _ = Decoder.readU64 header 48
                let total, _ = Decoder.readU64 header 56
                if format <> FormatVersion then return! Error(BinaryError.UnsupportedFormat format)
                elif schema <> BinaryGenerated.Schema then return! Error(BinaryError.SchemaMismatch(BinaryGenerated.Schema, schema))
                elif System.Convert.ToHexString(header[16..47]) <> ContractFingerprint then return! Error BinaryError.ContractMismatch
                elif rootOffset <> uint64 HeaderSize || total <> length then return! malformed 48 "Root offset or total extent disagrees with the image"
                else
                    let root : BinaryIndexed.Location = { Offset = rootOffset; Length = total - rootOffset }
                    let! fields = BinaryIndexed.fixedDirectory BinaryGenerated.RevisionFields limits (limits.MaxValues - 1) source root
                    if fields.Length <> BinaryGenerated.RevisionFields then return! malformed HeaderSize "Revision directory disagrees with its schema"
                    else
                        if limits.MaxDepth < 2 then return! Error(BinaryError.LimitExceeded("MaxDepth", int fields[BinaryGenerated.RevisionNodesField].Offset))
                        else
                          let! nodes = BinaryIndexed.collectionDirectory limits (limits.MaxValues - 2) source fields[BinaryGenerated.RevisionNodesField]
                          if nodes.Length = 0 then return! malformed HeaderSize "Node map has no count"
                          else
                            let! count, countState = BinaryIndexed.readUInt (BinaryIndexed.initialRead {limits with MaxValues = limits.MaxValues - 2} source nodes[0])
                            if count > uint64 limits.MaxCollectionLength then return! Error(BinaryError.LimitExceeded("MaxCollectionLength", int nodes[0].Offset))
                            elif count <> uint64 (nodes.Length - 1) then return! malformed (int nodes[0].Offset) "Node map count disagrees with its directory"
                            else
                                let rec index at prior remaining accumulated = BinaryRuntime.result {
                                    if at = nodes.Length then return List.rev accumulated |> List.toArray
                                    elif remaining <= 0 then return! Error(BinaryError.LimitExceeded("MaxValues", int nodes[at].Offset))
                                    elif limits.MaxDepth < 3 then return! Error(BinaryError.LimitExceeded("MaxDepth", int nodes[at].Offset))
                                    else
                                        let! entry = BinaryIndexed.fixedDirectory 2 limits (remaining - 1) source nodes[at]
                                        if entry.Length <> 2 then return! malformed (int nodes[at].Offset) "Node map entry is not a key/value pair"
                                        else
                                            let keyState = {BinaryIndexed.initialRead {limits with MaxValues = remaining - 1} source entry[0] with Depth = 3}
                                            let! key, state = BinaryGenerated.read_Fidelity_PSG_NodeId keyState
                                            if prior |> Option.exists(fun previous -> compare previous key >= 0) then return! malformed (int entry[0].Offset) "Node identities are duplicated or not in canonical order"
                                            else return! index (at + 1) (Some key) state.Remaining ((key, entry[1]) :: accumulated)
                                }
                                let! entries = index 1 None countState.Remaining []
                                return { Source = source; Limits = limits; Root = root; Nodes = entries }
    }

    /// Random access to one node in the checked index. Sibling payloads are not
    /// visited and may still be malformed; this is a reading, not graph admission.
    let tryNode (id: NodeId) (view: View) : Result<SemanticNode option, Error> =
        let rec find low high =
            if low > high then Ok None
            else
                let middle = low + (high - low) / 2
                let key, location = view.Nodes[middle]
                let order = compare id key
                if order < 0 then find low (middle - 1)
                elif order > 0 then find (middle + 1) high
                else
                    readAt BinaryGenerated.read_Fidelity_PSG_SemanticNode view.Limits view.Source location
                    |> Result.bind(fun node ->
                        if node.Id <> key then malformed (int location.Offset) "Node identity disagrees with its index key"
                        else Ok(Some node))
        // Absence is cached in the index, but a retained view still belongs to
        // its byte source's lifetime even when no node payload is needed.
        readSource view.Source 0UL 0
        |> Result.bind(fun _ -> find 0 (view.Nodes.Length - 1))

    /// Read every stored field and check complete structural integrity. This does
    /// not discharge a proof, establish provenance, or grant execution permission.
    let readRevision (view: View) : Result<Revision, Error> =
        readAt BinaryGenerated.readRevision view.Limits view.Source view.Root
        |> Result.bind(fun revision ->
            match Integrity.check revision with
            | [] -> Ok revision
            | failures -> Error(BinaryError.InvalidRevision failures))

    /// Array convenience over the same indexed reader used by mapped hosts.
    let decode (limits: Limits) (bytes: byte array) : Result<Revision, Error> =
        BinaryRuntime.validate limits |> Result.bind(fun () ->
            if isNull bytes then malformed 0 "Null snapshot"
            elif bytes.Length > limits.MaxBytes then Error(BinaryError.LimitExceeded("MaxBytes", 0))
            else openSource limits (ByteSource.ofArray bytes) |> Result.bind readRevision)
