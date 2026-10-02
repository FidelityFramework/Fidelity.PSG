namespace Fidelity.PSG

open BAREWire.Encoding
open BAREWire.Memory

/// Bounded images of changed live-occurrence sections and their exact-base
/// transaction. This is the occurrence part of a scoped protocol, not an
/// executable semantic revision or a source/proof authorization verdict.
/// Complete Revision images have a different magic and are always refused.
module OccurrenceBinary =
    [<Literal>]
    let FormatVersion = 1u

    [<Literal>]
    let private HeaderSize = 64

    let private magic = [|70uy;80uy;83uy;71uy;79uy;67uy;67uy;49uy|] // FPSGOCC1

    /// The host owns stable bytes and their lifetime. A view neither installs a
    /// transaction nor grants current-source or execution authority.
    type View = private {
        Source: ByteSource
        Limits: BinaryLimits
        Root: BinaryIndexed.Location
    }

    let private malformed offset reason = Error(BinaryError.Malformed(offset, reason))

    let private checkDelivery delivery =
        match OccurrenceDelivery.check delivery with
        | [] -> Ok ()
        | violations -> Error(BinaryError.InvalidOccurrenceDelivery violations)

    /// Encode only the explicitly changed occurrence sections. Reauthorization
    /// of resident content carries no section, and retirement carries no body.
    let encode (limits: BinaryLimits) (delivery: OccurrenceDelivery) = BinaryRuntime.result {
        let! () = BinaryRuntime.validate limits
        if isNull (box delivery) then return! malformed 0 "Null occurrence delivery"
        elif limits.MaxBytes < HeaderSize then return! Error(BinaryError.LimitExceeded("MaxBytes", 0))
        else
            let! () = checkDelivery delivery
            let! planned = BinaryGenerated.writeOccurrenceDelivery
                                (BinaryIndexed.initialWrite {limits with MaxBytes = limits.MaxBytes - HeaderSize}) delivery
            let! fragment = BinaryIndexed.fragment planned
            let bytes = Array.zeroCreate (HeaderSize + BinaryIndexed.size fragment)
            Encoder.writeBytesRaw bytes 0 magic |> ignore
            Encoder.writeU32 bytes 8 FormatVersion |> ignore
            Encoder.writeI32 bytes 12 BinaryGenerated.Schema |> ignore
            Encoder.writeBytesRaw bytes 16 (System.Convert.FromHexString BinaryGenerated.Fingerprint) |> ignore
            Encoder.writeU64 bytes 48 (uint64 HeaderSize) |> ignore
            Encoder.writeU64 bytes 56 (uint64 bytes.Length) |> ignore
            BinaryIndexed.writeFragment bytes HeaderSize fragment
            return bytes
    }

    /// Check the occurrence envelope before any body is read. Source facts and
    /// receiver resident-base checks are separate from this representation check.
    let openSource (limits: BinaryLimits) (source: ByteSource) = BinaryRuntime.result {
        let! () = BinaryRuntime.validate limits
        let length = ByteSource.length source
        if length > uint64 limits.MaxBytes then return! Error(BinaryError.LimitExceeded("MaxBytes", 0))
        elif length < uint64 HeaderSize then return! malformed 0 "Truncated occurrence header"
        else
            let! header = ByteSource.read 0UL HeaderSize source |> Result.mapError(function
                | SourceError.OutOfBounds -> BinaryError.Malformed(0, "Occurrence header is outside the byte source")
                | SourceError.Unavailable reason -> BinaryError.SourceUnavailable(0UL, reason))
            if header[..7] <> magic then return! malformed 0 "Unknown occurrence image magic"
            else
                let format, _ = Decoder.readU32 header 8
                let schema, _ = Decoder.readI32 header 12
                let rootOffset, _ = Decoder.readU64 header 48
                let total, _ = Decoder.readU64 header 56
                if format <> FormatVersion then return! Error(BinaryError.UnsupportedFormat format)
                elif schema <> BinaryGenerated.Schema then return! Error(BinaryError.SchemaMismatch(BinaryGenerated.Schema, schema))
                elif System.Convert.ToHexString(header[16..47]) <> BinaryGenerated.Fingerprint then
                    return! Error BinaryError.ContractMismatch
                elif rootOffset <> uint64 HeaderSize || total <> length then
                    return! malformed 48 "Occurrence root offset or extent disagrees with the image"
                else
                    return { Source = source; Limits = limits; Root = {Offset = rootOffset; Length = total - rootOffset} }
    }

    /// Read and check the changed sections. This never calls the complete
    /// Revision codec and never resolves a context handle into a node body.
    let readDelivery (view: View) = BinaryRuntime.result {
        let! delivery, state = BinaryGenerated.readOccurrenceDelivery
                                    (BinaryIndexed.initialRead view.Limits view.Source view.Root)
        if state.Depth <> 0 || not state.Parents.IsEmpty || state.Current.Next <> 1 then
            return! malformed state.Offset "Incomplete occurrence read"
        else
            let! () = checkDelivery delivery
            return delivery
    }

    let decode limits (bytes: byte array) =
        BinaryRuntime.validate limits |> Result.bind(fun () ->
            if isNull bytes then malformed 0 "Null occurrence image"
            elif bytes.Length > limits.MaxBytes then Error(BinaryError.LimitExceeded("MaxBytes", 0))
            else openSource limits (ByteSource.ofArray bytes) |> Result.bind readDelivery)
