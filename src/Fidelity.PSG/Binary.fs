namespace Fidelity.PSG

/// Complete revision snapshots. This boundary preserves stored facts and checks
/// structural integrity; it never computes source semantics or renumbers nodes.
module Binary =
    type Limits = BinaryLimits
    type Error = BinaryError

    [<Literal>]
    let FormatVersion = BinaryGenerated.Format
    [<Literal>]
    let ContractFingerprint = BinaryGenerated.Fingerprint

    let private write (state: BinaryRuntime.WriteState) revision = BinaryRuntime.result {
        let! state = BinaryRuntime.writeU32 state FormatVersion
        let! state = BinaryRuntime.writeI32 state BinaryGenerated.Schema
        let! state = BinaryRuntime.writeRaw state (System.Convert.FromHexString ContractFingerprint)
        return! BinaryGenerated.writeRevision state revision
    }

    /// Encode with an exact-size first pass. Invalid revisions are refused.
    let encode (limits: Limits) (revision: Revision) : Result<byte array, Error> = BinaryRuntime.result {
        let! () = BinaryRuntime.validate limits
        let initial : BinaryRuntime.WriteState =
            { Data = None; Offset = 0; Depth = 0; Remaining = limits.MaxValues; Limits = limits }
        let! measured = write initial revision
        let failures = Integrity.check revision
        if not failures.IsEmpty then return! Error (BinaryError.InvalidRevision failures)
        else
            let bytes = Array.zeroCreate measured.Offset
            let! written = write { initial with Data = Some bytes } revision
            if written.Offset <> bytes.Length then
                return! Error (BinaryError.Malformed(written.Offset, "Encoded extent changed between measurement and writing"))
            else return bytes
    }

    /// Decode one exact snapshot. Incompatible, malformed, excessive or
    /// structurally inconsistent data has no partially accepted revision.
    let decode (limits: Limits) (bytes: byte array) : Result<Revision, Error> = BinaryRuntime.result {
        let! () = BinaryRuntime.validate limits
        if isNull bytes then return! Error (BinaryError.Malformed(0, "Null snapshot"))
        elif bytes.Length > limits.MaxBytes then return! Error (BinaryError.LimitExceeded("MaxBytes", 0))
        else
            let initial : BinaryRuntime.ReadState =
                { Data = bytes; Offset = 0; Depth = 0; Remaining = limits.MaxValues; Limits = limits }
            let! format, state = BinaryRuntime.readU32 initial
            if format <> FormatVersion then return! Error (BinaryError.UnsupportedFormat format)
            else
                let! schema, state = BinaryRuntime.readI32 state
                if schema <> BinaryGenerated.Schema then return! Error (BinaryError.SchemaMismatch(BinaryGenerated.Schema, schema))
                else
                    let! fingerprint, state = BinaryRuntime.readRaw 32 state
                    if System.Convert.ToHexString fingerprint <> ContractFingerprint then return! Error BinaryError.ContractMismatch
                    else
                        let! revision, state = BinaryGenerated.readRevision state
                        if state.Offset <> bytes.Length then return! Error (BinaryError.Malformed(state.Offset, "Trailing snapshot bytes"))
                        else
                            let failures = Integrity.check revision
                            if not failures.IsEmpty then return! Error (BinaryError.InvalidRevision failures)
                            else return revision
    }
