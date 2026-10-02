namespace Fidelity.PSG.Json

open Fidelity.PSG
open Fidelity.Data.JSON

/// On-demand inspection of a complete image through the shared binary reader.
/// No JSON reader or compiler proof receipt is introduced by this projection.
module Inspection =
    let read (view: Binary.View) : Result<JsonValue, Binary.Error> =
        Binary.readRevision view |> Result.map (fun revision ->
            JsonValue.Object [
                "$format", JsonValue.String "fidelity-psg-inspection/1"
                "schema", JsonValue.ofInt64 (int64 revision.Header.Schema)
                "binaryFormat", JsonValue.ofUInt64 (uint64 Binary.FormatVersion)
                "contractFingerprint", JsonValue.String Binary.ContractFingerprint
                "inspectionOnly", JsonValue.Bool true
                "Revision", JsonGenerated.writeRevision revision
            ])

    let render pretty view : Result<string, Binary.Error> =
        read view |> Result.map (if pretty then Json.serializePretty else Json.serialize)
