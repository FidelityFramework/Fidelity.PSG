namespace Fidelity.PSG.Json

open System
open System.Globalization
open Fidelity.Data.JSON

/// Inspection retains tags for wide values and representation-sensitive bit patterns.
/// These are descriptions of stored fields, never a second wire decoder.
module internal JsonRuntime =
    let private invariant = CultureInfo.InvariantCulture
    let private exact kind text = JsonValue.Object ["$type", JsonValue.String kind; "value", JsonValue.String text]
    let writeBool value = JsonValue.Bool value
    let writeByte (value: byte) = JsonValue.ofUInt64 (uint64 value)
    let writeUInt16 (value: uint16) = JsonValue.ofUInt64 (uint64 value)
    let writeInt32 (value: int) = JsonValue.ofInt64 (int64 value)
    let writeInt64 (value: int64) = exact "int64" (value.ToString invariant)
    let writeUInt64 (value: uint64) = exact "uint64" (value.ToString invariant)
    let writeBigInteger (value: bigint) = exact "bigint" (value.ToString invariant)
    let writeString value = JsonValue.String value
    let writeChar (value: char) =
        JsonValue.Object ["$type", JsonValue.String "char-utf16"; "codeUnit", JsonValue.ofUInt64 (uint64 (uint16 value))]
    let writeDecimal (value: decimal) =
        JsonValue.Object ["$type", JsonValue.String "decimal"; "value", JsonValue.String(value.ToString invariant)
                          "bits", Decimal.GetBits value |> Array.map writeInt32 |> Array.toList |> JsonValue.Array]
    let writeDouble (value: float) =
        JsonValue.Object ["$type", JsonValue.String "float64"
                          "bits", JsonValue.String((BitConverter.DoubleToInt64Bits value).ToString("X16", invariant))
                          "value", JsonValue.String(value.ToString("R", invariant))]
    let union case fields =
        JsonValue.Object ["$case", JsonValue.String case; "$fields", JsonValue.Object fields]
    let writeArray render values = values |> Array.map render |> Array.toList |> JsonValue.Array
    let writeList render values = values |> List.map render |> JsonValue.Array
    let writeSet render values = values |> Set.toList |> List.map render |> JsonValue.Array
    let writeMap key value values =
        values |> Map.toList |> List.map (fun (k, v) -> JsonValue.Object ["Key", key k; "Value", value v]) |> JsonValue.Array
    let writeOption render = function
        | None -> union "None" []
        | Some value -> union "Some" [("Value", render value)]
    let writeResult good bad = function
        | Ok value -> union "Ok" [("ResultValue", good value)]
        | Error value -> union "Error" [("ErrorValue", bad value)]
