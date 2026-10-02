module Fidelity.PSG.Inspect.Program

open System
open System.IO
open Fidelity.PSG
open Fidelity.PSG.Hosting
open Fidelity.PSG.Json

// This explicit process is the inspection sink. Compiler publication neither
// starts it nor waits for its JSON rendering. Exit success follows output close.
[<EntryPoint>]
let main arguments =
    try
        let input, output, pretty =
            match arguments with
            | [|"--input"; input; "--output"; output|] -> input, output, false
            | [|"--input"; input; "--output"; output; "--pretty"|] -> input, output, true
            | _ -> invalidArg "arguments" "Usage: PsgInspect --input <complete-image> --output <json-file|-> [--pretty]"
        if output <> "-" && Path.GetFullPath input = Path.GetFullPath output then
            invalidArg "output" "Inspection must not overwrite its input image"
        let limits : Binary.Limits = {
            MaxBytes = 127 * 1024 * 1024; MaxCollectionLength = 1000000; MaxDepth = 128
            MaxStringBytes = 8 * 1024 * 1024; MaxBigIntegerBytes = 1024 * 1024; MaxValues = 10000000
        }
        let take label = function Ok value -> value | Error error -> failwithf "%s: %A" label error
        use mapped = MappedRevision.Open(limits, input) |> take "Image open refused"
        let text = Inspection.render pretty mapped.View |> take "Complete revision inspection refused"
        if output = "-" then Console.Out.WriteLine text
        else
            // Refuse overwrite, including aliases of the input or another image.
            use destination = new FileStream(output, FileMode.CreateNew, FileAccess.Write, FileShare.None)
            use writer = new StreamWriter(destination, Text.UTF8Encoding(false, true))
            writer.Write text
        0
    with error ->
        eprintfn "PSG inspection failed: %s" error.Message
        1
