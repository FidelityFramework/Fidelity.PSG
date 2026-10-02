#load "JsonGeneration.fs"
match fsi.CommandLineArgs |> Array.skip 1 with
| [| assembly; output |] -> System.IO.File.WriteAllText(output, PsgJsonGeneration.generate assembly)
| _ -> failwith "Usage: GenerateJson.fsx <Fidelity.PSG.dll> <output.fs>"
