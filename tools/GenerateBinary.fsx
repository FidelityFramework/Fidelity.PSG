// Complete typed snapshot-codec generation from the compiled contract.
// Usage: dotnet fsi tools/GenerateBinary.fsx <Fidelity.PSG.dll> <output.fs>
#load "BinaryGeneration.fs"
match fsi.CommandLineArgs |> Array.skip 1 with
| [| assembly; output |] -> System.IO.File.WriteAllText(output, PsgBinaryGeneration.generate assembly)
| _ -> failwith "Usage: GenerateBinary.fsx <Fidelity.PSG.dll> <output.fs>"
