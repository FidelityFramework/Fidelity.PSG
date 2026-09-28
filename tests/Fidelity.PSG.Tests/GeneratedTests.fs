module Fidelity.PSG.Tests.GeneratedTests

open System.Diagnostics
open System.IO
open System.Reflection
open Microsoft.FSharp.Reflection
open Xunit
open Fidelity.PSG

let private repository = Path.GetFullPath(Path.Combine(__SOURCE_DIRECTORY__, "..", ".."))

/// The list of parts is generated from the compiled contract. A contract type that
/// changes without the generator being run again leaves a table unexamined, so the
/// file in the source tree must equal what the generator produces now.
[<Fact>]
let ``the generated list of parts is the one the contract produces`` () =
    let contract = typeof<Revision>.Assembly.Location
    let produced = Path.Combine(Path.GetTempPath(), sprintf "IntegrityNamed-%d.fs" (Process.GetCurrentProcess().Id))
    let start = ProcessStartInfo("dotnet", UseShellExecute = false, RedirectStandardOutput = true, RedirectStandardError = true)
    for argument in [ "fsi"; Path.Combine(repository, "tools", "GenerateIntegrity.fsx"); contract; produced ] do
        start.ArgumentList.Add argument
    use generator = new Process(StartInfo = start)
    Assert.True(generator.Start(), "The generator did not start")
    let output, errors = generator.StandardOutput.ReadToEndAsync(), generator.StandardError.ReadToEndAsync()
    Assert.True(generator.WaitForExit 300000, "The generator did not finish")
    Assert.True(generator.ExitCode = 0, sprintf "The generator failed:\n%s\n%s" (output.GetAwaiter().GetResult()) (errors.GetAwaiter().GetResult()))
    let held = File.ReadAllText(Path.Combine(repository, "src", "Fidelity.PSG", "IntegrityNamed.fs"))
    let current = File.ReadAllText produced
    File.Delete produced
    Assert.True((held = current), "src/Fidelity.PSG/IntegrityNamed.fs differs from the generator's output. Run tools/GenerateIntegrity.fsx.")

[<Fact>]
let ``every part the generator lists is examined`` () =
    Assert.Equal(IntegrityNamed.Parts, (Integrity.named (Revision.empty "contract-test")).Length)

/// The contract types with a field `Participants` that is a set of node identities, with
/// no role, ordinal or group for an occurrence. A row that states its participants as
/// `Participant` values leaves this list; no type joins it.
let private untypedParticipantSets =
    [ "ArrayAllocationConstruction"; "ArrayCopyConstruction"; "BoundaryCall"; "BoundaryImport"
      "CallableEmissionCall"; "CallableEmissionDeclaration"; "CallableProgramInstance"; "HardwareModuleWitness"
      "IntrinsicWriteCall"; "IntrinsicWriteImport"; "IntrinsicWriteProof"; "KernelIngress"
      "KernelModuleWitness"; "KernelTargetPlan"; "MemoryAddressWitness"; "MemoryArrayAccessWitness"
      "MemoryArrayAllocationWitness"; "MemoryArrayCopyWitness"; "MemoryArrayExtentWitness"; "MemoryArrayLiteralWitness"
      "MemoryBoundsWitness"; "MemoryExtentWitness"; "MemoryProof"; "MemoryStringViewWitness"
      "NumericIndexTransport"; "NumericOperationProof"; "NumericOperationWitness"; "ProgramStorageEntry"
      "ScalarCarrier"; "SequenceFamily"; "SequenceProgramWitness"; "SpatialProof" ]

[<Fact>]
let ``no contract type adds a participant set without roles`` () =
    let flags = BindingFlags.Public ||| BindingFlags.NonPublic
    let untyped (field: PropertyInfo) = field.Name = "Participants" && field.PropertyType = typeof<Set<NodeId>>
    let types = typeof<Revision>.Assembly.GetTypes()
    let records =
        types
        |> Array.filter (fun ty -> FSharpType.IsRecord(ty, flags) && FSharpType.GetRecordFields(ty, flags) |> Array.exists untyped)
        |> Array.map _.Name
    let cases =
        types
        |> Array.filter (fun ty -> FSharpType.IsUnion(ty, flags))
        |> Array.collect (fun ty ->
            FSharpType.GetUnionCases(ty, flags)
            |> Array.filter (fun case -> case.GetFields() |> Array.exists untyped)
            |> Array.map (fun case -> ty.Name + "." + case.Name))
    Assert.Equal<string list>(untypedParticipantSets, Array.append records cases |> Array.sort |> Array.toList)
