module Fidelity.PSG.Tests.GateTests

open System
open System.Diagnostics
open System.IO
open System.Xml.Linq
open Xunit

// The contract's own source is held to rules that the build checks before every
// compile (build/Contract.targets). These tests give the check one source or one
// project reference at a time and require its verdict.

let private repository = Path.GetFullPath(Path.Combine(__SOURCE_DIRECTORY__, "..", ".."))
let private targets = Path.Combine(repository, "build", "Contract.targets")
let private permitted = Path.Combine(repository, "..", "BAREWire", "src", "BAREWire.fsproj") |> Path.GetFullPath

let private name (value: string) = XName.Get value
let private attribute (key: string) (value: string) = XAttribute(name key, value)

/// The exit code and the output of the check for one source and the references given.
let private verdict (source: string) (references: string list) : int * string =
    let directory = Path.Combine(Path.GetTempPath(), "fidelity-psg-gate-" + Guid.NewGuid().ToString "N")
    Directory.CreateDirectory directory |> ignore
    try
        let path = Path.Combine(directory, "Probe.fs")
        File.WriteAllText(path, source)
        let project = Path.Combine(directory, "Probe.proj")
        XDocument(
            XElement(name "Project",
                XElement(name "Import", attribute "Project" targets),
                XElement(name "Target", attribute "Name" "Probe",
                    XElement(name "ValidatePsgContract",
                        attribute "Sources" path,
                        attribute "ProjectReferences" (String.concat ";" references),
                        attribute "PermittedProject" permitted))))
            .Save project
        let start = ProcessStartInfo("dotnet", UseShellExecute = false, RedirectStandardOutput = true, RedirectStandardError = true)
        for argument in [ "msbuild"; project; "-nologo"; "-t:Probe" ] do start.ArgumentList.Add argument
        use child = new Process(StartInfo = start)
        Assert.True(child.Start(), "The check did not start")
        let output, errors = child.StandardOutput.ReadToEndAsync(), child.StandardError.ReadToEndAsync()
        Assert.True(child.WaitForExit 120000, "The check did not finish")
        child.ExitCode, output.GetAwaiter().GetResult() + errors.GetAwaiter().GetResult()
    finally
        Directory.Delete(directory, true)

let private accepted (source: string) (references: string list) =
    let code, output = verdict source references
    Assert.True((code = 0), sprintf "The check refused what it must accept:\n%s" output)

let private refused (rule: string) (source: string) (references: string list) =
    let code, output = verdict source references
    Assert.True((code <> 0), sprintf "The check accepted what rule %s refuses" rule)
    Assert.Contains(rule, output)

[<Fact>]
let ``a declaration of data is accepted`` () =
    accepted "namespace Fidelity.PSG\ntype Probe = { Bits: int; Name: string }\n" [ permitted ]

[<Fact>]
let ``a comment is not examined`` () =
    accepted "namespace Fidelity.PSG\n// Immutable values. A reader opens no System.IO file and holds no mutable state.\ntype Probe = { Bits: int }\n" []

[<Theory>]
[<InlineData("open Clef.Compiler.NativeTypedTree")>]
[<InlineData("let reader = FSharp.Compiler.Text.Range.Zero")>]
let ``a source that names a compiler is refused`` (line: string) =
    refused "PSG001" ("namespace Fidelity.PSG\n" + line + "\n") []

[<Theory>]
[<InlineData("let text = System.IO.File.ReadAllText path")>]
[<InlineData("let exists = Directory.Exists path")>]
[<InlineData("let start = ProcessStartInfo \"tool\"")>]
[<InlineData("let home = Environment.GetEnvironmentVariable \"HOME\"")>]
[<InlineData("let cache = ConditionalWeakTable<obj, obj>()")>]
[<InlineData("let mutable count = 0")>]
let ``a source with an effect or with state is refused`` (line: string) =
    refused "PSG003" ("module Fidelity.PSG.Probe\n" + line + "\n") []

[<Fact>]
let ``the word mutable inside a longer word is accepted`` () =
    accepted "module Fidelity.PSG.Probe\nlet immutableValue = 1\n" []

[<Fact>]
let ``a reference to a project other than BAREWire is refused`` () =
    let other = Path.Combine(repository, "..", "clef", "src", "Compiler", "Clef.Compiler.Service.fsproj") |> Path.GetFullPath
    refused "PSG002" "namespace Fidelity.PSG\ntype Probe = { Bits: int }\n" [ permitted; other ]
