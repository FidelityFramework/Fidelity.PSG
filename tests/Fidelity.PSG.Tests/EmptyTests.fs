module Fidelity.PSG.Tests.EmptyTests

open Xunit
open Fidelity.PSG

[<Fact>]
let ``the empty revision names this contract and holds nothing`` () =
    let revision = Revision.empty "producer-under-test"
    Assert.Equal(Revision.Schema, revision.Header.Schema)
    Assert.Equal("producer-under-test", revision.Header.Producer)
    Assert.True(revision.Nodes.IsEmpty)
    Assert.Empty revision.Edges
    Assert.Empty revision.DeclarationRoots
    Assert.Empty revision.Obligations
    Assert.Equal(Empty.emission, revision.Emission)
    Assert.Equal(Codata.empty, revision.Codata)

[<Fact>]
let ``the empty revision declares no width and says so`` () =
    let revision = Revision.empty "producer-under-test"
    match revision.Platform.Register, revision.Platform.Pointer with
    | Error register, Error pointer ->
        Assert.Contains("Register", register)
        Assert.Contains("Pointer", pointer)
    | other -> failwithf "An empty revision supplied a width: %A" other

[<Fact>]
let ``the empty revision is well formed`` () =
    Assert.Empty(Integrity.check (Revision.empty "producer-under-test"))

[<Fact>]
let ``no named part of the empty revision names a node`` () =
    for part, identities in Integrity.named (Revision.empty "producer-under-test") do
        Assert.True(List.isEmpty identities, sprintf "%s names %A in an empty revision" part identities)
