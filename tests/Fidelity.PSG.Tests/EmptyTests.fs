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

[<Fact>]
let ``MeasureVar comparison uses Id and handles mismatched or null comparisons without throwing`` () =
    let a1 : MeasureVar = { Id = 1; Name = Some "u" }
    let a2 : MeasureVar = { Id = 1; Name = Some "v" }
    let b : MeasureVar = { Id = 2; Name = None }
    let nilVar = Unchecked.defaultof<MeasureVar>
    let eq : System.IEquatable<MeasureVar> = upcast a1
    let cmpTyped : System.IComparable<MeasureVar> = upcast a1
    let cmpTypedB : System.IComparable<MeasureVar> = upcast b
    let cmpObj : System.IComparable = upcast a1
    let cmpObjB : System.IComparable = upcast b
    Assert.True(eq.Equals a2)
    Assert.False(eq.Equals b)
    Assert.False(eq.Equals nilVar)
    Assert.Equal(a1.GetHashCode(), a2.GetHashCode())
    Assert.Equal(0, cmpTyped.CompareTo a2)
    Assert.True(cmpTyped.CompareTo b < 0)
    Assert.True(cmpTypedB.CompareTo a1 > 0)
    Assert.Equal(1, cmpTyped.CompareTo nilVar)
    Assert.Equal(0, cmpObj.CompareTo a2)
    Assert.True(cmpObjB.CompareTo a1 > 0)
    Assert.Equal(1, cmpObj.CompareTo null)
    Assert.Equal(-1, cmpObj.CompareTo "other")
    let map = Map.ofList [ a1, 10; b, 20 ]
    Assert.Equal(10, map[a2])
    Assert.Equal(20, map[b])
    let set = Set.ofList [ a1; a2; b ]
    Assert.Equal(2, set.Count)
    Assert.True(Set.contains a2 set)
    Assert.True(Set.contains b set)
