module Fidelity.PSG.Tests.AsyncAndRegionIntegrityTests

open Xunit
open Fidelity.PSG
open Fidelity.PSG.Tests.Build

// Deliberately isolate the allocation-construction account. Numeric and callable
// proofs have their own integrity tests; the native gate checks a whole revision.
let private deliveryFixture () =
    let scalar site value : ScalarCarrier =
        {Site=NodeId site;Slot=SettledSlot.Integer(8,None);Range=ValueRange.Bounded(value,value)
         Representation=None;Declaration=None;SourceType=unitType;Obligations=[];Participants=Set.empty}
    let requirement site frontier continuation : RequirementWitness =
        {Site=NodeId site;Condition=NodeId 70;Diagnostic="bounds";Frontier=NodeId frontier
         Continuation=NodeId continuation;PatternTest=None;Participants=[]}
    let guard=requirement 69 68 20
    let allocation : MemoryArrayAllocationWitness =
        {Site=NodeId 20;Count=NodeId 42;CountCarrier=scalar 42 2I;IndexUnsigned=true
         Element=SettledSlot.Integer(8,None);ElementBytes=1;Alignment=1;Residence=MemoryResidence.Stack(NodeId 3,NodeId 4)
         MinimumCount=2I;MaximumCount=2I;Requirement=guard;Participants=Set.empty
         Construction={Site=NodeId 20;Owner=NodeId 1;Count={Actual=NodeId 42;Binding=NodeId 43;Reference=NodeId 42}
                       Default=None;Initialization=None;Participants=Set.empty
                       Guard={Requirement=guard.Site;Predicate=guard.Condition;Frontier=guard.Frontier;Continuation=guard.Continuation
                              Count=NodeId 42;Offset=None;Buffer=None;Length=None;Zero=NodeId 40;NonnegativeCount=guard.Condition
                              NonnegativeOffset=None;End=None;Within=None}}}
    let write ordinal : MemoryArrayAccessWitness =
        {Site=NodeId(30+ordinal);Buffer=NodeId 22;Index=NodeId(40+ordinal);Value=Some(NodeId(10+ordinal))
         Element=allocation.Element;Adaptation=None;Participants=Set.empty
         Bounds={Buffer=NodeId 22;Index=NodeId(40+ordinal);IndexCarrier=scalar (40+ordinal) (bigint ordinal)
                 ExtentCarrier=scalar 42 2I;IndexUnsigned=true;Length=NodeId 42;Lower=NodeId 70;Upper=NodeId 70
                 Requirement=requirement (60+ordinal) (50+ordinal) (30+ordinal);Participants=Set.empty}}
    let writes=[write 0;write 1]
    let nodes=[1..70] |> List.map (fun site -> node site (SemanticKind.Literal NativeLiteral.Unit) [])
    let initial=revision nodes
    let nodes=initial.Nodes
                  .Add(NodeId 20,node 20 (SemanticKind.ArrayAllocate(NodeId 42)) [42])
                  .Add(NodeId 21,node 21 (SemanticKind.Binding("results",false,false,None)) [24])
                  .Add(NodeId 22,node 22 (SemanticKind.VarRef("results",Some(NodeId 21))) [])
                  .Add(NodeId 23,node 23 (SemanticKind.Sequential [NodeId 21;NodeId 50;NodeId 51;NodeId 22]) [21;50;51;22])
                  .Add(NodeId 24,node 24 (SemanticKind.Sequential [NodeId 69;NodeId 20]) [69;20])
    let initial=covered {initial with Nodes=nodes}
    let orchestration : AsyncOrchestration =
        {Site=NodeId 1;Mode=AsyncOrchestrationMode.Parallel;Children=[NodeId 10;NodeId 11];WorkDependencies=[]
         ResultOrdering=[0,NodeId 10;1,NodeId 11];JoinCondition=NodeId 2;ResultStorage=NodeId 20;ResultCapacity=2
         ElementStride=1;LifetimeScope=NodeId 3;SynchronizationObligations=[];Participants=[]}
    let activations=[10;11] |> List.map(fun site ->
        NodeId site,({Site=NodeId site;Formation=NodeId 4;ResultTarget=NodeId 5;CompletionTarget=NodeId 6;Obligations=[];Participants=[]}:AsyncActivation)) |> Map.ofList
    let memory={initial.Emission.Memory with Operations=Map.ofList ((NodeId 20,MemoryWitnessOperation.ArrayAllocation allocation)::(writes |> List.map(fun row -> row.Site,MemoryWitnessOperation.ArrayAccess row)))}
    {initial with
        Codata={initial.Codata with AsyncOrchestrations=Map.ofList [NodeId 1,orchestration];AsyncActivations=activations}
        Emission={initial.Emission with
                    Memory=memory
                    Storage={initial.Emission.Storage with Requirements=Map.ofList ((guard.Site,guard)::(writes |> List.map(fun row -> row.Bounds.Requirement.Site,row.Bounds.Requirement)))}}}

let private constructionDefects revision =
    Integrity.check revision |> List.filter(fun violation -> violation.Part="Emission.Memory.Operations.ArrayAllocation.Construction")

[<Fact>]
let ``complete async child delivery accounts for the uninitialized allocation`` () =
    Assert.Empty(constructionDefects(deliveryFixture()))

[<Theory>]
[<InlineData("missing child")>]
[<InlineData("duplicate delivery")>]
[<InlineData("wrong ordinal")>]
[<InlineData("wrong buffer")>]
[<InlineData("missing requirement")>]
[<InlineData("early escape")>]
[<InlineData("wrong capacity")>]
[<InlineData("wrong stride")>]
[<InlineData("wrong count")>]
[<InlineData("missing orchestration")>]
[<InlineData("cyclic storage")>]
let ``incomplete async delivery cannot authorize uninitialized storage`` mutation =
    let source=deliveryFixture()
    let memory=source.Emission.Memory
    let operations change={source with Emission={source.Emission with Memory={memory with Operations=change memory.Operations}}}
    let write change=operations(fun rows -> rows |> Map.map(fun site operation ->
        match operation with MemoryWitnessOperation.ArrayAccess row when site=NodeId 30 -> MemoryWitnessOperation.ArrayAccess(change row) | _ -> operation))
    let orchestration change={source with Codata={source.Codata with AsyncOrchestrations=source.Codata.AsyncOrchestrations |> Map.map(fun _ row -> change row)}}
    let changed =
        match mutation with
        | "missing child" -> operations(fun rows -> rows.Remove(NodeId 31))
        | "duplicate delivery" -> write(fun row -> {row with Value=Some(NodeId 11)})
        | "wrong ordinal" -> write(fun row -> {row with Bounds={row.Bounds with IndexCarrier={row.Bounds.IndexCarrier with Range=ValueRange.Bounded(1I,1I)}}})
        | "wrong buffer" -> write(fun row -> {row with Buffer=NodeId 70;Bounds={row.Bounds with Buffer=NodeId 70}})
        | "missing requirement" -> {source with Emission={source.Emission with Storage={source.Emission.Storage with Requirements=source.Emission.Storage.Requirements.Remove(NodeId 60)}}}
        | "early escape" -> {source with Nodes=source.Nodes.Add(NodeId 23,node 23 (SemanticKind.Sequential [NodeId 21;NodeId 50;NodeId 22]) [21;50;22])}
        | "wrong capacity" -> orchestration(fun row -> {row with ResultCapacity=3})
        | "wrong stride" -> orchestration(fun row -> {row with ElementStride=8})
        | "wrong count" -> operations(fun rows -> rows |> Map.map(fun _ operation ->
            match operation with MemoryWitnessOperation.ArrayAllocation row -> MemoryWitnessOperation.ArrayAllocation {row with MaximumCount=3I} | _ -> operation))
        | "missing orchestration" -> {source with Codata={source.Codata with AsyncOrchestrations=Map.empty}}
        | "cyclic storage" -> {source with Nodes=source.Nodes.Add(NodeId 21,node 21 (SemanticKind.Binding("results",false,false,None)) [21])}
        | other -> failwithf "Unknown mutation %s" other
    Assert.NotEmpty(constructionDefects changed)
