module Fidelity.PSG.Tests.IntegrityTests

open Xunit
open Fidelity.PSG
open Fidelity.PSG.Tests.Build

// A closed call returns the same callable component constructed in its body.
let private ordinaryResultReturnedWrite () =
    let p role ordinal group number : Participant =
        { Role = role; Ordinal = ordinal; Group = NodeId group; Node = NodeId number }
    let fnType = TypeIdentity.Function(unitType, unitType)
    let resultConstructor : ConstructorIdentity =
        { Declaration = { Module = []; Name = "Result" }
          Parameters = [TypeParamKind.Type; TypeParamKind.Type]; NativeKind = None }
    let resultType = TypeIdentity.Application(resultConstructor, [fnType; boolType])
    let typed number kind children ty = { node number kind children with Type = ty }
    let nodes =
        [ typed 1 (SemanticKind.Application(NodeId 3, [NodeId 4])) [3; 4] resultType
          typed 2 (SemanticKind.UnionCase("Ok", 0, Some(NodeId 30))) [30] resultType
          node 3 (SemanticKind.VarRef("make", Some(NodeId 7))) []
          node 4 (SemanticKind.Literal NativeLiteral.Unit) []
          typed 5 (SemanticKind.Lambda(["unit", unitType, NodeId 6], NodeId 2, [], Some "make", LambdaContext.RegularClosure)) [6; 2] (TypeIdentity.Function(unitType, resultType))
          node 6 (SemanticKind.PatternBinding "unit") []
          node 7 (SemanticKind.Binding("make", false, false, None)) [5]
          typed 10 (SemanticKind.Lambda([], NodeId 11, [], Some "callback", LambdaContext.RegularClosure)) [11] fnType
          { node 11 (SemanticKind.Literal NativeLiteral.Unit) [] with Parent = Some(NodeId 10) }
          typed 30 (SemanticKind.Literal NativeLiteral.Unit) [] fnType ]
    let initial = revision nodes
    let contract : CallableContract =
        { Identity = NodeId 100; Kind = CallableKind.OrdinaryFlatClosure; Convention = CallableConvention.Ordinary
          ParameterTypes = []; OmittedParameters = []; ParameterRepresentations = []; ResultType = unitType
          ResultRepresentation = ValueRepresentation.Scalar SettledSlot.Bool; EnvironmentBytes = None
          SourcePremises = Map.empty; Participants = [p ParticipantRole.CallableContract 0 100 100] }
    let carrier : CallableCarrier =
        { Occurrence = NodeId 30; Kind = CallableKind.OrdinaryFlatClosure; Formation = NodeId 30
          EnvironmentValue = None; Contract = Ok(NodeId 100); Lifetime = []; SourceType = fnType
          Implementation = NodeId 10; Parameters = []; ParameterShapes = []; OmittedParameters = Set.empty
          Result = NodeId 11; ResultShape = CallableValueShape.Data(NodeId 11); Environment = None }
    let slot : CallableAggregateSlot =
        { Identity = NodeId 101; AggregateType = resultType; Declaration = None; DeclarationFacts = []
          Path = [CallableAggregatePathStep.UnionPayload(0, 0)]; SourceType = fnType; Contract = Ok(NodeId 100)
          Participants = [p ParticipantRole.AggregateSlot 0 101 101; p ParticipantRole.CallableContract 0 101 100] }
    let tag : CallableAggregateTag =
        { Constructor = NodeId 2; TagRead = None; CaseOrdinal = 0; PayloadOrdinal = Some 0; Payload = Some(NodeId 30)
          Participants = [p ParticipantRole.AggregateConstructor 0 2 2; p ParticipantRole.AggregatePayload 0 2 30] }
    let alternative : CallableAggregateAlternative =
        { Ordinal = 0; Carrier = NodeId 30; Formation = NodeId 30; EnvironmentValue = None
          Contract = NodeId 100; Adapter = None; EnvironmentPlacement = None }
    let parts group inputs =
        [p ParticipantRole.AggregateValue 0 group group; p ParticipantRole.AggregateSource 0 group group
         p ParticipantRole.AggregateSlot 0 group 101; p ParticipantRole.AggregateWrite 0 group 30
         p ParticipantRole.CallableCarrier 0 group 30; p ParticipantRole.CallableFormation 0 group 30
         p ParticipantRole.CallableContract 0 group 100] @
        (inputs |> List.mapi (fun ordinal id -> p ParticipantRole.AggregateInput ordinal group (NodeId.value id)))
    let sourceInputs = [NodeId 30]
    let source : CallableAggregateValue =
        { Occurrence = NodeId 2; Aggregate = NodeId 2; Slot = NodeId 101; Alternatives = [alternative]
          Selector = Some {Lower = 0; UpperExclusive = 1; Storage = None; Slot = None; ByteOffset = None}
          FormationInputs = sourceInputs; Value = Some(NodeId 30); SelectedAlternative = Some 0
          Operation = CallableAggregateOperation.Construct; Frontier = None; Tag = Some tag; Selection = None
          ResultRetirement = None; Bytes = 0; Alignment = 1; Participants = parts 2 sourceInputs }
    let inputs = [NodeId 3; NodeId 4; NodeId 5; NodeId 6; NodeId 2; NodeId 2; NodeId 30]
    let returned =
        { source with Occurrence = NodeId 1; Aggregate = NodeId 1; Operation = CallableAggregateOperation.Result
                      FormationInputs = inputs; ResultRetirement = Some(Error "not a boundary callback")
                      Participants =
                        parts 1 inputs @
                            [p ParticipantRole.Site 0 1 1; p ParticipantRole.Path 0 1 3; p ParticipantRole.Path 1 1 7
                             p ParticipantRole.CalleeArgument 0 1 4; p ParticipantRole.Callee 0 1 5
                             p ParticipantRole.CallableImplementation 0 1 5; p ParticipantRole.CalleeParameter 0 1 6
                             p ParticipantRole.CalleeBody 0 5 2; p ParticipantRole.AggregateConstructor 0 1 2
                             p ParticipantRole.AggregatePayload 0 1 30] }
    let name = CallableSymbolName.RootBinding "callback"
    let declaration : CallableEmissionDeclaration =
        { Lookup = NodeId 10; Implementation = NodeId 10; Parameters = []; Result = NodeId 11
          Context = LambdaContext.RegularClosure; Captures = []; Name = name; Parent = None
          Participants = Set.ofList [NodeId 10; NodeId 11] }
    let representation =
        ValueRepresentation.Union(["Ok", [ValueRepresentation.CallableComponent(NodeId 101, ValueRepresentation.Record([], Some([], 0, 1)))]; "Error", []], Some(1, 1, 1))
    let callable =
        { initial.Emission.Callable with
            Contracts = Map.ofList [NodeId 100, contract]
            Carriers = Map.ofList [NodeId 30, carrier]
            AggregateSlots = Map.ofList [NodeId 101, slot]
            AggregateValues = Map.ofList [NodeId 1, [returned]; NodeId 2, [source]]
            Declarations = Map.ofList [NodeId 10, declaration]
            Symbols = Map.ofList [NodeId 5, CallableSymbolName.Anonymous(NodeId 5); NodeId 10, name]
            SignatureData = Map.ofList [NodeId 10, Set.singleton(NodeId 11)]
            ClosedData = Set.singleton(NodeId 11) }
    let account site values =
        let participants = slot.Participants @ (values |> List.collect (fun (row: CallableAggregateValue) -> row.Participants @ tag.Participants)) @ contract.Participants
        let sources =
            participants |> List.map _.Node |> List.distinct |> List.choose (fun id ->
                initial.Nodes.TryFind id |> Option.map (fun n -> {Node = id; Kind = n.Kind; Type = n.Type; Children = n.Children; Anchors = n.ObligationAnchors}))
        { Occurrence = site; Slots = [slot]; Values = values; Carriers = [carrier]; Contracts = [contract]
          Flows = []; Joins = []; Participants = participants; Sources = sources; Claims = []
          Symbols = [NodeId 10, name] @ (if site = NodeId 1 then [NodeId 5, CallableSymbolName.Anonymous(NodeId 5)] else [])
          Inactivity = []; MemoryPolicy = None } : CallableAggregateDependencyAccount
    let callable = { callable with AggregateDependencies = Map.ofList [NodeId 1, account (NodeId 1) [returned; source]; NodeId 2, account (NodeId 2) [source]] }
    let numeric =
        { initial.Emission.Numeric with OccurrenceRepresentations = initial.Emission.Numeric.OccurrenceRepresentations.Add(NodeId 1, Ok representation).Add(NodeId 2, Ok representation) }
    { initial with
        Codata = { initial.Codata with CallableContracts = callable.Contracts; CallableCarriers = callable.Carriers
                                       CallableAggregateSlots = callable.AggregateSlots; CallableAggregateValues = callable.AggregateValues
                                       CallableAggregateDependencies = callable.AggregateDependencies }
        Emission = { initial.Emission with Callable = callable; Numeric = numeric } }

[<Fact>]
let ``ordinary Result Ok returned write retains the exact construction`` () =
    Assert.Empty(Integrity.check (ordinaryResultReturnedWrite ()))

[<Theory>]
[<InlineData("Error")>]
[<InlineData("tag")>]
let ``ordinary Result returned write rejects an Error construction or changed tag`` defect =
    let held = ordinaryResultReturnedWrite ()
    let changed =
        if defect = "Error" then
            let construction = {held.Nodes[NodeId 2] with Kind = SemanticKind.UnionCase("Error", 1, Some(NodeId 30))}
            let c = held.Emission.Callable
            let values =
                c.AggregateValues |> Map.map (fun _ rows ->
                    rows |> List.map (fun row -> {row with Tag = row.Tag |> Option.map (fun tag -> {tag with CaseOrdinal = 1})}))
            let accounts =
                c.AggregateDependencies |> Map.map (fun _ account ->
                    {account with Values = account.Values |> List.map (fun row -> values[row.Occurrence] |> List.exactlyOne)
                                  Sources = account.Sources |> List.map (fun source ->
                                      if source.Node = NodeId 2 then {source with Kind = construction.Kind} else source)})
            { held with Nodes = held.Nodes.Add(NodeId 2, construction)
                        Codata = {held.Codata with CallableAggregateValues = values; CallableAggregateDependencies = accounts}
                        Emission = {held.Emission with Callable = {c with AggregateValues = values; AggregateDependencies = accounts}} }
        else
            let c = held.Emission.Callable
            let row = c.AggregateValues[NodeId 1] |> List.exactlyOne
            let changed = {row with Tag = row.Tag |> Option.map (fun tag -> {tag with CaseOrdinal = 1})}
            let values = c.AggregateValues.Add(NodeId 1, [changed])
            {held with Codata = {held.Codata with CallableAggregateValues = values}
                       Emission = {held.Emission with Callable = {c with AggregateValues = values}}}
    Assert.Contains(Integrity.check changed, fun violation ->
        violation.Part = "Emission.Callable.Aggregates.I5" && violation.Node = Some(NodeId 1) &&
        violation.Reason = "The aggregate result differs from its exact closed application, return or original constructor.")

/// The one violation of the revision, which the part given reports.
let private only part (violations: IntegrityViolation list) =
    let violation = Assert.Single violations
    Assert.Equal(part, violation.Part)
    violation

/// The one violation that the part given reports. Other parts may report the same defect.
let private within part (violations: IntegrityViolation list) =
    violations |> List.filter (fun violation -> violation.Part = part) |> Assert.Single

[<Fact>]
let ``a revision whose every identity is held is well formed`` () =
    Assert.Empty(Integrity.check bindingWithLiteral)

[<Fact>]
let ``a revision of another contract version is refused by its header`` () =
    let foreign = { bindingWithLiteral with Header = { bindingWithLiteral.Header with Schema = Revision.Schema + 1 } }
    let violation = only "Header" (Integrity.check foreign)
    Assert.Equal(None, violation.Node)
    Assert.Contains(string (Revision.Schema + 1), violation.Reason)
    Assert.Contains(string Revision.Schema, violation.Reason)

[<Fact>]
let ``a node filed under another identity is reported at the key`` () =
    let misfiled = { bindingWithLiteral with Nodes = bindingWithLiteral.Nodes.Add(NodeId 2, bindingWithLiteral.Nodes[NodeId 1]) }
    let violations = Integrity.check misfiled
    Assert.Contains(violations, fun violation -> violation.Part = "Nodes" && violation.Node = Some (NodeId 2))

[<Fact>]
let ``a child that is not held is reported once`` () =
    let orphaned = { bindingWithLiteral with Nodes = bindingWithLiteral.Nodes.Remove(NodeId 2) }
    let violations = Integrity.check orphaned
    let violation = within "Nodes.Children" violations
    Assert.Equal(Some (NodeId 2), violation.Node)
    // Every table that still holds a row for the node reports it as well.
    Assert.All(violations, fun other -> Assert.Equal(Some (NodeId 2), other.Node))
    Assert.Contains(violations, fun other -> other.Part = "Emission.Callable.ValueShapes")

[<Fact>]
let ``an original historical parent does not replace actual context authority`` () =
    let literal = {bindingWithLiteral.Nodes[NodeId 2] with Parent = Some(NodeId 9000)}
    let stated = {bindingWithLiteral with Nodes = bindingWithLiteral.Nodes.Add(NodeId 2, literal)}
    Assert.Empty(Integrity.check stated)
    let orphaned = {stated with SourceReadings = {stated.SourceReadings with Contexts = stated.SourceReadings.Contexts.Remove(NodeId 1)}}
    Assert.Contains(Integrity.check orphaned, fun violation -> violation.Part = "SourceReadings.Contexts" && violation.Node = Some(NodeId 2))

[<Theory>]
[<InlineData(true)>]
[<InlineData(false)>]
let ``an edge with an end that is not held is reported by that end`` target =
    let edge : Hyperedge =
        { Sources = [ (if target then NodeId 2 else NodeId 9) ]
          Target = (if target then NodeId 9 else NodeId 1)
          Class = EdgeClass.Structural; Role = EdgeRole.Attached; Ordinal = 0 }
    let violation = only (if target then "Edges.Target" else "Edges.Sources") (Integrity.check { bindingWithLiteral with Edges = [ edge ] })
    Assert.Equal(Some (NodeId 9), violation.Node)

[<Fact>]
let ``an edge whose ends are held adds no violation`` () =
    let edge : Hyperedge =
        { Sources = [ NodeId 2 ]; Target = NodeId 1; Class = EdgeClass.Structural; Role = EdgeRole.Attached; Ordinal = 0 }
    Assert.Empty(Integrity.check { bindingWithLiteral with Edges = [ edge ] })

[<Fact>]
let ``a declaration root that is not held is reported`` () =
    let rooted = { bindingWithLiteral with DeclarationRoots = [ NodeId 7, DeclRoot.EntryPoint ] }
    let violation = only "DeclarationRoots" (Integrity.check rooted)
    Assert.Equal(Some (NodeId 7), violation.Node)

[<Fact>]
let ``library export requires its held source identity without a spatial plan`` () =
    let binding = {bindingWithLiteral.Nodes[NodeId 1] with Kind = SemanticKind.Binding("value", false, false, Some DeclRoot.LibraryExport)}
    let held =
        {bindingWithLiteral with
            Nodes = bindingWithLiteral.Nodes.Add(NodeId 1, binding)
            DeclarationRoots = [NodeId 1, DeclRoot.LibraryExport]}
    Assert.Empty(Integrity.check held)
    let orphaned = {held with DeclarationRoots = [NodeId 7, DeclRoot.LibraryExport]}
    let violation = only "DeclarationRoots" (Integrity.check orphaned)
    Assert.Equal(Some(NodeId 7), violation.Node)
    Assert.Equal("Node 7 is named and is not held by the revision.", violation.Reason)

[<Fact>]
let ``a published fact about a node that is not held is reported by its table`` () =
    let escapes = Map.ofList [ NodeId 5, EscapeKind.StackScoped ]
    let stated = { bindingWithLiteral with Codata = { bindingWithLiteral.Codata with Escapes = escapes } }
    let violation = only "Codata.Escapes" (Integrity.check stated)
    Assert.Equal(Some (NodeId 5), violation.Node)

[<Fact>]
let ``both ends of an identity relation are examined`` () =
    let origins = Map.ofList [ NodeId 1, NodeId 6 ]
    let stated = { bindingWithLiteral with Codata = { bindingWithLiteral.Codata with SequenceOrigins = origins } }
    let violation = only "Codata.SequenceOrigins (values)" (Integrity.check stated)
    Assert.Equal(Some (NodeId 6), violation.Node)
    let reversed = { bindingWithLiteral with Codata = { bindingWithLiteral.Codata with SequenceOrigins = Map.ofList [ NodeId 6, NodeId 1 ] } }
    let key = only "Codata.SequenceOrigins" (Integrity.check reversed)
    Assert.Equal(Some (NodeId 6), key.Node)

[<Fact>]
let ``a grouped source account without a current claim is reported`` () =
    let sources = Map.ofList [ NodeId 1, [ [ NodeId 2; NodeId 8 ] ] ]
    let violation = only "ObligationSources" (Integrity.check { bindingWithLiteral with ObligationSources = sources })
    Assert.Equal(Some (NodeId 1), violation.Node)
    Assert.Contains("CurrentClaims", violation.Reason)

[<Fact>]
let ``an identity named many times by one part is reported once`` () =
    let edges : Hyperedge list =
        [ 0; 1; 2 ] |> List.map (fun ordinal ->
            { Sources = [ NodeId 9 ]; Target = NodeId 1; Class = EdgeClass.Reference; Role = EdgeRole.Definition; Ordinal = ordinal })
    let violation = only "Edges.Sources" (Integrity.check { bindingWithLiteral with Edges = edges })
    Assert.Equal(Some (NodeId 9), violation.Node)

// A lazy value, its occurrence and its layout contract, each held by the revision.
let private lazyStorage : Revision =
    let layout : LazyLayout =
        { Owner = NodeId 1; Thunk = NodeId 2; Formal = NodeId 2; Computed = NodeId 2; Cached = NodeId 2
          Slots = []; Bytes = 8; Alignment = 8; Obligations = [] }
    let contract : LazyWitnessContract = { Layout = layout; ElementType = boolType; ThunkBody = NodeId 2 }
    let storage =
        { bindingWithLiteral.Emission.Storage with
            Lazies = Map.ofList [ NodeId 1, contract ]
            LazyOccurrences = Map.ofList [ NodeId 1, NodeId 1 ]
            LazyValues = Set.ofList [ NodeId 1 ]
            DefinitionOnlyThunks = Set.ofList [ NodeId 2 ] }
    let callable = { bindingWithLiteral.Emission.Callable with Symbols = Map.ofList [NodeId 2, CallableSymbolName.Anonymous (NodeId 2)] }
    { bindingWithLiteral with Emission = { bindingWithLiteral.Emission with Storage = storage; Callable = callable } }

let private withStorage (change: StorageWitnessProjection -> StorageWitnessProjection) : Revision =
    { lazyStorage with Emission = { lazyStorage.Emission with Storage = change lazyStorage.Emission.Storage } }

[<Fact>]
let ``a lazy value with its occurrence and its layout is well formed`` () =
    Assert.Empty(Integrity.check lazyStorage)

[<Fact>]
let ``a lazy occurrence whose owner has no layout is reported`` () =
    let withdrawn = withStorage (fun storage -> { storage with Lazies = Map.empty; DefinitionOnlyThunks = Set.empty })
    let violation = only "Emission.Storage.LazyOccurrences (values)" (Integrity.check withdrawn)
    Assert.Equal(Some (NodeId 1), violation.Node)
    Assert.Contains("Emission.Storage.Lazies", violation.Reason)

[<Fact>]
let ``a lazy value with no occurrence is reported`` () =
    let withdrawn = withStorage (fun storage -> { storage with LazyOccurrences = Map.empty })
    let violation = only "Emission.Storage.LazyValues" (Integrity.check withdrawn)
    Assert.Equal(Some (NodeId 1), violation.Node)
    Assert.Contains("Emission.Storage.LazyOccurrences", violation.Reason)

[<Fact>]
let ``a definition only thunk that no layout names is reported`` () =
    let withdrawn = withStorage (fun storage -> { storage with DefinitionOnlyThunks = Set.ofList [ NodeId 1 ] })
    let violation = only "Emission.Storage.DefinitionOnlyThunks" (Integrity.check withdrawn)
    Assert.Equal(Some (NodeId 1), violation.Node)

[<Fact>]
let ``a lazy thunk declaration that no layout names is reported`` () =
    let declaration : CallableEmissionDeclaration =
        { Lookup = NodeId 2; Implementation = NodeId 2; Parameters = []; Result = NodeId 2
          Context = LambdaContext.LazyThunk; Captures = []; Name = CallableSymbolName.Anonymous (NodeId 2)
          Parent = None; Participants = Set.ofList [ NodeId 2 ] }
    let declared (revision: Revision) =
        { revision with
            Emission =
                { revision.Emission with
                    Callable = { revision.Emission.Callable with Declarations = Map.ofList [ NodeId 2, declaration ] } } }
    Assert.Empty(Integrity.check (declared lazyStorage))
    let withdrawn =
        declared (withStorage (fun storage ->
            { storage with Lazies = Map.empty; LazyOccurrences = Map.empty; LazyValues = Set.empty; DefinitionOnlyThunks = Set.empty }))
    let violation = only "Emission.Callable.Declarations (LazyThunk)" (Integrity.check withdrawn)
    Assert.Equal(Some (NodeId 2), violation.Node)

[<Fact>]
let ``an identity named by the kind of a node is examined`` () =
    let reference = { node 3 (SemanticKind.VarRef("value", Some (NodeId 8))) [] with Type = boolType }
    let stated = covered { bindingWithLiteral with Nodes = bindingWithLiteral.Nodes.Add(NodeId 3, reference) }
    let violation = only "Nodes.Kind" (Integrity.check stated)
    Assert.Equal(Some (NodeId 8), violation.Node)

[<Theory>]
[<InlineData("Emission.Callable.ValueShapes")>]
[<InlineData("Emission.Callable.AliasTargets")>]
[<InlineData("Emission.Callable.Supports")>]
[<InlineData("Emission.Numeric.SourceTypes")>]
[<InlineData("Emission.Numeric.OccurrenceRepresentations")>]
let ``a node with no row in a table that covers every node is reported`` table =
    let callable = bindingWithLiteral.Emission.Callable
    let numeric = bindingWithLiteral.Emission.Numeric
    let emission =
        match table with
        | "Emission.Callable.ValueShapes" -> { bindingWithLiteral.Emission with Callable = { callable with ValueShapes = callable.ValueShapes.Remove(NodeId 2) } }
        | "Emission.Callable.AliasTargets" -> { bindingWithLiteral.Emission with Callable = { callable with AliasTargets = callable.AliasTargets.Remove(NodeId 2) } }
        | "Emission.Callable.Supports" -> { bindingWithLiteral.Emission with Callable = { callable with Supports = callable.Supports.Remove(NodeId 2) } }
        | "Emission.Numeric.SourceTypes" -> { bindingWithLiteral.Emission with Numeric = { numeric with SourceTypes = numeric.SourceTypes.Remove(NodeId 2) } }
        | _ -> { bindingWithLiteral.Emission with Numeric = { numeric with OccurrenceRepresentations = numeric.OccurrenceRepresentations.Remove(NodeId 2) } }
    let violation = Assert.Single(Integrity.check { bindingWithLiteral with Emission = emission })
    Assert.Equal(Some (NodeId 2), violation.Node)
    Assert.StartsWith("Nodes", violation.Part)
    Assert.Contains(table, violation.Reason)

[<Fact>]
let ``an inactive body is refused even when no numeric row is needed`` () =
    let unreachable = { bindingWithLiteral.Nodes[NodeId 2] with IsReachable = false }
    let numeric = bindingWithLiteral.Emission.Numeric
    let stated =
        { bindingWithLiteral with
            Nodes = bindingWithLiteral.Nodes.Add(NodeId 2, unreachable)
            Emission =
                { bindingWithLiteral.Emission with
                    Numeric =
                        { numeric with
                            SourceTypes = numeric.SourceTypes.Remove(NodeId 2)
                            OccurrenceRepresentations = numeric.OccurrenceRepresentations.Remove(NodeId 2) } } }
    let violations = Integrity.check stated
    Assert.Equal(2, violations.Length)
    let violation = within "Nodes" violations
    Assert.Equal(Some(NodeId 2), violation.Node)
    Assert.Contains("inactive", violation.Reason)
    let context = within "SourceReadings.Contexts" violations
    Assert.Equal(Some(NodeId 2), context.Node)
    Assert.Contains("no live body", context.Reason)

[<Theory>]
[<InlineData("Emission.Numeric.Required")>]
[<InlineData("Emission.Numeric.OperationRequired")>]
[<InlineData("Emission.Numeric.ResultSites")>]
[<InlineData("Emission.Memory.Required")>]
[<InlineData("Emission.Spatial.Required")>]
let ``a required site with no row is reported by the set that requires it`` part =
    let site = Set.ofList [ NodeId 2 ]
    let emission = bindingWithLiteral.Emission
    let stated =
        match part with
        | "Emission.Numeric.Required" -> { emission with Numeric = { emission.Numeric with Required = site } }
        | "Emission.Numeric.OperationRequired" -> { emission with Numeric = { emission.Numeric with OperationRequired = site } }
        | "Emission.Numeric.ResultSites" -> { emission with Numeric = { emission.Numeric with ResultSites = site } }
        | "Emission.Memory.Required" -> { emission with Memory = { emission.Memory with Required = site } }
        | _ -> { emission with Spatial = { emission.Spatial with Required = site } }
    let violation = only part (Integrity.check { bindingWithLiteral with Emission = stated })
    Assert.Equal(Some (NodeId 2), violation.Node)

[<Fact>]
let ``a required numeric site whose carrier is unresolved has its row`` () =
    let emission = bindingWithLiteral.Emission
    let numeric =
        { emission.Numeric with
            Required = Set.ofList [ NodeId 2 ]
            Unresolved = Map.ofList [ NodeId 2, "The carrier is not settled." ] }
    Assert.Empty(Integrity.check { bindingWithLiteral with Emission = { emission with Numeric = numeric } })

[<Fact>]
let ``the reason given to a reader names the first violations and counts the rest`` () =
    let edges : Hyperedge list =
        [ 10 .. 20 ] |> List.map (fun absent ->
            { Sources = [ NodeId absent ]; Target = NodeId 1; Class = EdgeClass.Reference; Role = EdgeRole.Definition; Ordinal = 0 })
    let reason = Integrity.describe (Integrity.check { bindingWithLiteral with Edges = edges })
    Assert.StartsWith("The revision is not well formed.", reason)
    Assert.Contains("Edges.Sources: Node 10 is named and is not held by the revision.", reason)
    Assert.Contains("and 3 more", reason)
    Assert.DoesNotContain("Node 18", reason)

[<Theory>]
[<InlineData("codata")>]
[<InlineData("emission")>]
[<InlineData("both")>]
let ``a fact held in two tables must be the same in both`` held =
    let join : CallableJoin =
        { Occurrence = NodeId 1; SourceType = boolType; Storage = NodeId 1; Read = NodeId 2; Alternatives = [ NodeId 2 ] }
    let other : CallableJoin = { join with Alternatives = [ NodeId 1 ] }
    let codata = bindingWithLiteral.Codata
    let callable = bindingWithLiteral.Emission.Callable
    let stated =
        match held with
        | "codata" -> { bindingWithLiteral with Codata = { codata with CallableJoins = Map.ofList [ NodeId 1, join ] } }
        | "emission" -> { bindingWithLiteral with Emission = { bindingWithLiteral.Emission with Callable = { callable with Joins = Map.ofList [ NodeId 1, join ] } } }
        | _ ->
            { bindingWithLiteral with
                Codata = { codata with CallableJoins = Map.ofList [ NodeId 1, join ] }
                Emission = { bindingWithLiteral.Emission with Callable = { callable with Joins = Map.ofList [ NodeId 1, other ] } } }
    let violation = only "Emission.Callable.Joins" (Integrity.check stated)
    Assert.Equal(Some (NodeId 1), violation.Node)
    Assert.Contains("Codata.CallableJoins", violation.Reason)
    let agreed =
        { bindingWithLiteral with
            Codata = { codata with CallableJoins = Map.ofList [ NodeId 1, join ] }
            Emission = { bindingWithLiteral.Emission with Callable = { callable with Joins = Map.ofList [ NodeId 1, join ] } } }
    Assert.Empty(Integrity.check agreed)

// Stored signature rows model a higher-order formal. Source typing and physical
// convention settlement remain Baker's responsibility; these controls read rows.
let private callableComponentRows kind =
  let formal, target = NodeId 3, NodeId 4
  let initial =
    { bindingWithLiteral with
        Nodes = bindingWithLiteral.Nodes
                  .Add(formal, node 3 (SemanticKind.PatternBinding "callback") [])
                  .Add(target, node 4 (SemanticKind.Binding("target", false, false, None)) []) }
    |> covered
  let carrier occurrence implementation parameters shapes : CallableCarrier =
    { Occurrence = occurrence; Kind = CallableKind.OrdinaryFlatClosure; Formation = occurrence
      EnvironmentValue = None; Contract = Error "Stored signature fixture"; Lifetime = []
      SourceType = boolType; Implementation = implementation; Parameters = parameters
      ParameterShapes = shapes; OmittedParameters = Set.empty; Result = NodeId 2
      ResultShape = CallableValueShape.Data(NodeId 2); Environment = None }
  let parameters = [ "callback", boolType, formal ]
  let carriers = Map.ofList [ NodeId 1, carrier (NodeId 1) (NodeId 1) parameters [CallableValueShape.Callable formal];
                             target, carrier target target [] [] ]
  let flow : CallableFlow =
    { Occurrence = formal; SourceType = boolType; Alternatives = [target]; Dependencies = Map.empty; Calls = [] }
  let join : CallableJoin =
    { Occurrence = formal; SourceType = boolType; Storage = formal; Read = formal; Alternatives = [target] }
  let carriers =
    if kind = "carrier" || kind = "duplicate" then carriers.Add(formal, carrier formal target [] []) else carriers
  let joins = if kind = "join" then Map.ofList [formal, join] else Map.empty
  let flows = if kind = "flow" || kind = "duplicate" then Map.ofList [formal, flow] else Map.empty
  let declaration id parameters : CallableEmissionDeclaration =
    { Lookup = id; Implementation = id; Parameters = parameters; Result = NodeId 2
      Context = LambdaContext.RegularClosure; Captures = []; Name = CallableSymbolName.Anonymous id
      Parent = None; Participants = Set.ofList (id :: NodeId 2 :: (parameters |> List.map (fun (_, _, formal) -> formal))) }
  let callable =
    { initial.Emission.Callable with
        Carriers = carriers; Joins = joins; Flows = flows
        Declarations = Map.ofList [NodeId 1, declaration (NodeId 1) parameters; target, declaration target []]
        Symbols = Map.ofList [NodeId 1, CallableSymbolName.Anonymous(NodeId 1); target, CallableSymbolName.Anonymous target]
        ClosedData = Set.singleton(NodeId 2)
        ValueShapes = initial.Emission.Callable.ValueShapes.Add(formal, CallableValueShape.Callable formal) }
  { initial with
      Codata = { initial.Codata with CallableCarriers = carriers; CallableJoins = joins; CallableFlows = flows }
      Emission = { initial.Emission with Callable = callable } }

[<Theory>]
[<InlineData("carrier")>]
[<InlineData("join")>]
[<InlineData("flow")>]
let ``callable signature components retain their single stored carrier owner`` kind =
  Assert.Empty(Integrity.check (callableComponentRows kind))

[<Theory>]
[<InlineData("missing")>]
[<InlineData("duplicate")>]
let ``callable signature components refuse missing or competing owner rows`` kind =
  let violation = only "Emission.Callable.Carriers.ParameterShapes" (Integrity.check (callableComponentRows kind))
  Assert.Equal(Some(NodeId 3), violation.Node)
  let reason =
    if kind = "missing" then "has no row in Emission.Callable.Carriers, Joins or Flows."
    else "Callable component has conflicting carrier, join or flow rows."
  Assert.Contains(reason, violation.Reason)

// A string literal (node 3) and its body-free current storage claim (identity 4). Node 5 is a call whose
// ordinal 0 is omitted and node 6 the declaration of the pool's space.
let private storageProof : ObligationInfo =
    { Id = "storage_text"; Kind = "storage-reservation"; Logic = "QF_LIA"
      Statement = "the storage of \"text\" reserves 5 bytes"; Source = "contract-test.clef:1:0"; Refs = []
      Body = ObligationBody.StorageReservation(4, 5) }

let private literalWithProof : Revision =
    let literal = node 3 (SemanticKind.Literal(NativeLiteral.String "text")) []
    let call = node 5 (SemanticKind.Literal(NativeLiteral.Bool true)) []
    let space = node 6 (SemanticKind.Literal(NativeLiteral.Bool false)) []
    { revision [ literal; call; space ] with
        CurrentClaims = Map.ofList [NodeId 4, storageProof]; Obligations = [storageProof]
        ObligationSources = Map.ofList [ NodeId 4, [ [ NodeId 3 ] ] ] }

let private pool (listed: int) : StaticStringPool =
    { Symbol = "__clef_static_strings"; Bytes = [ 116uy; 101uy; 120uy; 116uy; 0uy ]; Alignment = 1; Size = 5; UsedSize = 5
      Entries = [ { NodeIds = [ NodeId listed ]; Content = "text"; Offset = 0; Length = 4; StorageLength = 5 } ]
      SpaceName = "rodata"; Capacity = 4096L; SpaceAlignment = 1; Granularity = 1; DeclarationNode = NodeId 6 }

let private omission : OrdinaryOmission = { Site = NodeId 5; Origin = OrdinaryOmissionOrigin.CallArgument 0; Actual = NodeId 3 }

/// The literal with its storage row, and the pool given.
let private stored (row: LiteralStorage) (placed: StaticStringPool option) : Revision =
    { literalWithProof with StaticStringPool = placed; LiteralStorage = Map.ofList [ NodeId 3, row ] }

[<Fact>]
let ``a materialized literal names the pool entry that lists it`` () =
    Assert.Empty(Integrity.check (stored (LiteralStorage.Materialized 0) (Some (pool 3))))

[<Fact>]
let ``a literal that no demanded position reads states the omissions under which it is not entered`` () =
    Assert.Empty(Integrity.check (stored (LiteralStorage.NotMaterialized (StoragePremise.Established [ omission ])) None))

[<Fact>]
let ``a literal proof whose literal has no storage row is reported`` () =
    let violation = only "ObligationSources (literal proofs)" (Integrity.check literalWithProof)
    Assert.Equal(Some (NodeId 3), violation.Node)
    Assert.Contains("LiteralStorage", violation.Reason)

[<Theory>]
[<InlineData("no pool")>]
[<InlineData("no entry")>]
[<InlineData("other literal")>]
let ``a materialized row names an entry that the pool has for its literal`` defect =
    let violations =
        match defect with
        | "no pool" -> Integrity.check (stored (LiteralStorage.Materialized 0) None)
        | "no entry" -> Integrity.check (stored (LiteralStorage.Materialized 1) (Some (pool 3)))
        | _ -> Integrity.check (stored (LiteralStorage.Materialized 0) (Some (pool 5)))
    let violation = within "LiteralStorage" violations
    Assert.Equal(Some (NodeId 3), violation.Node)

[<Theory>]
[<InlineData("no row")>]
[<InlineData("not materialized")>]
let ``every literal a pool entry lists has a row that names the entry`` defect =
    let placed = { literalWithProof with StaticStringPool = Some (pool 3) }
    let violations =
        match defect with
        | "no row" -> Integrity.check placed
        | _ -> Integrity.check { placed with LiteralStorage = Map.ofList [ NodeId 3, LiteralStorage.NotMaterialized (StoragePremise.Established [ omission ]) ] }
    let violation = within "StaticStringPool.Entries" violations
    Assert.Equal(Some (NodeId 3), violation.Node)

[<Fact>]
let ``a row that is not materialized and states no omission is reported`` () =
    let violation = only "LiteralStorage" (Integrity.check (stored (LiteralStorage.NotMaterialized (StoragePremise.Established [])) None))
    Assert.Equal(Some (NodeId 3), violation.Node)

[<Fact>]
let ``an omission that names a node absent from the revision is reported`` () =
    let foreign = LiteralStorage.NotMaterialized (StoragePremise.Established [ { omission with Site = NodeId 9 } ])
    let violation = only "LiteralStorage (values)" (Integrity.check (stored foreign None))
    Assert.Equal(Some (NodeId 9), violation.Node)

[<Fact>]
let ``a storage premise that is pending is reported at its literal`` () =
    let violation = only "LiteralStorage" (Integrity.check (stored (LiteralStorage.NotMaterialized (StoragePremise.Pending [ omission ])) None))
    Assert.Equal(Some (NodeId 3), violation.Node)
    Assert.Contains("pending", violation.Reason)

// A string byte view at node 3 of source 4, whose extent source and one origin is the
// literal 5 and whose byte representation node 6 declares. The calls 7 and 9 supply
// the actuals 8 and 10, each of which reaches the literal 5.
let private octet : NumericRepresentation =
    { Name = "octet"; Capability = "native"; Family = "uint"; Bits = 8; MinMagnitude = "0"; MaxMagnitude = "255"; Boundary = "wrap" }

let private participant number role ordinal group : Participant =
    { Node = NodeId number; Role = role; Ordinal = ordinal; Group = NodeId group }

let private borrowed : Participant list =
    [ participant 3 ParticipantRole.Site 0 3
      participant 4 ParticipantRole.Source 0 3
      participant 5 ParticipantRole.ExtentSource 0 3
      participant 6 ParticipantRole.RepresentationDeclaration 0 3
      participant 7 ParticipantRole.ReachingCall 0 7
      participant 8 ParticipantRole.ReachingActual 0 7
      participant 5 ParticipantRole.Origin 0 7
      participant 9 ParticipantRole.ReachingCall 0 9
      participant 10 ParticipantRole.ReachingActual 0 9
      participant 5 ParticipantRole.Origin 0 9 ]

let private nodesOf (participants: Participant list) = participants |> List.map _.Node

let private byteView (participants: ParticipantEvidence) : BoundaryByteView =
    { Site = NodeId 3; Source = NodeId 4; ExtentSource = NodeId 5; Representation = octet; RepresentationDeclaration = NodeId 6
      StaticOrigins = Map.ofList [ NodeId 5, 4I ]; Participants = participants }

let private stringExtent (participants: ParticipantEvidence) : BoundaryStringExtent =
    { Site = NodeId 3; Source = NodeId 4; ExtentSource = NodeId 5; StaticOrigins = Map.ofList [ NodeId 5, 4I ]; Participants = participants }

let private borrowNodes = [ 3 .. 10 ] |> List.map (fun number -> node number (SemanticKind.Literal(NativeLiteral.Bool true)) [])

/// The nodes of the borrow with the edges given.
let private withEdges (edges: Hyperedge list) : Revision =
    { revision borrowNodes with Edges = edges }

/// The borrow's view row with the participants and the sources given.
let private viewEdge (participants: ParticipantEvidence) (sources: NodeId list) : Hyperedge =
    { Sources = sources; Target = NodeId 3; Class = EdgeClass.Range; Role = EdgeRole.StringByteView (byteView participants); Ordinal = 0 }

[<Fact>]
let ``one node in two roles and in two groups is no violation`` () =
    let occurrences = borrowed |> List.filter (fun occurrence -> occurrence.Node = NodeId 5)
    Assert.Equal(2, occurrences |> List.map _.Role |> List.distinct |> List.length)
    Assert.Equal(3, occurrences |> List.map _.Group |> List.distinct |> List.length)
    Assert.Empty(Integrity.check (withEdges [ viewEdge (ParticipantEvidence.Established borrowed) (nodesOf borrowed) ]))

[<Fact>]
let ``a historical participant needs no body when its ordered incidence is intact`` () =
    let foreign = borrowed @ [ participant 11 ParticipantRole.Path 0 7 ]
    let violations = Integrity.check (withEdges [ viewEdge (ParticipantEvidence.Established foreign) (nodesOf foreign) ])
    Assert.Empty violations

[<Theory>]
[<InlineData("prefix")>]
[<InlineData("order")>]
[<InlineData("set")>]
let ``an edge whose sources differ from its participants is reported at its site`` form =
    let sources =
        match form with
        | "prefix" -> NodeId 4 :: NodeId 5 :: nodesOf borrowed
        | "order" -> List.rev (nodesOf borrowed)
        | _ -> nodesOf borrowed |> List.distinct
    let violation = only "Edges (StringByteView)" (Integrity.check (withEdges [ viewEdge (ParticipantEvidence.Established borrowed) sources ]))
    Assert.Equal(Some (NodeId 3), violation.Node)

[<Theory>]
[<InlineData("no site")>]
[<InlineData("empty")>]
let ``an established list without the row's site is reported at the site`` form =
    let participants =
        match form with
        | "no site" -> borrowed |> List.filter (fun occurrence -> occurrence.Role <> ParticipantRole.Site)
        | _ -> []
    let violation = only "Edges (StringByteView)" (Integrity.check (withEdges [ viewEdge (ParticipantEvidence.Established participants) (nodesOf participants) ]))
    Assert.Equal(Some (NodeId 3), violation.Node)

[<Theory>]
[<InlineData("Edges (StringByteView)")>]
[<InlineData("Edges (StringExtent)")>]
[<InlineData("Emission.Boundary.ByteViews")>]
[<InlineData("Emission.Boundary.StringExtents")>]
let ``a string borrow row with pending participants is reported at its site`` part =
    let pending = ParticipantEvidence.Pending { Derived = borrowed }
    let boundary = (revision borrowNodes).Emission.Boundary
    let stated =
        match part with
        | "Edges (StringByteView)" -> withEdges [ viewEdge pending (nodesOf borrowed) ]
        | "Edges (StringExtent)" ->
            withEdges [ { Sources = nodesOf borrowed; Target = NodeId 3; Class = EdgeClass.Range; Role = EdgeRole.StringExtent (stringExtent pending); Ordinal = 0 } ]
        | "Emission.Boundary.ByteViews" ->
            let borrow = revision borrowNodes
            { borrow with Emission = { borrow.Emission with Boundary = { boundary with ByteViews = Map.ofList [ NodeId 3, byteView pending ] } } }
        | _ ->
            let borrow = revision borrowNodes
            { borrow with Emission = { borrow.Emission with Boundary = { boundary with StringExtents = Map.ofList [ NodeId 3, stringExtent pending ] } } }
    let violation = only part (Integrity.check stated)
    Assert.Equal(Some (NodeId 3), violation.Node)
    Assert.Contains("pending", violation.Reason)

/// The history row of the borrow at node 3, whose early derivation is the list given.
let private historyEdge (early: Participant list) : Hyperedge =
    { Sources = nodesOf early; Target = NodeId 3; Class = EdgeClass.Provenance
      Role = EdgeRole.StringBorrowHistory { Site = NodeId 3; Early = { Derived = early } }; Ordinal = 0 }

[<Fact>]
let ``a history row that names a node absent from the revision is reported`` () =
    let early = borrowed @ [ participant 11 ParticipantRole.OmissionSite 1 7 ]
    let violations = Integrity.check (withEdges [ viewEdge (ParticipantEvidence.Established borrowed) (nodesOf borrowed); historyEdge early ])
    let violation = within "Edges.Role" violations
    Assert.Equal(Some (NodeId 11), violation.Node)
    Assert.All(violations, fun other -> Assert.Equal(Some (NodeId 11), other.Node))

[<Fact>]
let ``a history row that differs from its current row is no violation`` () =
    let early = borrowed |> List.map (fun occurrence ->
        if occurrence.Role = ParticipantRole.ReachingCall && occurrence.Node = NodeId 7 then { occurrence with Node = NodeId 6 } else occurrence)
    Assert.NotEqual<Participant list>(borrowed, early)
    let premise = { Literal = NodeId 5; Early = [ { Site = NodeId 6; Origin = OrdinaryOmissionOrigin.CallArgument 0; Actual = NodeId 8 } ] }
    let literalHistory : Hyperedge =
        { Sources = [ NodeId 6; NodeId 8 ]; Target = NodeId 5; Class = EdgeClass.Provenance; Role = EdgeRole.LiteralStorageHistory premise; Ordinal = 0 }
    Assert.Empty(Integrity.check (withEdges [ viewEdge (ParticipantEvidence.Established borrowed) (nodesOf borrowed); historyEdge early; literalHistory ]))

// The borrow with the omitted call 20 of actual 21 under the omissions (22, 0, 23) and
// (24, 0, 25): each site in the group of the omitted call, each actual in the group of its site.
let private omissionNodes = [ 3 .. 10 ] @ [ 20 .. 25 ] |> List.map (fun number -> node number (SemanticKind.Literal(NativeLiteral.Bool true)) [])

let private omitted : Participant list =
    borrowed
    @ [ participant 20 ParticipantRole.OmittedCall 0 20
        participant 21 ParticipantRole.OmittedCallActual 0 20
        participant 22 ParticipantRole.OmissionSite 0 20
        participant 24 ParticipantRole.OmissionSite 0 20
        participant 23 ParticipantRole.OmittedActual 0 22
        participant 25 ParticipantRole.OmittedActual 0 24 ]

let private withOmissions (participants: Participant list) : Revision =
    { revision omissionNodes with Edges = [ viewEdge (ParticipantEvidence.Established participants) (nodesOf participants) ] }

[<Fact>]
let ``each omitted actual in the group of its omission site at the same ordinal is no violation`` () =
    Assert.Empty(Integrity.check (withOmissions omitted))

let private initializerOmitted =
  borrowed
  @ [ participant 22 ParticipantRole.OmissionBinding 0 20
      participant 23 ParticipantRole.OmittedInitializer 0 22 ]

[<Fact>]
let ``initializer omission and call argument omission pairs coexist without positional aliasing`` () =
  Assert.Empty(Integrity.check (withOmissions initializerOmitted))
  Assert.Empty(Integrity.check (withOmissions (omitted @ [participant 22 ParticipantRole.OmissionBinding 0 20; participant 23 ParticipantRole.OmittedInitializer 0 22])))

[<Theory>]
[<InlineData("no initializer")>]
[<InlineData("no binding")>]
[<InlineData("wrong group")>]
[<InlineData("duplicate initializer")>]
[<InlineData("call actual at binding")>]
[<InlineData("initializer at call site")>]
let ``initializer omission pairing refuses absent duplicate mismatched and cross-kind participants`` defect =
  let changed =
    match defect with
    | "no initializer" -> initializerOmitted |> List.filter (fun occurrence -> occurrence.Role <> ParticipantRole.OmittedInitializer)
    | "no binding" -> initializerOmitted |> List.filter (fun occurrence -> occurrence.Role <> ParticipantRole.OmissionBinding)
    | "wrong group" -> initializerOmitted |> List.map (fun occurrence -> if occurrence.Role = ParticipantRole.OmittedInitializer then {occurrence with Group = NodeId 20} else occurrence)
    | "duplicate initializer" -> initializerOmitted @ [participant 21 ParticipantRole.OmittedInitializer 0 22]
    | "call actual at binding" -> initializerOmitted |> List.map (fun occurrence -> if occurrence.Role = ParticipantRole.OmittedInitializer then {occurrence with Role = ParticipantRole.OmittedActual} else occurrence)
    | "initializer at call site" -> initializerOmitted |> List.map (fun occurrence -> if occurrence.Role = ParticipantRole.OmissionBinding then {occurrence with Role = ParticipantRole.OmissionSite} else occurrence)
    | other -> failwithf "Unknown initializer omission defect: %s" other
  let unplaced = "The omitted actual 23 of the string borrow row of node 3 is not in the group of an omission site at ordinal 0."
  let missing = "The omission site 22 at ordinal 0 of the string borrow row of node 3 has 0 omitted actuals, not one."
  let expected =
    match defect with
    | "no initializer" -> [missing]
    | "no binding" -> [unplaced]
    | "duplicate initializer" -> ["The omission site 22 at ordinal 0 of the string borrow row of node 3 has 2 omitted actuals, not one."]
    | _ -> [unplaced; missing]
  let failures = Integrity.incidence (withOmissions changed)
  Assert.Equal<string list>(List.sort expected, failures |> List.map _.Reason |> List.sort)
  Assert.All(failures, fun failure ->
    Assert.Equal("Edges (StringByteView)", failure.Part)
    Assert.Equal(Some(NodeId 3), failure.Node))

[<Theory>]
[<InlineData("binding")>]
[<InlineData("initializer")>]
[<InlineData("both")>]
let ``initializer omission participants refuse nonzero positions even when their pair agrees`` role =
  let changed = initializerOmitted |> List.map (fun occurrence ->
    match occurrence.Role with
    | ParticipantRole.OmissionBinding when role = "binding" || role = "both" -> {occurrence with Ordinal = 1}
    | ParticipantRole.OmittedInitializer when role = "initializer" || role = "both" -> {occurrence with Ordinal = 1}
    | _ -> occurrence)
  let reasons = Integrity.incidence (withOmissions changed) |> List.map _.Reason
  let nonpositional = "An initializer omission participant has a position although its role is non-positional."
  let expected =
    match role with
    | "both" -> [nonpositional; nonpositional]
    | "binding" ->
      [nonpositional
       "The omitted actual 23 of the string borrow row of node 3 is not in the group of an omission site at ordinal 0."
       "The omission site 22 at ordinal 1 of the string borrow row of node 3 has 0 omitted actuals, not one."]
    | _ ->
      [nonpositional
       "The omitted actual 23 of the string borrow row of node 3 is not in the group of an omission site at ordinal 1."
       "The omission site 22 at ordinal 0 of the string borrow row of node 3 has 0 omitted actuals, not one."]
  Assert.Equal<string list>(List.sort expected, List.sort reasons)

[<Theory>]
[<InlineData("actual in the omitted call's group")>]
[<InlineData("actual at another ordinal")>]
[<InlineData("two actuals at one site and ordinal")>]
[<InlineData("site with no actual")>]
let ``an omission whose site and actual are not paired is reported at the row's site`` defect =
    let changed =
        match defect with
        | "actual in the omitted call's group" ->
            omitted |> List.map (fun occurrence -> if occurrence.Node = NodeId 23 then { occurrence with Group = NodeId 20 } else occurrence)
        | "actual at another ordinal" ->
            omitted |> List.map (fun occurrence -> if occurrence.Node = NodeId 23 then { occurrence with Ordinal = 1 } else occurrence)
        | "two actuals at one site and ordinal" -> omitted @ [ participant 21 ParticipantRole.OmittedActual 0 22 ]
        | _ -> omitted |> List.filter (fun occurrence -> occurrence.Node <> NodeId 23)
    let violations = Integrity.check (withOmissions changed)
    Assert.NotEmpty violations
    Assert.All(violations, fun violation ->
        Assert.Equal("Edges (StringByteView)", violation.Part)
        Assert.Equal(Some (NodeId 3), violation.Node)
        Assert.Contains("omi", violation.Reason))

// The borrow whose demanded call 7 resolves to the lambda 30 with the body 31: the lambda,
// the call's argument 8 and the parameter 32 that remains for the call are in the group
// of the call, the body in the group of the lambda.
let private targetNodes = [ 3 .. 10 ] @ [ 30 .. 32 ] |> List.map (fun number -> node number (SemanticKind.Literal(NativeLiteral.Bool true)) [])

let private targeted : Participant list =
    borrowed
    @ [ participant 30 ParticipantRole.Callee 0 7
        participant 8 ParticipantRole.CalleeArgument 0 7
        participant 31 ParticipantRole.CalleeBody 0 30
        participant 32 ParticipantRole.CalleeParameter 0 7 ]

let private withTargets (participants: Participant list) : Revision =
    { revision targetNodes with Edges = [ viewEdge (ParticipantEvidence.Established participants) (nodesOf participants) ] }

[<Fact>]
let ``a target's body in the group of its lambda and its arguments and parameters in the group of the call are no violation`` () =
    Assert.Empty(Integrity.check (withTargets targeted))

[<Theory>]
[<InlineData("body in the call's group")>]
[<InlineData("parameter in the lambda's group")>]
[<InlineData("argument and parameter at different ordinals")>]
[<InlineData("argument in the lambda's group")>]
let ``a target's body, parameter or argument outside the group of its owner is reported at the row's site`` defect =
    let moved node group =
        targeted |> List.map (fun occurrence -> if occurrence.Node = NodeId node && occurrence.Role <> ParticipantRole.ReachingActual then { occurrence with Group = NodeId group } else occurrence)
    let changed =
        match defect with
        | "body in the call's group" -> moved 31 7
        | "parameter in the lambda's group" -> moved 32 30
        | "argument and parameter at different ordinals" ->
            targeted |> List.map (fun occurrence -> if occurrence.Node = NodeId 32 then { occurrence with Ordinal = 1 } else occurrence)
        | _ -> moved 8 30
    let violations = Integrity.check (withTargets changed)
    Assert.NotEmpty violations
    Assert.All(violations, fun violation ->
        Assert.Equal("Edges (StringByteView)", violation.Part)
        Assert.Equal(Some (NodeId 3), violation.Node)
        Assert.Contains("callee", violation.Reason))

// The same target with the nodes 33 and 34 held, for a second parameter and a second argument.
let private withPositions (participants: Participant list) : Revision =
    let nodes = targetNodes @ ([ 33; 34 ] |> List.map (fun number -> node number (SemanticKind.Literal(NativeLiteral.Bool true)) []))
    { revision nodes with Edges = [ viewEdge (ParticipantEvidence.Established participants) (nodesOf participants) ] }

[<Fact>]
let ``one argument and one parameter at each position of a call, the same argument at two positions, is no violation`` () =
    let twoPositions = targeted @ [ participant 8 ParticipantRole.CalleeArgument 1 7; participant 33 ParticipantRole.CalleeParameter 1 7 ]
    Assert.Empty(Integrity.check (withPositions twoPositions))

[<Theory>]
[<InlineData("two parameters at one position")>]
[<InlineData("two arguments at one position")>]
let ``two parameters or two arguments at one position of a call are reported at the row's site`` defect =
    let changed =
        match defect with
        | "two parameters at one position" -> targeted @ [ participant 33 ParticipantRole.CalleeParameter 0 7 ]
        | _ -> targeted @ [ participant 34 ParticipantRole.CalleeArgument 0 7 ]
    let violation = only "Edges (StringByteView)" (Integrity.check (withPositions changed))
    Assert.Equal(Some (NodeId 3), violation.Node)
    Assert.Contains("call 7", violation.Reason)
    Assert.Contains("ordinal 0", violation.Reason)

// These are deliberately stored-data controls. They do not claim that these
// rows prove the semantics of a source Result program; Baker owns that check.
let private branchAuthorityRevision : Revision =
    let one, two = NodeId 1, NodeId 2
    let occurrence role ordinal group node : Participant =
        { Node = node; Role = role; Ordinal = ordinal; Group = group }
    let observation : CallableBranchObservation =
        { Choice = one; Guard = two; Operator = two; Comparison = CallableBranchComparison.Equal
          TagRead = two; Subject = two; Literal = two; ExpectedTag = 0; UnionType = boolType
          TrueArm = one; FalseArm = two; SelectedArm = one
          Alternatives = [{ Constructor = one; Tag = 0; Payloads = [two] }]
          Participants =
            [ occurrence ParticipantRole.BranchChoice 0 one one
              occurrence ParticipantRole.BranchGuard 0 one two
              occurrence ParticipantRole.BranchOperator 0 one two
              occurrence ParticipantRole.BranchTagRead 0 one two
              occurrence ParticipantRole.BranchSubject 0 one two
              occurrence ParticipantRole.BranchLiteral 0 one two
              occurrence ParticipantRole.BranchTrueArm 0 one one
              occurrence ParticipantRole.BranchFalseArm 0 one two
              occurrence ParticipantRole.BranchSelectedArm 0 one one
              occurrence ParticipantRole.BranchConstructor 0 one one
              occurrence ParticipantRole.BranchPayload 0 one two ] }
    let authority : CallableBranchAuthority =
        { Scope = CallableBranchScope.WholeRevision; Observations = Map.ofList [one, observation]
          CarrierUses = Set.singleton one; FlowUses = Set.singleton two; CallUses = Set.singleton one }
    let carrier : CallableCarrier =
        { Occurrence = one; Kind = CallableKind.OrdinaryFlatClosure; Formation = one; EnvironmentValue = None
          Contract = Error "This branch-authority fixture publishes no aggregate convention."; Lifetime = []
          SourceType = boolType; Implementation = two; Parameters = []
          ParameterShapes = []; OmittedParameters = Set.empty; Result = two
          ResultShape = CallableValueShape.Data two; Environment = None }
    let flow : CallableFlow =
        { Occurrence = two; SourceType = boolType; Alternatives = [one]; Dependencies = Map.empty; Calls = [] }
    let carriers, flows = Map.ofList [one, carrier], Map.ofList [two, flow]
    let application =
        { bindingWithLiteral.Nodes[one] with Kind = SemanticKind.Application(two, []); Children = [two] }
    let codata =
        { bindingWithLiteral.Codata with
            CallableCarriers = carriers; CallableFlows = flows; CallableBranches = authority }
    let callable =
        { bindingWithLiteral.Emission.Callable with
            Carriers = carriers; Flows = flows; Branches = authority
            SignatureData = Map.ofList [one, Set.singleton two]
            Symbols = Map.ofList [two, CallableSymbolName.Anonymous two]
            Declarations = Map.ofList [two,
                { Lookup = two; Implementation = two; Parameters = []; Result = two
                  Context = LambdaContext.RegularClosure; Captures = []; Name = CallableSymbolName.Anonymous two
                  Parent = None; Participants = Set.singleton two }] }
    { bindingWithLiteral with
        Nodes = bindingWithLiteral.Nodes.Add(one, application)
        Codata = codata
        Emission = { bindingWithLiteral.Emission with Callable = callable } }

let private withBranchAuthority (authority: CallableBranchAuthority) (revision: Revision) =
    { revision with
        Codata = { revision.Codata with CallableBranches = authority }
        Emission = { revision.Emission with Callable = { revision.Emission.Callable with Branches = authority } } }

[<Fact>]
let ``shared callable branch authority references source applications outside emitted calls`` () =
    Assert.Empty branchAuthorityRevision.Emission.Callable.Calls
    Assert.NotEmpty branchAuthorityRevision.Emission.Callable.Branches.CallUses
    Assert.Empty(Integrity.check branchAuthorityRevision)

[<Theory>]
[<InlineData("observations")>]
[<InlineData("carriers")>]
[<InlineData("flows")>]
[<InlineData("calls")>]
let ``duplicated callable branch authority must agree field for field`` change =
    let original = branchAuthorityRevision
    Assert.Empty(Integrity.check original)
    let held = original.Emission.Callable.Branches
    let part, changed =
        match change with
        | "observations" ->
            let key, row = held.Observations |> Map.toList |> Assert.Single
            "Observations", { held with Observations = Map.ofList [key, { row with SelectedArm = row.FalseArm }] }
        | "carriers" -> "CarrierUses", { held with CarrierUses = Set.empty }
        | "flows" -> "FlowUses", { held with FlowUses = Set.empty }
        | "calls" -> "CallUses", { held with CallUses = Set.empty }
        | other -> failwithf "Unexpected authority mutation: %s" other
    let revision =
        { original with Emission = { original.Emission with Callable = { original.Emission.Callable with Branches = changed } } }
    let violation = within ("Emission.Callable.Branches." + part) (Integrity.check revision)
    Assert.Contains("differs from", violation.Reason)

[<Theory>]
[<InlineData(true)>]
[<InlineData(false)>]
let ``branch authority uses require the declared carrier or flow row`` carrier =
    let original = branchAuthorityRevision
    Assert.Empty(Integrity.check original)
    let codata, callable =
        if carrier then
            { original.Codata with CallableCarriers = Map.empty },
            { original.Emission.Callable with Carriers = Map.empty }
        else
            { original.Codata with CallableFlows = Map.empty },
            { original.Emission.Callable with Flows = Map.empty }
    let revision = { original with Codata = codata; Emission = { original.Emission with Callable = callable } }
    let part = if carrier then "CarrierUses" else "FlowUses"
    let violation = only ("Emission.Callable.Branches." + part) (Integrity.check revision)
    Assert.Contains("has no row", violation.Reason)

[<Fact>]
let ``branch call authority does not name a nonapplication node`` () =
    let original = branchAuthorityRevision
    Assert.Empty(Integrity.check original)
    let authority = { original.Emission.Callable.Branches with CallUses = original.Emission.Callable.Branches.CallUses.Add(NodeId 2) }
    let violation = only "Emission.Callable.Branches.CallUses" (Integrity.check (withBranchAuthority authority original))
    Assert.Contains("Nodes (reachable Application)", violation.Reason)

[<Theory>]
[<InlineData(true)>]
[<InlineData(false)>]
let ``whole revision branch authority and scalar reuse scopes cannot overlap`` nonempty =
    let original = branchAuthorityRevision
    Assert.Empty(Integrity.check original)
    let authority = if nonempty then original.Emission.Callable.Branches else CallableBranchAuthority.empty
    let scalar : WitnessRegion =
        { Identity = "scalar-data-control"; Flavor = WitnessRegionKind.ScalarCallable
          Root = Some(NodeId 1); Anchor = None; Path = []; Members = Set.ofList [NodeId 1; NodeId 2]
          Supports = Set.ofList [NodeId 1; NodeId 2]; OwnerSupport = SupportKey.WholeOwningAnalysisRegion "fixture-owner"
          CallableInterfaceDigest = CallableInterfaceDigest "callable-interface:scalar-data-control-ci"
          SemanticRealizationDigest = SemanticRealizationDigest "semantic-realization:scalar-data-control-sr"
          CanonicalProofSupportDigest = CanonicalProofSupportDigest "proof-support:scalar-data-control-ps"
          ProofSupportCoverage = ProofSupportCoverage.Local([], [])
          Dependencies = Set.empty }
    let revision = withBranchAuthority authority original
    let revision = { revision with Codata = { revision.Codata with WitnessSegmentation = Some { Version = 1; Regions = [scalar] } } }
    if nonempty then
        let violation = only "Codata.WitnessSegmentation" (Integrity.check revision)
        Assert.Contains("Whole-revision", violation.Reason)
    else Assert.Empty(Integrity.check revision)

[<Fact>]
let ``empty branch observations do not authorize nonempty use sets`` () =
    let original = branchAuthorityRevision
    Assert.Empty(Integrity.check original)
    let authority = { original.Emission.Callable.Branches with Observations = Map.empty }
    let violation = only "Emission.Callable.Branches" (Integrity.check (withBranchAuthority authority original))
    Assert.Contains("empty observation", violation.Reason)

[<Fact>]
let ``shared branch authority cannot omit a source application from both copies`` () =
    let original = branchAuthorityRevision
    Assert.Empty(Integrity.check original)
    let authority = { original.Emission.Callable.Branches with CallUses = Set.empty }
    let changed = withBranchAuthority authority original
    Assert.Equal<CallableBranchAuthority>(changed.Codata.CallableBranches, changed.Emission.Callable.Branches)
    let violation = only "Nodes (reachable Application, branch authority)" (Integrity.check changed)
    Assert.Equal(Some(NodeId 1), violation.Node)
    Assert.Contains("Emission.Callable.Branches.CallUses", violation.Reason)

// These source-authorized facts have no implementation, binding, declaration
// container or claim bodies. Their roles remain distinct from the single live use.
let private scopedFacts : Revision =
    let site, binding, code, formal, result, container, claim = NodeId 2, NodeId 99, NodeId 70, NodeId 100, NodeId 101, NodeId 50, NodeId 404
    let reference = { node 2 (SemanticKind.VarRef("function", Some binding)) [] with Parent = Some container }
    let initial = revision [reference]
    let account : SourcePortAccount = { Extent = 2048; Stamp = "module-port"; Positions = Map.ofList [17, site] }
    let frame : OccurrenceBreadcrumb = { Parent = container; Port = OccurrencePort.ModuleDeclaration; Ordinal = 17; Extent = 2048; Stamp = "module-port" }
    let bindingUse : BindingUseContract =
        { Binding = binding; Name = "function"; Class = SourceBindingClass.ImmutableValue
          IsProgramSlotIntent = false; HasProgramSlotAuthority = false; IsFunctionBinding = true
          IsCallableDeclaration = false; IsPartialApplication = false }
    let name = CallableSymbolName.LocalBinding(binding, "function")
    let declaration : CallableEmissionDeclaration =
        { Lookup = code; Implementation = code; Parameters = ["argument", boolType, formal]; Result = result
          Context = LambdaContext.RegularClosure; Captures = []; Name = name; Parent = Some container
          Participants = Set.ofList [binding; code; formal; result; NodeId 8000] }
    let callable =
        { initial.Emission.Callable with
            Declarations = Map.ofList [code, declaration]; Symbols = Map.ofList [code, name]
            SignatureData = Map.ofList [code, Set.ofList [formal; result]]
            ValueShapes = initial.Emission.Callable.ValueShapes.Add(formal, CallableValueShape.Data formal).Add(result, CallableValueShape.Data result) }
    let form = Ok(ValueRepresentation.Scalar SettledSlot.Bool)
    let numeric =
        { initial.Emission.Numeric with
            SourceTypes = initial.Emission.Numeric.SourceTypes.Add(formal, boolType).Add(result, boolType)
            OccurrenceRepresentations = initial.Emission.Numeric.OccurrenceRepresentations.Add(formal, form).Add(result, form) }
    let info : ObligationInfo =
        { Id = "current-order"; Kind = "order"; Logic = "QF_LIA"; Statement = "stored order"; Source = "fixture"; Refs = []
          Body = ObligationBody.ProgramInitializationOrder(0, 1, [0]) }
    let source =
        { initial.SourceReadings with
            Entries = [{ Focus = site; Reason = SourceEntryReason.DetachedDefinition; Context = [frame] }
                       { Focus = container; Reason = SourceEntryReason.BoundaryScope; Context = [] }]
            Ports = initial.SourceReadings.Ports.Add((container, OccurrencePort.ModuleDeclaration), account)
            Contexts = Map.ofList [site, [[frame]]; container, [[]]]
            ContextHeaders = Map.ofList [container, { Identity = container; Name = "namespace"; Ports = Map.ofList [OccurrencePort.ModuleDeclaration, account] }]
            BindingUses = Map.ofList [site, bindingUse] }
    let region : WitnessRegion =
        { Identity = "live-common"; Flavor = WitnessRegionKind.Common; Root = None; Anchor = Some container
          Path = [frame]; Members = Set.singleton site; Supports = Set.ofList [site; NodeId 8000]
          OwnerSupport = SupportKey.WholeOwningAnalysisRegion "current-source-owner"
          CallableInterfaceDigest = CallableInterfaceDigest "callable-interface:live-common-ci"
          SemanticRealizationDigest = SemanticRealizationDigest "semantic-realization:live-common-sr"
          CanonicalProofSupportDigest = CanonicalProofSupportDigest "proof-support:live-common-ps"
          ProofSupportCoverage = ProofSupportCoverage.Unclassified("common-whole-revision-envelope", Set.singleton "owner:current-source-owner")
          Dependencies = Set.empty }
    { initial with
        SourceReadings = source; Emission = { initial.Emission with Callable = callable; Numeric = numeric }
        CurrentClaims = Map.ofList [claim, info]; Obligations = [info]
        ObligationSources = Map.ofList [claim, [[NodeId 8000]; [NodeId 9000; NodeId 8000]]]
        Codata = { initial.Codata with WitnessSegmentation = Some {Version = 1; Regions = [region]} } }

[<Fact>]
let ``binding signature context and claim roles need no inactive bodies`` () =
    Assert.Single scopedFacts.Nodes |> ignore
    Assert.Empty(Integrity.check scopedFacts)
    let inventory = Integrity.named scopedFacts
    Assert.Contains(inventory, fun (part, ids) -> part = "CurrentClaims" && ids = [NodeId 404])
    Assert.Contains(inventory, fun (part, ids) -> part = "ObligationSources (values)" && List.contains (NodeId 9000) ids)

[<Fact>]
let ``a callable symbol does not replace a missing resolved binding use`` () =
    let stated = { scopedFacts with SourceReadings = {scopedFacts.SourceReadings with BindingUses = Map.empty} }
    let violation = within "Nodes.Kind" (Integrity.check stated)
    Assert.Equal(Some(NodeId 99), violation.Node)
    Assert.Contains("BindingUses", violation.Reason)

[<Fact>]
let ``a current claim cannot replace a signature representation row`` () =
    let stated = scopedFacts
    // Identity 404 has a current claim and grouped source account, but no
    // representation. Naming it in a signature does not turn a claim into data.
    let carrier : CallableCarrier =
        { Occurrence = NodeId 2; Kind = CallableKind.OrdinaryFlatClosure; Formation = NodeId 2; EnvironmentValue = None
          Contract = Error "This signature-row fixture publishes no aggregate convention."; Lifetime = []
          SourceType = boolType; Implementation = NodeId 70
          Parameters = ["argument", boolType, NodeId 100]; ParameterShapes = [CallableValueShape.Data(NodeId 404)]
          OmittedParameters = Set.empty; Result = NodeId 101; ResultShape = CallableValueShape.Data(NodeId 101); Environment = None }
    let callable =
        {stated.Emission.Callable with
            Carriers = Map.ofList [NodeId 2, carrier]
            ValueShapes = stated.Emission.Callable.ValueShapes.Add(NodeId 100, CallableValueShape.Data(NodeId 404))
            SignatureData = stated.Emission.Callable.SignatureData.Add(NodeId 2, Set.ofList [NodeId 404; NodeId 101])}
    let stated = {stated with Emission = {stated.Emission with Callable = callable}; Codata = {stated.Codata with CallableCarriers = callable.Carriers} }
    let violation = within "Emission.Callable.Carriers.ParameterShapes" (Integrity.check stated)
    Assert.Equal(Some(NodeId 404), violation.Node)
    Assert.Contains("OccurrenceRepresentations", violation.Reason)

[<Fact>]
let ``historical proof source groups are intact without resident bodies`` () =
    let edge sources ordinal : Hyperedge =
        {Sources = sources; Target = NodeId 404; Role = EdgeRole.Constrains; Class = EdgeClass.Obligation; Ordinal = ordinal}
    let edges = [edge [NodeId 8000] 0; edge [NodeId 9000; NodeId 8000] 1]
    Assert.Empty(Integrity.check {scopedFacts with Edges = edges})
    let corrupt = {scopedFacts with Edges = [edge [NodeId 8000] 0; edge [NodeId 8000; NodeId 9000] 1]}
    let violation = within "Edges (Constrains)" (Integrity.check corrupt)
    Assert.Equal(Some(NodeId 404), violation.Node)

[<Fact>]
let ``current claims require their complete grouped account`` () =
    let stated = {scopedFacts with ObligationSources = Map.empty}
    let violation = within "CurrentClaims" (Integrity.check stated)
    Assert.Equal(Some(NodeId 404), violation.Node)

[<Fact>]
let ``a context header cannot replace the exact source port account`` () =
    let stated = {scopedFacts with SourceReadings = {scopedFacts.SourceReadings with Ports = scopedFacts.SourceReadings.Ports.Remove(NodeId 50, OccurrencePort.ModuleDeclaration)} }
    Assert.Contains(Integrity.check stated, fun violation -> violation.Part = "SourceReadings.ContextHeaders.Ports")

[<Fact>]
let ``a support reference cannot replace the explicit whole owner policy`` () =
    let segmentation = scopedFacts.Codata.WitnessSegmentation.Value
    let regions = segmentation.Regions |> List.map (fun region -> {region with OwnerSupport = SupportKey.Node(NodeId 8000)})
    let stated = {scopedFacts with Codata = {scopedFacts.Codata with WitnessSegmentation = Some {segmentation with Regions = regions}} }
    let violation = within "Codata.WitnessSegmentation.Regions.OwnerSupport" (Integrity.check stated)
    Assert.Contains("whole owning", violation.Reason)

[<Fact>]
let ``context authority cannot traverse a source omitted local position`` () =
    let children = [{Ordinal = 0; Traversal = ChildTraversal.SourceOmitted(SupportKey.WholeOwningAnalysisRegion "owner", NodeId 2)}]
    let stated = {bindingWithLiteral with SourceReadings = {bindingWithLiteral.SourceReadings with Children = Map.ofList [NodeId 1, children; NodeId 2, []]}}
    let violation = within "SourceReadings.Contexts" (Integrity.check stated)
    Assert.Equal(Some(NodeId 2), violation.Node)
    Assert.Contains("omitted", violation.Reason)

[<Fact>]
let ``context headers cannot stand in for structural parent bodies`` () =
    let source = scopedFacts.SourceReadings
    let header = source.ContextHeaders[NodeId 50]
    let account = header.Ports[OccurrencePort.ModuleDeclaration]
    let frame : OccurrenceBreadcrumb = {Parent = NodeId 50; Port = OccurrencePort.StructuralChild; Ordinal = 17; Extent = 2048; Stamp = "module-port"}
    let source =
        {source with
            Ports = source.Ports.Remove(NodeId 50, OccurrencePort.ModuleDeclaration).Add((NodeId 50, OccurrencePort.StructuralChild), account)
            ContextHeaders = source.ContextHeaders.Add(NodeId 50, {header with Ports = Map.ofList [OccurrencePort.StructuralChild, account]})
            Contexts = source.Contexts.Add(NodeId 2, [[frame]])
            Entries = source.Entries |> List.map (fun entry -> if entry.Focus = NodeId 2 then {entry with Context = [frame]} else entry)}
    let violation = within "SourceReadings.Contexts" (Integrity.check {scopedFacts with SourceReadings = source})
    Assert.Contains("cannot stand in", violation.Reason)

// Numeric rows copy provenance and complete proof participants without loading
// their source bodies. Only the ordered executable operands remain live here.
let private numericOperationFacts : Revision =
    let integer =
        TypeIdentity.Application(
            { Declaration = {Module = []; Name = "int32"}; Parameters = []; NativeKind = Some(NTUKind.NTUint(NTUWidth.Fixed 32)) }, [])
    let operation = {node 1 (SemanticKind.Application(NodeId 2, [NodeId 3; NodeId 4])) [2; 3; 4] with Type = integer}
    let callee = {node 2 (SemanticKind.VarRef("add", None)) [] with Parent = Some(NodeId 1)}
    let literal id value =
        {node id (SemanticKind.Literal(NativeLiteral.Int(value, NTUKind.NTUint(NTUWidth.Fixed 32)))) [] with
            Type = integer; Parent = Some(NodeId 1)}
    let initial = revision [operation; callee; literal 3 1L; literal 4 3L]
    let carrier site lower upper : ScalarCarrier =
        { Site = NodeId site; Slot = SettledSlot.Integer(32, None); Range = ValueRange.Bounded(lower, upper)
          Representation = None; Declaration = Some(NodeId 64); SourceType = integer; Obligations = [NodeId 404]
          Participants = Set.ofList [NodeId site; NodeId 64; NodeId 8000] }
    let values = Map.ofList [NodeId 1, carrier 1 4I 8I; NodeId 3, carrier 3 1I 4I; NodeId 4, carrier 4 3I 4I]
    let adaptation operand fromBits intoBits : Meet =
        {Consumer = NodeId 1; Operand = NodeId operand; From = fromBits; To = intoBits; Adapt = if fromBits < intoBits then MeetKind.ExtendSigned else MeetKind.Truncate}
    let settled : NumericOperationWitness =
        { Site = NodeId 1; Callee = NodeId 2; Kind = NumericOperationKind.Add; Form = NumericOperationForm.Integer true
          Operands = [3; 4] |> List.map (fun site -> {Actual = NodeId site; Carrier = Some values[NodeId site]; Adaptation = Some(adaptation site 32 64)})
          OperationCarrier = Some(SettledSlot.Integer(64, None)); Representation = None; Declaration = Some(NodeId 64)
          Result = values[NodeId 1]; ResultAdaptation = Some(adaptation 1 64 32); Range = Some(ValueRange.Bounded(4I, 8I))
          Obligations = [NodeId 404]; Participants = Set.ofList [NodeId 1; NodeId 2; NodeId 3; NodeId 4; NodeId 64; NodeId 8000] }
    let info = {scopedFacts.CurrentClaims[NodeId 404] with Body = ObligationBody.IntegerRepresentationCoverage(4I, 8I, -2147483648I, 2147483647I)}
    {initial with
        CurrentClaims = Map.ofList [NodeId 404, info]; Obligations = [info]
        ObligationSources = Map.ofList [NodeId 404, [[NodeId 64; NodeId 8000]; [NodeId 3; NodeId 4]]]
        Emission =
            {initial.Emission with
                Numeric =
                    {initial.Emission.Numeric with
                        Values = values; Operations = Map.ofList [NodeId 1, settled]; Required = Set.ofList [NodeId 1; NodeId 3; NodeId 4]
                        OperationRequired = Set.singleton(NodeId 1); ResultSites = Set.singleton(NodeId 1)} } }

let private withNumericOperation operation (revision: Revision) =
    {revision with Emission = {revision.Emission with Numeric = {revision.Emission.Numeric with Operations = Map.ofList [NodeId 1, operation]}}}

[<Fact>]
let ``numeric carriers retain declarations claims and historical participants without bodies`` () =
    Assert.Empty(Integrity.check numericOperationFacts)
    let inventory = Integrity.named numericOperationFacts
    for part in ["Emission.Numeric.Operations.Operands"; "Emission.Numeric.Operations.Result"] do
        let identities = inventory |> List.find (fun (name, _) -> name = part) |> snd
        for identity in [NodeId 64; NodeId 404; NodeId 8000] do Assert.Contains(identity, identities)
    for identity in [NodeId 64; NodeId 404; NodeId 8000] do Assert.False(numericOperationFacts.Nodes.ContainsKey identity)

[<Fact>]
let ``a numeric scalar row cannot replace an absent executable operand`` () =
    let stated = {numericOperationFacts with Nodes = numericOperationFacts.Nodes.Remove(NodeId 3)}
    let violation = within "Emission.Numeric.Operations.Operands.Actual" (Integrity.check stated)
    Assert.Equal(Some(NodeId 3), violation.Node)

[<Theory>]
[<InlineData(true)>]
[<InlineData(false)>]
let ``embedded numeric carriers must match their exact current scalar row`` result =
    let operation = numericOperationFacts.Emission.Numeric.Operations[NodeId 1]
    let changed =
        if result then {operation with Result = {operation.Result with Participants = Set.singleton(NodeId 1)}}
        else {operation with Operands = operation.Operands |> List.map (fun operand -> if operand.Actual = NodeId 3 then {operand with Carrier = operand.Carrier |> Option.map (fun carrier -> {carrier with Slot = SettledSlot.Integer(64, None)})} else operand)}
    let part = if result then "Emission.Numeric.Operations.Result" else "Emission.Numeric.Operations.Operands.Carrier"
    let violation = within part (Integrity.check (withNumericOperation changed numericOperationFacts))
    Assert.Contains("exact scalar carrier", violation.Reason)

[<Theory>]
[<InlineData(true)>]
[<InlineData(false)>]
let ``embedded numeric carrier sites cannot be replaced by a current claim identity`` result =
    let operation = numericOperationFacts.Emission.Numeric.Operations[NodeId 1]
    let changed =
        if result then {operation with Result = {operation.Result with Site = NodeId 404}}
        else {operation with Operands = operation.Operands |> List.map (fun operand -> if operand.Actual = NodeId 3 then {operand with Carrier = operand.Carrier |> Option.map (fun carrier -> {carrier with Site = NodeId 404})} else operand)}
    let part = if result then "Emission.Numeric.Operations.Result" else "Emission.Numeric.Operations.Operands.Carrier"
    Assert.Contains(Integrity.check (withNumericOperation changed numericOperationFacts), fun violation -> violation.Part = part && violation.Reason.Contains("different site"))

[<Fact>]
let ``embedded numeric carrier claims require their current grouped claim account`` () =
    let noClaim = {numericOperationFacts with CurrentClaims = Map.empty; Obligations = []; ObligationSources = Map.empty}
    let violations = Integrity.check noClaim
    for part in ["Emission.Numeric.Operations.Operands.Carrier"; "Emission.Numeric.Operations.Result"] do
        Assert.Contains(violations, fun violation -> violation.Part = part && violation.Node = Some(NodeId 404) && violation.Reason.Contains("CurrentClaims"))
    let noGroup = {numericOperationFacts with ObligationSources = Map.empty}
    let violation = within "CurrentClaims" (Integrity.check noGroup)
    Assert.Equal(Some(NodeId 404), violation.Node)

[<Theory>]
[<InlineData(true)>]
[<InlineData(false)>]
let ``numeric adaptations retain the exact consuming operation and operand`` result =
    let operation = numericOperationFacts.Emission.Numeric.Operations[NodeId 1]
    let changed =
        if result then {operation with ResultAdaptation = operation.ResultAdaptation |> Option.map (fun row -> {row with Operand = NodeId 3})}
        else {operation with Operands = operation.Operands |> List.map (fun operand -> if operand.Actual = NodeId 3 then {operand with Adaptation = operand.Adaptation |> Option.map (fun row -> {row with Consumer = NodeId 4})} else operand)}
    let part = if result then "Emission.Numeric.Operations.ResultAdaptation" else "Emission.Numeric.Operations.Operands.Adaptation"
    let violation = within part (Integrity.check (withNumericOperation changed numericOperationFacts))
    Assert.Contains("different", violation.Reason)

let private memoryExtentFacts =
    let result = numericOperationFacts.Emission.Numeric.Values[NodeId 1]
    let row : MemoryArrayExtentWitness =
        {Site = NodeId 1; Source = NodeId 3; Element = SettledSlot.Integer(32, None); Result = result
         Participants = Set.ofList [NodeId 1; NodeId 3; NodeId 64; NodeId 404; NodeId 8000]}
    let memory =
        {numericOperationFacts.Emission.Memory with
            Required = Set.singleton(NodeId 1)
            Operations = Map.ofList [NodeId 1, MemoryWitnessOperation.ArrayExtent row]}
    {numericOperationFacts with Emission = {numericOperationFacts.Emission with Memory = memory}}

let private withMemoryExtent (change: MemoryArrayExtentWitness -> MemoryArrayExtentWitness) (revision: Revision) =
    let current = match revision.Emission.Memory.Operations[NodeId 1] with MemoryWitnessOperation.ArrayExtent row -> row | _ -> failwith "Expected extent"
    let memory =
        {revision.Emission.Memory with
            Operations = revision.Emission.Memory.Operations.Add(NodeId 1, MemoryWitnessOperation.ArrayExtent(change current))}
    {revision with Emission = {revision.Emission with Memory = memory}}

[<Fact>]
let ``a memory extent retains exact scalar and claim accounts without provenance bodies`` () =
    Assert.Empty(Integrity.check memoryExtentFacts)
    let identities = Integrity.named memoryExtentFacts |> List.find(fun (part, _) -> part = "Emission.Memory.Operations (values)") |> snd
    for identity in [NodeId 64; NodeId 404; NodeId 8000] do
        Assert.Contains(identity, identities)
        Assert.False(memoryExtentFacts.Nodes.ContainsKey identity)

[<Theory>]
[<InlineData("operand")>]
[<InlineData("carrier")>]
[<InlineData("carrier-site")>]
let ``a memory extent refuses wrong role operands and changed carriers`` defect =
    let changed, part =
        match defect with
        | "operand" -> withMemoryExtent (fun row -> {row with Source = NodeId 8000}) memoryExtentFacts, "Emission.Memory.Operations.ArrayExtent.Source"
        | "carrier" -> withMemoryExtent (fun row -> {row with Result = {row.Result with Participants = Set.empty}}) memoryExtentFacts, "Emission.Memory.Operations.ArrayExtent.Result"
        | _ -> withMemoryExtent (fun row -> {row with Result = {row.Result with Site = NodeId 404}}) memoryExtentFacts, "Emission.Memory.Operations.ArrayExtent.Result"
    Assert.Contains(Integrity.check changed, fun violation -> violation.Part = part)

let private snapshotFacts =
    let baseRevision = numericOperationFacts
    let additional = [5..11] |> List.map(fun site -> node site (SemanticKind.Literal NativeLiteral.Unit) [])
    let coveredRows = covered {baseRevision with Nodes = additional |> List.fold(fun (nodes: Map<NodeId, SemanticNode>) row -> nodes.Add(row.Id, row)) baseRevision.Nodes}
    let current = baseRevision.CurrentClaims
    let scalar (site: int) : ScalarCarrier = {baseRevision.Emission.Numeric.Values[NodeId 3] with Site = NodeId site}
    let numeric =
        {baseRevision.Emission.Numeric with
            SourceTypes = coveredRows.Emission.Numeric.SourceTypes
            OccurrenceRepresentations = coveredRows.Emission.Numeric.OccurrenceRepresentations
            Values = [5; 6] |> List.fold(fun (table: Map<NodeId, ScalarCarrier>) site -> table.Add(NodeId site, scalar site)) baseRevision.Emission.Numeric.Values}
    let requirement : RequirementWitness =
        {Site = NodeId 7; Condition = NodeId 8; Diagnostic = "bounded construction"; Frontier = NodeId 9
         Continuation = NodeId 10; PatternTest = None; Participants = [NodeId 9; NodeId 7; NodeId 8; NodeId 10]}
    let allocation : MemoryArrayAllocationWitness =
        {Site = NodeId 11; Count = NodeId 5; CountCarrier = numeric.Values[NodeId 5]; IndexUnsigned = true
         Element = SettledSlot.Integer(32, None); ElementBytes = 4; Alignment = 4; Residence = MemoryResidence.Stack(NodeId 1, NodeId 5521)
         MinimumCount = 1I; MaximumCount = 4I; Requirement = requirement
         Construction =
             {Site = NodeId 11; Owner = NodeId 6; Count = {Actual = NodeId 5; Binding = NodeId 5; Reference = NodeId 5}
              Default = None; Initialization = None
              Guard = {Requirement = requirement.Site; Predicate = requirement.Condition; Frontier = requirement.Frontier
                       Continuation = requirement.Continuation; Count = NodeId 5; Offset = None; Buffer = None; Length = None
                       Zero = NodeId 3; NonnegativeCount = requirement.Condition; NonnegativeOffset = None; End = None; Within = None}
              Participants = Set.ofList [NodeId 5; NodeId 64; NodeId 5521; NodeId 8000]}
         Participants = Set.ofList [NodeId 5; NodeId 64; NodeId 5521; NodeId 8000]}
    let copy : MemoryArrayCopyWitness =
        {Site = NodeId 6; Source = NodeId 1; SourceOffset = NodeId 3; Destination = NodeId 11; DestinationOffset = NodeId 4
         Count = NodeId 5; CountCarrier = numeric.Values[NodeId 5]; Allocation = Some(NodeId 11); Loop = None
         CountOperand = {Actual = NodeId 5; Binding = NodeId 5; Reference = NodeId 5}
         Read = None; Write = None; Requirements = [requirement]; Participants = Set.ofList [NodeId 64; NodeId 404; NodeId 8000]}
    let view : MemoryStringViewWitness =
        {Site = NodeId 1; Source = NodeId 3; Owner = NodeId 8000; Snapshot = NodeId 6; Direction = MemoryStringViewDirection.ToBytes; Checked = None
         SourceCarrier = numeric.OccurrenceRepresentations[NodeId 3] |> Result.defaultWith failwith
         ResultCarrier = numeric.OccurrenceRepresentations[NodeId 1] |> Result.defaultWith failwith
         Element = SettledSlot.Integer(32, None)
         Representation = {Name = "int32"; Capability = "native"; Family = "int"; Bits = 32; MinMagnitude = "-2147483648"; MaxMagnitude = "2147483647"; Boundary = "wrap"}
         Declaration = NodeId 64; Extent = numeric.Values[NodeId 5]; Participants = Set.ofList [NodeId 64; NodeId 404; NodeId 8000]}
    let memory =
        {coveredRows.Emission.Memory with
            Operations = Map.ofList [NodeId 1, MemoryWitnessOperation.StringView view; NodeId 11, MemoryWitnessOperation.ArrayAllocation allocation]
            ArrayCopies = Map.ofList [NodeId 6, copy]; Required = Set.ofList [NodeId 1; NodeId 11]}
    let storage = {coveredRows.Emission.Storage with Requirements = Map.ofList [NodeId 7, requirement]}
    {coveredRows with CurrentClaims = current; Emission = {coveredRows.Emission with Numeric = numeric; Memory = memory; Storage = storage}}

let private changeView change (revision: Revision) =
    let current = match revision.Emission.Memory.Operations[NodeId 1] with MemoryWitnessOperation.StringView row -> row | _ -> failwith "Expected view"
    let memory =
        {revision.Emission.Memory with
            Operations = revision.Emission.Memory.Operations.Add(NodeId 1, MemoryWitnessOperation.StringView(change current))}
    {revision with Emission = {revision.Emission with Memory = memory}}

[<Fact>]
let ``snapshot extent allocation and requirements have exact shared accounts without space bodies`` () =
    Assert.Empty(Integrity.check snapshotFacts)
    Assert.False(snapshotFacts.Nodes.ContainsKey(NodeId 5521))

[<Theory>]
[<InlineData("snapshot")>]
[<InlineData("extent")>]
[<InlineData("physical-carrier")>]
[<InlineData("requirement")>]
[<InlineData("allocation")>]
let ``snapshot accounts cannot borrow historical identities or altered shared rows`` defect =
    let changed, part =
        match defect with
        | "snapshot" -> changeView (fun row -> {row with Snapshot = NodeId 8000}) snapshotFacts, "Emission.Memory.Operations.StringView.Snapshot"
        | "extent" -> changeView (fun row -> {row with Extent = snapshotFacts.Emission.Numeric.Values[NodeId 6]}) snapshotFacts, "Emission.Memory.Operations.StringView.Snapshot"
        | "physical-carrier" -> changeView (fun row -> {row with SourceCarrier = ValueRepresentation.Scalar(SettledSlot.Integer(64, None))}) snapshotFacts, "Emission.Memory.Operations.StringView.SourceCarrier"
        | "requirement" ->
            {snapshotFacts with Emission = {snapshotFacts.Emission with Storage = {snapshotFacts.Emission.Storage with Requirements = Map.empty}}}, "Emission.Memory.Operations.ArrayAllocation.Requirement"
        | _ ->
            let copy = snapshotFacts.Emission.Memory.ArrayCopies[NodeId 6]
            {snapshotFacts with Emission = {snapshotFacts.Emission with Memory = {snapshotFacts.Emission.Memory with ArrayCopies = Map.ofList [NodeId 6, {copy with Allocation = Some(NodeId 8000)}]}}}, "Emission.Memory.ArrayCopies.Allocation"
    Assert.Contains(Integrity.check changed, fun violation -> violation.Part = part)

let private programStorageFacts =
    let space : BAREWire.Platform.MemorySpace =
        {Name = "program"; Kind = "ram"; Capacity = 4096L; Alignment = 8; Granularity = 8; Growth = "fixed"; Access = "rw"
         Base = None; Notes = ""; MapKind = ""; Since = ""; Until = ""}
    let identity = ProgramStorageIdentity.Allocation(NodeId 3)
    let entry : ProgramStorageEntry =
        {Identity = identity; SourceType = numericOperationFacts.Nodes[NodeId 3].Type; Shape = ProgramStorageShape.Bytes
         Bytes = 16; Alignment = 8; SpaceNode = NodeId 5521; Space = space; Participants = Set.ofList [NodeId 64; NodeId 5521; NodeId 8000]}
    let reservation : BAREWire.Platform.WritableReservation =
        {Space = space; Requests = [|{Name = "allocation:3"; Length = 16L; Alignment = 8}|]; PayloadSize = 16L}
    let storage : ProgramStorageInventory =
        {Entries = Map.ofList [identity, entry]; Reservations = Map.ofList [NodeId 5521, reservation]; Unresolved = Map.empty}
    {numericOperationFacts with
        Codata = {numericOperationFacts.Codata with ProgramStorage = storage}
        Emission = {numericOperationFacts.Emission with Storage = {numericOperationFacts.Emission.Storage with ProgramStorage = storage}}}

[<Fact>]
let ``program entries and reservations carry the exact declared space without its body`` () =
    Assert.Empty(Integrity.check programStorageFacts)
    Assert.False(programStorageFacts.Nodes.ContainsKey(NodeId 5521))

[<Theory>]
[<InlineData("space")>]
[<InlineData("requests")>]
[<InlineData("identity")>]
let ``program storage refuses mismatched space inventory and entry identities`` defect =
    let storage = programStorageFacts.Codata.ProgramStorage
    let reservation = storage.Reservations[NodeId 5521]
    let identity = ProgramStorageIdentity.Allocation(NodeId 3)
    let altered =
        match defect with
        | "space" -> {storage with Reservations = storage.Reservations.Add(NodeId 5521, {reservation with Space = {reservation.Space with Capacity = 2048L}})}
        | "requests" -> {storage with Reservations = storage.Reservations.Add(NodeId 5521, {reservation with Requests = [|{reservation.Requests[0] with Length = 8L}|]})}
        | _ -> {storage with Entries = storage.Entries.Add(identity, {storage.Entries[identity] with Identity = ProgramStorageIdentity.Allocation(NodeId 4)})}
    let revision =
        {programStorageFacts with
            Codata = {programStorageFacts.Codata with ProgramStorage = altered}
            Emission = {programStorageFacts.Emission with Storage = {programStorageFacts.Emission.Storage with ProgramStorage = altered}}}
    Assert.Contains(Integrity.check revision, fun violation -> violation.Part.StartsWith("Codata.ProgramStorage", System.StringComparison.Ordinal))

let private moduleUnitFacts =
    let id = NodeId 50
    let source = scopedFacts.SourceReadings
    let callable =
        {scopedFacts.Emission.Callable with
            ValueShapes = scopedFacts.Emission.Callable.ValueShapes.Add(id, CallableValueShape.Data id)
            AliasTargets = scopedFacts.Emission.Callable.AliasTargets.Add(id, id)
            UnitNodes = Set.singleton id; ClosedData = Set.singleton id
            Supports = scopedFacts.Emission.Callable.Supports.Add(id, Set.singleton(NodeId 9000))}
    let numeric =
        {scopedFacts.Emission.Numeric with
            SourceTypes = scopedFacts.Emission.Numeric.SourceTypes.Add(id, unitType)
            OccurrenceRepresentations = scopedFacts.Emission.Numeric.OccurrenceRepresentations.Add(id, Ok(ValueRepresentation.Scalar SettledSlot.Unit))}
    {scopedFacts with SourceReadings = source; Emission = {scopedFacts.Emission with Callable = callable; Numeric = numeric}}

[<Fact>]
let ``a module header carries its exact unit metadata without a module body`` () =
    Assert.Empty(Integrity.check moduleUnitFacts)
    Assert.False(moduleUnitFacts.Nodes.ContainsKey(NodeId 50))

[<Theory>]
[<InlineData("header")>]
[<InlineData("type")>]
[<InlineData("representation")>]
[<InlineData("alias")>]
let ``module unit metadata cannot be justified by arbitrary historical identity or conflicting facts`` defect =
    let id = NodeId 50
    let changed =
        match defect with
        | "header" -> {moduleUnitFacts with SourceReadings = {moduleUnitFacts.SourceReadings with ContextHeaders = Map.empty}}
        | "type" -> {moduleUnitFacts with Emission = {moduleUnitFacts.Emission with Numeric = {moduleUnitFacts.Emission.Numeric with SourceTypes = moduleUnitFacts.Emission.Numeric.SourceTypes.Add(id, boolType)}}}
        | "representation" -> {moduleUnitFacts with Emission = {moduleUnitFacts.Emission with Numeric = {moduleUnitFacts.Emission.Numeric with OccurrenceRepresentations = moduleUnitFacts.Emission.Numeric.OccurrenceRepresentations.Add(id, Ok(ValueRepresentation.Scalar SettledSlot.Bool))}}}
        | _ -> {moduleUnitFacts with Emission = {moduleUnitFacts.Emission with Callable = {moduleUnitFacts.Emission.Callable with AliasTargets = moduleUnitFacts.Emission.Callable.AliasTargets.Add(id, NodeId 9000)}}}
    Assert.Contains(Integrity.check changed, fun violation -> violation.Part = "Emission.Callable.ValueShapes" && violation.Node = Some id)

let private kernelStepFacts =
    let step = numericOperationFacts.Emission.Numeric.Operations[NodeId 1]
    let fact : BoundaryDeclarationFact = {Form = "record"; Text = []; Numbers = []; References = []; Children = []; Parent = None; SourceType = unitType}
    let transport : KernelTransport =
        {Declaration = NodeId 64; Representation = {Name = "int32"; Capability = "native"; Family = "int"; Bits = 32; MinMagnitude = "-2147483648"; MaxMagnitude = "2147483647"; Boundary = "wrap"}
         Range = ValueRange.Bounded(-2147483648I, 2147483647I)}
    let ingress : KernelIngress =
        {Site = NodeId 1; Scope = NodeId 2; Target = NodeId 64; Core = NodeId 64; ComputeBinding = NodeId 2; Implementation = NodeId 2
         ComputePath = Set.singleton(NodeId 2); Uses = Map.empty; Parameters = []; Result = NodeId 1; Inputs = []; Output = transport
         Participants = Set.singleton(NodeId 8000); Premises = Map.ofList [NodeId 64, fact]; SourceFiles = Map.empty; Platform = None}
    let target : KernelTargetPlan =
        {Declaration = NodeId 64; Device = "npu2"; Columns = 8; ShimRow = 0; ComputeRow = 2; FifoDepth = 2; Iterations = 1I; Participants = Set.singleton(NodeId 9000)}
    let kernel : KernelModuleWitness =
        {Site = NodeId 1; Scope = NodeId 2; Name = "kernel"; ComputeBinding = NodeId 2; Implementation = NodeId 2; Parameters = []; Result = NodeId 1
         Steps = [KernelScalarStep.Operation step]; Ingress = ingress; ElementsSite = NodeId 3; GrainSite = NodeId 4; Elements = 4; Grain = 4
         Target = target; Tiles = []; MetadataOnly = Set.singleton(NodeId 9000); Participants = Set.singleton(NodeId 8000); Obligations = [NodeId 404]}
    let spatial =
        {numericOperationFacts.Emission.Spatial with
            Kernels = Map.ofList [NodeId 1, kernel]; MetadataOnly = kernel.MetadataOnly; Required = Set.singleton(NodeId 1)}
    {numericOperationFacts with Emission = {numericOperationFacts.Emission with Spatial = spatial}}

[<Fact>]
let ``kernel scalar steps retain exact numeric rows and typed ingress without topology bodies`` () =
    Assert.Empty(Integrity.check kernelStepFacts)

[<Theory>]
[<InlineData("body")>]
[<InlineData("operation")>]
[<InlineData("claim")>]
[<InlineData("transport")>]
let ``kernel topology premises cannot authorize missing or altered executable steps`` defect =
    let spatial = kernelStepFacts.Emission.Spatial
    let kernel = spatial.Kernels[NodeId 1]
    let changed, part =
        match defect with
        | "body" -> {kernelStepFacts with Nodes = kernelStepFacts.Nodes.Remove(NodeId 3)}, "Emission.Spatial.Kernels.Steps.Operation.Operands.Actual"
        | "claim" -> {kernelStepFacts with CurrentClaims = Map.empty; Obligations = []; ObligationSources = Map.empty}, "Emission.Spatial.Kernels.Obligations"
        | "operation" ->
            let op = kernelStepFacts.Emission.Numeric.Operations[NodeId 1]
            let changed = {kernel with Steps = [KernelScalarStep.Operation {op with Participants = Set.empty}]}
            {kernelStepFacts with Emission = {kernelStepFacts.Emission with Spatial = {spatial with Kernels = Map.ofList [NodeId 1, changed]}}}, "Emission.Spatial.Kernels.Steps.Operation"
        | _ ->
            let changed = {kernel with Ingress = {kernel.Ingress with Premises = Map.empty}}
            {kernelStepFacts with Emission = {kernelStepFacts.Emission with Spatial = {spatial with Kernels = Map.ofList [NodeId 1, changed]}}}, "Emission.Spatial.Kernels.Ingress.Transport"
    Assert.Contains(Integrity.check changed, fun violation -> violation.Part = part)

let private hardwareClockFacts =
    let pins : PinMapping =
        {Pins = []; Clock = {PortName = "clock"; PackagePin = "A1"; IOStandard = "LVCMOS33"; FrequencyHz = 100000000L}
         Reset = None; DevicePart = "test-device"; FieldPinAttrs = Map.empty}
    let hardware : HardwareModuleWitness =
        {Site = NodeId 1; Scope = NodeId 2; Name = "hardware"; StepBinding = NodeId 2; Implementation = NodeId 2
         Parameters = []; Result = NodeId 1; StateRepresentation = ValueRepresentation.Scalar SettledSlot.Bool
         InputRepresentation = None; ResultRepresentation = ValueRepresentation.Scalar SettledSlot.Bool
         InputPorts = []; OutputPorts = []; ResetFields = []; ClockReference = NodeId 57; ClockDeclaration = NodeId 18
         ResetDeclaration = NodeId 19; ClockPath = Set.ofList [NodeId 57; NodeId 18; NodeId 11]; Pins = pins
         MetadataOnly = Set.singleton(NodeId 9000); Participants = Set.singleton(NodeId 8000); Obligations = []}
    let spatial = {numericOperationFacts.Emission.Spatial with Hardware = Map.ofList [NodeId 1, hardware]}
    {numericOperationFacts with Emission = {numericOperationFacts.Emission with Spatial = spatial}}

[<Fact>]
let ``hardware clock reference and declaration retain their exact path without source bodies`` () =
    Assert.Empty(Integrity.check hardwareClockFacts)
    for id in [NodeId 57; NodeId 18; NodeId 11] do Assert.False(hardwareClockFacts.Nodes.ContainsKey id)

[<Theory>]
[<InlineData(true)>]
[<InlineData(false)>]
let ``hardware clock path requires both its actual reference and selected declaration`` reference =
    let hardware = hardwareClockFacts.Emission.Spatial.Hardware[NodeId 1]
    let field, id = if reference then "ClockReference", hardware.ClockReference else "ClockDeclaration", hardware.ClockDeclaration
    let spatial =
        {hardwareClockFacts.Emission.Spatial with Hardware = Map.ofList [NodeId 1, {hardware with ClockPath = hardware.ClockPath.Remove id}]}
    let changed = {hardwareClockFacts with Emission = {hardwareClockFacts.Emission with Spatial = spatial}}
    let violation = only ("Emission.Spatial.Hardware." + field) (Integrity.check changed)
    Assert.Equal(Some id, violation.Node)

[<Fact>]
let ``hardware clock provenance cannot authorize an executable numeric operand`` () =
    let operation = hardwareClockFacts.Emission.Numeric.Operations[NodeId 1]
    let operand = {operation.Operands.Head with Actual = NodeId 57; Carrier = None; Adaptation = None}
    let numeric =
        {hardwareClockFacts.Emission.Numeric with Operations = Map.ofList [NodeId 1, {operation with Operands = operand :: operation.Operands.Tail}]}
    let changed = {hardwareClockFacts with Emission = {hardwareClockFacts.Emission with Numeric = numeric}}
    Assert.Contains(Integrity.check changed, fun violation ->
        violation.Part = "Emission.Numeric.Operations.Operands.Actual" && violation.Node = Some(NodeId 57))

let private spatialDeclarationFacts hardware =
    let initial = if hardware then hardwareClockFacts else kernelStepFacts
    let root = if hardware then DeclRoot.HardwareModule else DeclRoot.KernelModule
    let shell = node 86 (SemanticKind.Binding("spatial", false, false, Some root)) [9000]
    let nodes = initial.Nodes.Add(shell.Id, shell)
    let source = (covered {initial with Nodes = nodes}).SourceReadings
    let port = source.Ports[shell.Id, OccurrencePort.StructuralChild]
    let source =
        {source with
            Ports = source.Ports.Add((shell.Id, OccurrencePort.StructuralChild), {port with Positions = Map.empty})
            Children = source.Children.Add(shell.Id, [{Ordinal = 0; Traversal = ChildTraversal.SourceOmitted(SupportKey.WholeOwningAnalysisRegion "spatial-owner", NodeId 9000)}])
            Entries = source.Entries |> List.map (fun entry -> if entry.Focus = shell.Id then {entry with Reason = SourceEntryReason.SpatialRoot} else entry)}
    let spatial = initial.Emission.Spatial
    let spatial =
        if hardware then
            let plan = spatial.Hardware[NodeId 1]
            {spatial with Hardware = Map.ofList [shell.Id, {plan with Site = shell.Id}]; Required = Set.singleton shell.Id}
        else
            let plan = spatial.Kernels[NodeId 1]
            {spatial with Kernels = Map.ofList [shell.Id, {plan with Site = shell.Id; Ingress = {plan.Ingress with Site = shell.Id}}]
                          Required = Set.singleton shell.Id}
    {initial with Nodes = nodes; SourceReadings = source; Emission = {initial.Emission with Spatial = spatial}}

[<Theory>]
[<InlineData(true)>]
[<InlineData(false)>]
let ``a specialized declaration shell uses its exact spatial plan without ordinary value facts`` hardware =
    let stated = spatialDeclarationFacts hardware
    Assert.Empty(Integrity.check stated)
    Assert.False(stated.Nodes.ContainsKey(NodeId 9000))
    Assert.False(stated.Emission.Callable.ValueShapes.ContainsKey(NodeId 86))
    Assert.False(stated.Emission.Callable.AliasTargets.ContainsKey(NodeId 86))
    Assert.False(stated.Emission.Callable.Supports.ContainsKey(NodeId 86))
    Assert.False(stated.Emission.Numeric.SourceTypes.ContainsKey(NodeId 86))
    Assert.False(stated.Emission.Numeric.OccurrenceRepresentations.ContainsKey(NodeId 86))

[<Theory>]
[<InlineData(true, true)>]
[<InlineData(true, false)>]
[<InlineData(false, true)>]
[<InlineData(false, false)>]
let ``generic value facts cannot replace a missing or mismatching specialized declaration plan`` hardware mismatch =
    let initial = spatialDeclarationFacts hardware
    let generic = (covered initial).Emission
    let stated = {initial with Emission = generic}
    let spatial = stated.Emission.Spatial
    let spatial =
        if hardware then
            {spatial with Hardware = if mismatch then Map.ofList [NodeId 86, {spatial.Hardware[NodeId 86] with Site = NodeId 1}] else Map.empty}
        else
            {spatial with Kernels = if mismatch then Map.ofList [NodeId 86, {spatial.Kernels[NodeId 86] with Site = NodeId 1}] else Map.empty}
    let changed = {stated with Emission = {stated.Emission with Spatial = spatial}}
    let part = if hardware then "Nodes (HardwareModule declaration)" else "Nodes (KernelModule declaration)"
    let violation = within part (Integrity.check changed)
    Assert.Equal(Some(NodeId 86), violation.Node)

[<Theory>]
[<InlineData(true, true)>]
[<InlineData(true, false)>]
[<InlineData(false, true)>]
[<InlineData(false, false)>]
let ``ordinary binding and other declaration roots retain ordinary mandatory value facts`` hardware otherRoot =
    let stated = spatialDeclarationFacts hardware
    let shell = stated.Nodes[NodeId 86]
    let root = if otherRoot then Some DeclRoot.EntryPoint else None
    let changed = {stated with Nodes = stated.Nodes.Add(shell.Id, {shell with Kind = SemanticKind.Binding("ordinary", false, false, root)})}
    let missing = Integrity.check changed |> List.filter (fun violation -> violation.Node = Some shell.Id && violation.Part.StartsWith("Nodes"))
    Assert.Equal(5, missing.Length)
    for table in ["Emission.Callable.ValueShapes"; "Emission.Callable.AliasTargets"; "Emission.Callable.Supports";
                  "Emission.Numeric.SourceTypes"; "Emission.Numeric.OccurrenceRepresentations"] do
        Assert.Contains(missing, fun violation -> violation.Reason.Contains table)

[<Theory>]
[<InlineData(true)>]
[<InlineData(false)>]
let ``a matching specialized declaration plan still has to satisfy its own structural facts`` hardware =
    let stated = spatialDeclarationFacts hardware
    let spatial = stated.Emission.Spatial
    let spatial =
        if hardware then
            {spatial with Hardware = Map.ofList [NodeId 86, {spatial.Hardware[NodeId 86] with ClockPath = Set.empty}]}
        else
            let plan = spatial.Kernels[NodeId 86]
            {spatial with Kernels = Map.ofList [NodeId 86, {plan with Ingress = {plan.Ingress with Site = NodeId 1}}]}
    let changed = {stated with Emission = {stated.Emission with Spatial = spatial}}
    let part = if hardware then "Emission.Spatial.Hardware.ClockReference" else "Emission.Spatial.Kernels.Ingress"
    Assert.Contains(Integrity.check changed, fun violation -> violation.Part = part)

[<Theory>]
[<InlineData(true)>]
[<InlineData(false)>]
let ``a specialized declaration does not waive actual kernel operand body or carrier requirements`` body =
    let stated = spatialDeclarationFacts false
    let changed =
        if body then {stated with Nodes = stated.Nodes.Remove(NodeId 3)}
        else {stated with Emission = {stated.Emission with Numeric = {stated.Emission.Numeric with Values = stated.Emission.Numeric.Values.Remove(NodeId 3)}}}
    let part = "Emission.Spatial.Kernels.Steps.Operation.Operands." + (if body then "Actual" else "Carrier")
    Assert.Contains(Integrity.check changed, fun violation -> violation.Part = part && violation.Node = Some(NodeId 3))

let private startupContextFacts =
    let initializer : StartupInitializerWitness = {Module = NodeId 50; Binding = NodeId 2; Initializer = NodeId 2; Ordinal = 0}
    let startup : StartupWitness =
        {EntryBinding = NodeId 2; EntryLambda = NodeId 2; SourceBinding = NodeId 2; SourceLambda = NodeId 2
         OriginalBody = NodeId 2; Spine = NodeId 2; EntryCall = NodeId 2; Symbol = "main"
         Initializers = [initializer]; ValueBindings = Set.singleton(NodeId 2)}
    {moduleUnitFacts with Emission = {moduleUnitFacts.Emission with Storage = {moduleUnitFacts.Emission.Storage with Startup = Some startup}}}

[<Fact>]
let ``startup actions retain their module context without a module body`` () =
    Assert.Empty(Integrity.check startupContextFacts)

[<Theory>]
[<InlineData("module")>]
[<InlineData("action")>]
let ``startup module and executable action roles remain distinct`` role =
    let startup = startupContextFacts.Emission.Storage.Startup.Value
    let initializer = startup.Initializers.Head
    let changed = if role = "module" then {initializer with Module = NodeId 9000} else {initializer with Initializer = NodeId 9000}
    let storage = {startupContextFacts.Emission.Storage with Startup = Some {startup with Initializers = [changed]}}
    let revision = {startupContextFacts with Emission = {startupContextFacts.Emission with Storage = storage}}
    let part = if role = "module" then "Emission.Storage.Startup.Initializers.Module" else "Emission.Storage.Startup.Initializers.Action"
    Assert.Contains(Integrity.check revision, fun violation -> violation.Part = part && violation.Node = Some(NodeId 9000))

// A source-authored instance copies a carrier whose code/signature are already
// held by their typed tables. The receiving contract is a row identity, not a
// live executable body. This fixture independently states the startup account.
let private programInstanceFacts =
    let carrier : CallableCarrier =
        { Occurrence = NodeId 2; Kind = CallableKind.OrdinaryFlatClosure; Formation = NodeId 2
          EnvironmentValue = None; Contract = Ok(NodeId 7000); Lifetime = []
          SourceType = TypeIdentity.Function(boolType, boolType); Implementation = NodeId 70
          Parameters = ["argument", boolType, NodeId 100]; ParameterShapes = [CallableValueShape.Data(NodeId 100)]
          OmittedParameters = Set.empty; Result = NodeId 101; ResultShape = CallableValueShape.Data(NodeId 101)
          Environment = None }
    let physical = ValueRepresentation.Scalar SettledSlot.Bool
    let contract : CallableContract =
        { Identity = NodeId 7000; Kind = CallableKind.OrdinaryFlatClosure; Convention = CallableConvention.Ordinary
          ParameterTypes = [boolType]; OmittedParameters = []; ParameterRepresentations = [0, physical]
          ResultType = boolType; ResultRepresentation = physical; EnvironmentBytes = None; SourcePremises = Map.empty
          Participants = [{Node = NodeId 7000; Role = ParticipantRole.CallableContract; Ordinal = 0; Group = NodeId 7000}] }
    let instance : CallableProgramInstance =
        {Carrier = carrier; Allocation = None; Participants = Set.singleton(NodeId 2)}
    let callable =
        {scopedFacts.Emission.Callable with
            Carriers = Map.ofList [NodeId 2, carrier]; Contracts = Map.ofList [NodeId 7000, contract]
            SignatureData = scopedFacts.Emission.Callable.SignatureData.Add(NodeId 2, Set.ofList [NodeId 100; NodeId 101])
            ProgramInstances = Map.ofList [NodeId 2, instance]}
    let claim =
        {scopedFacts.CurrentClaims[NodeId 404] with
            Kind = "program-initialization-order"; Body = ObligationBody.ProgramInitializationOrder(0, 1, [])}
    let order : ProgramInitializationOrderAccount =
        {Binding = NodeId 2; Claim = NodeId 404
         Participants =
             [ParticipantRole.InitializationBinding; ParticipantRole.InitializationEntry
              ParticipantRole.InitializationSpine; ParticipantRole.InitializationValue]
             |> List.map (fun role -> {Node = NodeId 2; Role = role; Ordinal = 0; Group = NodeId 2})}
    let storage =
        {scopedFacts.Emission.Storage with
            Startup = startupContextFacts.Emission.Storage.Startup
            ProgramInitializationOrders = Map.ofList [NodeId 2, order]}
    {scopedFacts with
        CurrentClaims = Map.ofList [NodeId 404, claim]; Obligations = [claim]
        ObligationSources = Map.ofList [NodeId 404, [[NodeId 2; NodeId 2; NodeId 2; NodeId 2]]]
        Emission = {scopedFacts.Emission with Callable = callable; Storage = storage}
        Codata = {scopedFacts.Codata with CallableCarriers = callable.Carriers; CallableContracts = callable.Contracts}}

let private changeInstanceCallable change revision =
    let callable = change revision.Emission.Callable
    {revision with Emission = {revision.Emission with Callable = callable}
                   Codata = {revision.Codata with CallableCarriers = callable.Carriers; CallableContracts = callable.Contracts;
                                                 MutableCallableStorage = callable.MutableStorage}}

[<Fact>]
let ``an embedded program carrier retains typed contract and signature identities without their bodies`` () =
    let held = programInstanceFacts
    for id in [NodeId 70; NodeId 100; NodeId 101; NodeId 7000] do
        Assert.False(held.Nodes.ContainsKey id)
    Assert.True(held.Emission.Callable.Contracts.ContainsKey(NodeId 7000))
    Assert.Equal(held.Emission.Callable.Carriers[NodeId 2], held.Emission.Callable.ProgramInstances[NodeId 2].Carrier)
    Assert.Contains(Integrity.named held, fun (part, ids) ->
        part = "Emission.Callable.ProgramInstances.Carrier" && List.contains (NodeId 7000) ids)
    Assert.Empty(Integrity.check held)

[<Theory>]
[<InlineData("stale contract")>]
[<InlineData("changed formation")>]
[<InlineData("missing canonical")>]
let ``an embedded program carrier must be the exact current canonical row`` mutation =
    let held = programInstanceFacts
    let changed = held |> changeInstanceCallable (fun callable ->
        let instance = callable.ProgramInstances[NodeId 2]
        match mutation with
        | "missing canonical" -> {callable with Carriers = Map.empty}
        | "stale contract" ->
            let alternate =
                {callable.Contracts[NodeId 7000] with
                    Identity = NodeId 7001
                    Participants = [{Node = NodeId 7001; Role = ParticipantRole.CallableContract; Ordinal = 0; Group = NodeId 7001}]}
            {callable with Contracts = callable.Contracts.Add(NodeId 7001, alternate)
                           ProgramInstances = callable.ProgramInstances.Add(NodeId 2, {instance with Carrier = {instance.Carrier with Contract = Ok(NodeId 7001)}})}
        | _ ->
            {callable with ProgramInstances = callable.ProgramInstances.Add(NodeId 2, {instance with Carrier = {instance.Carrier with Formation = NodeId 70}})})
    let violation = within "Emission.Callable.ProgramInstances.Carrier" (Integrity.check changed)
    Assert.Equal(Some(NodeId 2), violation.Node)
    Assert.Contains("exact callable carrier", violation.Reason)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``an embedded program carrier requires a contract row even when that identity has an executable body`` bodyPresent =
    let held = programInstanceFacts
    let identity = if bodyPresent then NodeId 2 else NodeId 7000
    Assert.Equal(bodyPresent, held.Nodes.ContainsKey identity)
    let changed = held |> changeInstanceCallable (fun callable ->
        let carrier = {callable.Carriers[NodeId 2] with Contract = Ok identity}
        let instance = {callable.ProgramInstances[NodeId 2] with Carrier = carrier}
        {callable with Contracts = Map.empty; Carriers = Map.ofList [NodeId 2, carrier]
                       ProgramInstances = Map.ofList [NodeId 2, instance]})
    let violation = within "Emission.Callable.ProgramInstances.Carrier.Contract" (Integrity.check changed)
    Assert.Equal(Some identity, violation.Node)
    Assert.Contains("Emission.Callable.Contracts", violation.Reason)

[<Fact>]
let ``matching pending canonical and embedded carriers do not authorize a program instance`` () =
    let changed = programInstanceFacts |> changeInstanceCallable (fun callable ->
        let carrier = {callable.Carriers[NodeId 2] with Contract = Error "The receiving convention is not settled."}
        let instance = {callable.ProgramInstances[NodeId 2] with Carrier = carrier}
        {callable with Contracts = Map.empty; Carriers = Map.ofList [NodeId 2, carrier]
                       ProgramInstances = Map.ofList [NodeId 2, instance]})
    Assert.Equal(changed.Emission.Callable.Carriers[NodeId 2], changed.Emission.Callable.ProgramInstances[NodeId 2].Carrier)
    let violation = within "Emission.Callable.ProgramInstances.Carrier.Contract" (Integrity.check changed)
    Assert.Equal(Some(NodeId 2), violation.Node)
    Assert.Contains("no settled receiving contract", violation.Reason)

// Mutable alternatives copy the same mixed-role carrier as program instances.
// The storage account adds no executable body for a receiving contract or signature.
let private mutableAlternativeFacts =
    programInstanceFacts |> changeInstanceCallable (fun callable ->
        let carrier = callable.Carriers[NodeId 2]
        let storage : MutableCallableStorage =
            {Binding = NodeId 2; SourceType = carrier.SourceType
             Initializer = {Site = NodeId 2; Destination = NodeId 2; Value = NodeId 2; Alternative = 0}
             Writes = []; Reads = Set.singleton(NodeId 2); Alternatives = [NodeId 2]
             AlternativeCarriers = [carrier]; EnvironmentBytes = None; Captures = Set.empty; Borrows = Set.empty}
        {callable with MutableStorage = Map.ofList [NodeId 2, storage]; ProgramInstances = Map.empty})

[<Fact>]
let ``mutable alternatives retain typed contract and signature identities without their bodies`` () =
    let held = mutableAlternativeFacts
    for id in [NodeId 70; NodeId 100; NodeId 101; NodeId 7000] do
        Assert.False(held.Nodes.ContainsKey id)
    Assert.True(held.Emission.Callable.Contracts.ContainsKey(NodeId 7000))
    let carrier = Assert.Single held.Emission.Callable.MutableStorage[NodeId 2].AlternativeCarriers
    Assert.Equal(held.Emission.Callable.Carriers[NodeId 2], carrier)
    Assert.Equal<Map<NodeId, MutableCallableStorage>>(held.Emission.Callable.MutableStorage, held.Codata.MutableCallableStorage)
    for part in ["Emission.Callable.MutableStorage.AlternativeCarriers"; "Codata.MutableCallableStorage.AlternativeCarriers"] do
        Assert.Contains(Integrity.named held, fun (name, ids) -> name = part && List.contains (NodeId 7000) ids)
    Assert.Empty(Integrity.check held)

[<Theory>]
[<InlineData("stale contract")>]
[<InlineData("changed formation")>]
[<InlineData("missing canonical")>]
let ``a mutable alternative must be the exact current canonical carrier`` mutation =
    let changed = mutableAlternativeFacts |> changeInstanceCallable (fun callable ->
        let storage = callable.MutableStorage[NodeId 2]
        let carrier = Assert.Single storage.AlternativeCarriers
        match mutation with
        | "missing canonical" -> {callable with Carriers = Map.empty}
        | "stale contract" ->
            let alternate =
                {callable.Contracts[NodeId 7000] with
                    Identity = NodeId 7001
                    Participants = [{Node = NodeId 7001; Role = ParticipantRole.CallableContract; Ordinal = 0; Group = NodeId 7001}]}
            let storage = {storage with AlternativeCarriers = [{carrier with Contract = Ok(NodeId 7001)}]}
            {callable with Contracts = callable.Contracts.Add(NodeId 7001, alternate)
                           MutableStorage = callable.MutableStorage.Add(NodeId 2, storage)}
        | _ ->
            let storage = {storage with AlternativeCarriers = [{carrier with Formation = NodeId 70}]}
            {callable with MutableStorage = callable.MutableStorage.Add(NodeId 2, storage)})
    let violation = within "Emission.Callable.MutableStorage.AlternativeCarriers" (Integrity.check changed)
    Assert.Equal(Some(NodeId 2), violation.Node)
    Assert.Contains("exact callable carrier", violation.Reason)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``a mutable alternative requires a contract row even when that identity has an executable body`` bodyPresent =
    let held = mutableAlternativeFacts
    let identity = if bodyPresent then NodeId 2 else NodeId 7000
    Assert.Equal(bodyPresent, held.Nodes.ContainsKey identity)
    let changed = held |> changeInstanceCallable (fun callable ->
        let carrier = {callable.Carriers[NodeId 2] with Contract = Ok identity}
        let storage = {callable.MutableStorage[NodeId 2] with AlternativeCarriers = [carrier]}
        {callable with Contracts = Map.empty; Carriers = Map.ofList [NodeId 2, carrier]
                       MutableStorage = Map.ofList [NodeId 2, storage]})
    let violation = within "Emission.Callable.MutableStorage.AlternativeCarriers.Contract" (Integrity.check changed)
    Assert.Equal(Some identity, violation.Node)
    Assert.Contains("Emission.Callable.Contracts", violation.Reason)

[<Fact>]
let ``matching pending canonical and alternative carriers do not authorize mutable storage`` () =
    let changed = mutableAlternativeFacts |> changeInstanceCallable (fun callable ->
        let carrier = {callable.Carriers[NodeId 2] with Contract = Error "The receiving convention is not settled."}
        let storage = {callable.MutableStorage[NodeId 2] with AlternativeCarriers = [carrier]}
        {callable with Contracts = Map.empty; Carriers = Map.ofList [NodeId 2, carrier]
                       MutableStorage = Map.ofList [NodeId 2, storage]})
    let carrier = Assert.Single changed.Emission.Callable.MutableStorage[NodeId 2].AlternativeCarriers
    Assert.Equal(changed.Emission.Callable.Carriers[NodeId 2], carrier)
    let violation = within "Emission.Callable.MutableStorage.AlternativeCarriers.Contract" (Integrity.check changed)
    Assert.Equal(Some(NodeId 2), violation.Node)
    Assert.Equal("A callable storage alternative has no settled receiving contract.", violation.Reason)

[<Fact>]
let ``an exact mutable alternative does not waive its canonical formation body`` () =
    let changed = mutableAlternativeFacts |> changeInstanceCallable (fun callable ->
        let carrier = {callable.Carriers[NodeId 2] with Formation = NodeId 9000}
        let storage = {callable.MutableStorage[NodeId 2] with AlternativeCarriers = [carrier]}
        {callable with Carriers = Map.ofList [NodeId 2, carrier]; MutableStorage = Map.ofList [NodeId 2, storage]})
    let carrier = Assert.Single changed.Emission.Callable.MutableStorage[NodeId 2].AlternativeCarriers
    Assert.Equal(changed.Emission.Callable.Carriers[NodeId 2], carrier)
    let violation = within "Emission.Callable.Carriers.Formation" (Integrity.check changed)
    Assert.Equal(Some(NodeId 9000), violation.Node)
    Assert.Equal("Node 9000 is named and is not held by the revision.", violation.Reason)

// A module-level mutable callable binding resides in one program-long cell.
// The cell restates the published storage protocol; it never replaces it.
let private callableCellFacts environment =
    let held =
        mutableAlternativeFacts |> changeInstanceCallable (fun callable ->
            {callable with MutableStorage = callable.MutableStorage.Add(NodeId 2, {callable.MutableStorage[NodeId 2] with EnvironmentBytes = environment})})
        |> fun revision -> {revision with Platform = {revision.Platform with Pointer = Ok 64}}
    let pointerBytes =
        match held.Platform.Pointer with
        | Ok bits -> bits / 8
        | Error reason -> failwith reason
    let bytes = pointerBytes + defaultArg environment 0
    let space : BAREWire.Platform.MemorySpace =
        {Name = "program"; Kind = "ram"; Capacity = 4096L; Alignment = 8; Granularity = 8; Growth = "fixed"; Access = "rw"
         Base = None; Notes = ""; MapKind = ""; Since = ""; Until = ""}
    let identity = ProgramStorageIdentity.BindingSlot(NodeId 2)
    let entry : ProgramStorageEntry =
        {Identity = identity; SourceType = held.Codata.MutableCallableStorage[NodeId 2].SourceType
         Shape = ProgramStorageShape.CallableCell environment
         Bytes = bytes; Alignment = pointerBytes; SpaceNode = NodeId 5521; Space = space
         Participants = Set.ofList [NodeId 2; NodeId 5521]}
    let reservation : BAREWire.Platform.WritableReservation =
        {Space = space; Requests = [|{Name = "binding:2"; Length = int64 bytes; Alignment = pointerBytes}|]; PayloadSize = int64 bytes}
    let storage : ProgramStorageInventory =
        {Entries = Map.ofList [identity, entry]; Reservations = Map.ofList [NodeId 5521, reservation]; Unresolved = Map.empty}
    {held with
        Codata = {held.Codata with ProgramStorage = storage; Escapes = held.Codata.Escapes.Add(NodeId 2, EscapeKind.StaticLifetime)}
        Emission = {held.Emission with Storage = {held.Emission.Storage with ProgramStorage = storage}}}

let private withProgramStorage change (revision: Revision) =
    let storage = change revision.Codata.ProgramStorage
    {revision with
        Codata = {revision.Codata with ProgramStorage = storage}
        Emission = {revision.Emission with Storage = {revision.Emission.Storage with ProgramStorage = storage}}}

[<Theory>]
[<InlineData(0)>]
[<InlineData(16)>]
let ``a program-long callable cell restates its published storage protocol and environment`` environment =
    let held = callableCellFacts (if environment = 0 then None else Some environment)
    Assert.Empty(Integrity.check held)

[<Theory>]
[<InlineData("environment", "Codata.ProgramStorage.Entries.CallableCell")>]
[<InlineData("source type", "Codata.ProgramStorage.Entries.CallableCell")>]
[<InlineData("lifetime", "Codata.ProgramStorage.Entries.CallableCell")>]
[<InlineData("no protocol", "Codata.ProgramStorage.Entries.CallableCell")>]
[<InlineData("allocation identity", "Codata.ProgramStorage.Entries.CallableCell")>]
[<InlineData("allocation twin", "Codata.ProgramStorage.Entries.CallableCell.Identity")>]
[<InlineData("extent", "Codata.ProgramStorage.Entries.CallableCell.Layout")>]
[<InlineData("alignment", "Codata.ProgramStorage.Entries.CallableCell.Layout")>]
let ``a callable cell cannot stand without its exact protocol lifetime and layout`` defect (part: string) =
    let held = callableCellFacts (Some 16)
    let identity = ProgramStorageIdentity.BindingSlot(NodeId 2)
    let entry = held.Codata.ProgramStorage.Entries[identity]
    let reshape change = held |> withProgramStorage (fun storage -> {storage with Entries = storage.Entries.Add(identity, change entry)})
    let changed =
        match defect with
        | "environment" -> reshape (fun entry -> {entry with Shape = ProgramStorageShape.CallableCell(Some 24); Bytes = entry.Bytes + 8})
        | "source type" -> reshape (fun entry -> {entry with SourceType = unitType})
        | "lifetime" -> {held with Codata = {held.Codata with Escapes = held.Codata.Escapes.Add(NodeId 2, EscapeKind.StackScoped)}}
        | "no protocol" -> held |> changeInstanceCallable (fun callable -> {callable with MutableStorage = Map.empty})
        | "allocation identity" ->
            held |> withProgramStorage (fun storage ->
                let moved = ProgramStorageIdentity.Allocation(NodeId 2)
                {storage with Entries = Map.ofList [moved, {entry with Identity = moved}]})
        | "allocation twin" ->
            held |> withProgramStorage (fun storage ->
                let twin = ProgramStorageIdentity.Allocation(NodeId 2)
                {storage with Entries = storage.Entries.Add(twin, {entry with Identity = twin; Shape = ProgramStorageShape.Bytes})})
        | "extent" -> reshape (fun entry -> {entry with Bytes = entry.Bytes - 8})
        | _ -> reshape (fun entry -> {entry with Alignment = entry.Alignment * 2})
    Assert.Contains(Integrity.check changed, fun violation -> violation.Part = part && violation.Node = Some(NodeId 2))

let private intrinsicContextFacts =
    let imported : IntrinsicWriteImport =
        {Identity = NodeId 2; Scope = NodeId 50; Symbol = "write"; Fd = BoundaryScalar.Integer(32, true)
         Count = BoundaryScalar.Integer(64, false); Result = BoundaryScalar.Integer(64, true)
         ByteRepresentation = {Name = "byte"; Capability = "native"; Family = "uint"; Bits = 8; MinMagnitude = "0"; MaxMagnitude = "255"; Boundary = "wrap"}
         Core = NodeId 4454; ReturnContract = NodeId 4476; Endpoint = NodeId 4536; Surface = NodeId 4608
         SyscallNumber = 1I; Participants = Set.ofList [NodeId 4454; NodeId 4476; NodeId 4536; NodeId 4608; NodeId 8000]}
    {moduleUnitFacts with Emission = {moduleUnitFacts.Emission with Boundary = {moduleUnitFacts.Emission.Boundary with IntrinsicWriteImports = Map.ofList [NodeId 2, imported]}}}

[<Fact>]
let ``an intrinsic import carries physical facts and declaration provenance without source bodies`` () =
    Assert.Empty(Integrity.check intrinsicContextFacts)
    for id in [4454; 4476; 4536; 4608] do Assert.False(intrinsicContextFacts.Nodes.ContainsKey(NodeId id))

[<Fact>]
let ``an intrinsic import requires its exact context header`` () =
    let imported = intrinsicContextFacts.Emission.Boundary.IntrinsicWriteImports[NodeId 2]
    let boundary = {intrinsicContextFacts.Emission.Boundary with IntrinsicWriteImports = Map.ofList [NodeId 2, {imported with Scope = NodeId 9000}]}
    let revision = {intrinsicContextFacts with Emission = {intrinsicContextFacts.Emission with Boundary = boundary}}
    let violation = within "Emission.Boundary.IntrinsicWriteImports.Scope" (Integrity.check revision)
    Assert.Equal(Some(NodeId 9000), violation.Node)

[<Fact>]
let ``a type declaration cannot be published as an executable body`` () =
    let declaration = node 1 (SemanticKind.TypeDef("Cell", TypeDefKind.RecordDef ["Value", boolType], [])) []
    let stated = revision [declaration]
    let violation = within "Nodes" (Integrity.check stated)
    Assert.Contains("type declaration", violation.Reason)

// These are structural duplicate-field controls. Real source boundary fixtures
// additionally exercise the native declaration and call-owner admission.
let private boundaryCalleeFacts =
    let declared : BoundaryDeclarationFact =
        {Form = "record"; Text = []; Numbers = []; References = []; Children = []; Parent = None; SourceType = unitType}
    let header = scopedFacts.SourceReadings.ContextHeaders[NodeId 50]
    let source =
        {numericOperationFacts.SourceReadings with
            ContextHeaders = Map.ofList [NodeId 50, header]
            Contexts = numericOperationFacts.SourceReadings.Contexts.Add(NodeId 50, [[]])
            Ports = numericOperationFacts.SourceReadings.Ports.Add((NodeId 50, OccurrencePort.ModuleDeclaration), header.Ports[OccurrencePort.ModuleDeclaration])}
    let imported : BoundaryImport =
        {Identity = NodeId 72; Binding = NodeId 2; Scope = NodeId 50; Library = "c"; Symbol = "add"; CallingConvention = "CDecl"
         DeclarationPath = [NodeId 2]; Parameters = [NodeId 3, BoundaryScalar.Integer(32, true); NodeId 4, BoundaryScalar.Integer(32, true)]
         Result = Some(BoundaryScalar.Integer(32, true)); Participants = Set.singleton(NodeId 8000)
         SourceTypes = [1;3;4] |> List.map(fun id -> NodeId id, numericOperationFacts.Nodes[NodeId id].Type) |> Map.ofList
         DeclarationFacts = Map.ofList [NodeId 72, declared]}
    let call : BoundaryCall =
        {Site = NodeId 1; Import = NodeId 72; Callee = NodeId 2; Entry = None; Resource = None
         Arguments = [3;4] |> List.map(fun id -> {Actual = NodeId id; Formal = NodeId id; Abi = BoundaryScalar.Integer(32, true); Adaptation = None; OptionalEntry = None; BufferAbsence = None})
         ErasedUnitArguments = []; Result = Some(BoundaryScalar.Integer(32, true)); ResultAdaptation = None; Participants = Set.singleton(NodeId 8000); SourceTypes = imported.SourceTypes}
    let callable =
        {numericOperationFacts.Emission.Callable with
            ValueShapes = numericOperationFacts.Emission.Callable.ValueShapes.Add(NodeId 72, CallableValueShape.Data(NodeId 72))
            AliasTargets = numericOperationFacts.Emission.Callable.AliasTargets.Add(NodeId 72, NodeId 72)
            ClosedData = Set.singleton(NodeId 72)
            Supports = numericOperationFacts.Emission.Callable.Supports.Add(NodeId 72, Set.singleton(NodeId 8000))}
    let numeric =
        {numericOperationFacts.Emission.Numeric with
            SourceTypes = numericOperationFacts.Emission.Numeric.SourceTypes.Add(NodeId 72, unitType)
            OccurrenceRepresentations = numericOperationFacts.Emission.Numeric.OccurrenceRepresentations.Add(NodeId 72, Ok(ValueRepresentation.Scalar SettledSlot.Unit))}
    let boundary = {numericOperationFacts.Emission.Boundary with Imports = Map.ofList [NodeId 72, imported]; Calls = Map.ofList [NodeId 1, call]}
    {numericOperationFacts with SourceReadings = source; Emission = {numericOperationFacts.Emission with Callable = callable; Numeric = numeric; Boundary = boundary}}

[<Fact>]
let ``a boundary call retains its live callee occurrence separately from its declaration identity`` () =
    Assert.Empty(Integrity.check boundaryCalleeFacts)
    Assert.NotEqual(boundaryCalleeFacts.Emission.Boundary.Calls[NodeId 1].Callee, boundaryCalleeFacts.Emission.Boundary.Imports[NodeId 72].Identity)
    Assert.False(boundaryCalleeFacts.Nodes.ContainsKey(NodeId 72))

[<Theory>]
[<InlineData("reverse")>]
[<InlineData("repeat")>]
[<InlineData("drop")>]
[<InlineData("erased")>]
let ``a direct boundary call preserves the original ordered source argument occurrences`` change =
    Assert.Empty(Integrity.check boundaryCalleeFacts)
    let call = boundaryCalleeFacts.Emission.Boundary.Calls[NodeId 1]
    let changed =
        match change with
        | "reverse" -> {call with Arguments = List.rev call.Arguments}
        | "repeat" -> {call with Arguments = [call.Arguments.Head; call.Arguments.Head]}
        | "drop" -> {call with Arguments = [call.Arguments.Head]}
        | _ -> {call with ErasedUnitArguments = [NodeId 3]}
    let boundary = {boundaryCalleeFacts.Emission.Boundary with Calls = Map.ofList [call.Site, changed]}
    let violations = Integrity.check {boundaryCalleeFacts with Emission = {boundaryCalleeFacts.Emission with Boundary = boundary}}
    let violation = within "Emission.Boundary.Calls.Callee" violations
    Assert.Contains("live source application", violation.Reason)

[<Fact>]
let ``an ordinary scalar operand cannot acquire an optional entry account`` () =
    Assert.Empty(Integrity.check boundaryCalleeFacts)
    let call = boundaryCalleeFacts.Emission.Boundary.Calls[NodeId 1]
    let optional : BoundaryOptionalEntry =
        {Construction = NodeId 3; CaseOrdinal = 0; Payload = None; Formation = None
         Transport = Set.singleton(NodeId 3)
         Obligation = NodeId 404}
    let changed = {call with Arguments = {call.Arguments.Head with OptionalEntry = Some (BoundaryOptionalEntryChoice.Direct optional)} :: call.Arguments.Tail}
    let boundary = {boundaryCalleeFacts.Emission.Boundary with Calls = Map.ofList [call.Site, changed]}
    let violations = Integrity.check {boundaryCalleeFacts with Emission = {boundaryCalleeFacts.Emission with Boundary = boundary}}
    let violation = within "Emission.Boundary.Calls.OptionalEntry" violations
    Assert.Equal("An optional-entry account requires its original Entry formal.", violation.Reason)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``optional entry inventory retains absent and present selection identities`` present =
    let call = boundaryCalleeFacts.Emission.Boundary.Calls[NodeId 1]
    let optional : BoundaryOptionalEntry =
        {Construction = NodeId 9101; CaseOrdinal = if present then 1 else 0
         Payload = if present then Some(NodeId 9102) else None
         Formation = if present then Some(NodeId 9103) else None
         Transport = Set.singleton(NodeId 9104)
         Obligation = NodeId 9106}
    let changed = {call with Arguments = [{call.Arguments.Head with OptionalEntry = Some (BoundaryOptionalEntryChoice.Direct optional)}]}
    let boundary = {boundaryCalleeFacts.Emission.Boundary with Calls = Map.ofList [call.Site, changed]}
    let named = Integrity.named {boundaryCalleeFacts with Emission = {boundaryCalleeFacts.Emission with Boundary = boundary}}
                |> List.collect snd |> Set.ofList
    for identity in [9101; 9104; 9106] @ (if present then [9102; 9103] else []) do
        Assert.Contains(NodeId identity, named)

[<Fact>]
let ``conditional optional entry inventory retains selection and option tag projection identities`` () =
    let call = boundaryCalleeFacts.Emission.Boundary.Calls[NodeId 1]
    let whenTrue : BoundaryOptionalEntry =
        {Construction = NodeId 9101; CaseOrdinal = 1; Payload = Some(NodeId 9102); Formation = Some(NodeId 9103)
         Transport = Set.singleton(NodeId 9104); Obligation = NodeId 9106}
    let whenFalse : BoundaryOptionalEntry =
        {Construction = NodeId 9107; CaseOrdinal = 0; Payload = None; Formation = None
         Transport = Set.singleton(NodeId 9108); Obligation = NodeId 9109}
    let choice = BoundaryOptionalEntryChoice.Conditional(NodeId 9100, NodeId 9105, whenTrue, whenFalse)
    let changed = {call with Arguments = [{call.Arguments.Head with OptionalEntry = Some choice}]}
    let boundary = {boundaryCalleeFacts.Emission.Boundary with Calls = Map.ofList [call.Site, changed]}
    let named = Integrity.named {boundaryCalleeFacts with Emission = {boundaryCalleeFacts.Emission with Boundary = boundary}}
                |> List.collect snd |> Set.ofList
    for identity in [9100; 9101; 9102; 9103; 9104; 9105; 9106; 9107; 9108; 9109] do
        Assert.Contains(NodeId identity, named)

[<Theory>]
[<InlineData("valid")>]
[<InlineData("missing-projection-node")>]
[<InlineData("wrong-projection-target")>]
[<InlineData("missing-call-child")>]
[<InlineData("missing-call-participant")>]
[<InlineData("missing-numeric-carrier")>]
let ``conditional optional entry requires its exact DUGetTag option tag projection`` defect =
    let call = boundaryCalleeFacts.Emission.Boundary.Calls[NodeId 1]
    let whenTrue : BoundaryOptionalEntry =
        {Construction = NodeId 3; CaseOrdinal = 1; Payload = Some(NodeId 3); Formation = Some(NodeId 3)
         Transport = Set.ofList [NodeId 3]; Obligation = NodeId 404}
    let whenFalse : BoundaryOptionalEntry =
        {Construction = NodeId 4; CaseOrdinal = 0; Payload = None; Formation = None
         Transport = Set.ofList [NodeId 4; NodeId 3]; Obligation = NodeId 405}
    let held : CallableAggregateSelection = { Condition = NodeId 2; WhenTrue = NodeId 3; WhenFalse = NodeId 4 }
    let selected : CallableAggregateValue =
        { Occurrence = NodeId 3; Aggregate = NodeId 3; Slot = NodeId 101; Alternatives = []; Selector = None
          FormationInputs = [NodeId 2; NodeId 3; NodeId 4]; Value = None; SelectedAlternative = None
          Operation = CallableAggregateOperation.Select; Frontier = None; Tag = None; Selection = Some held
          ResultRetirement = None; Bytes = 0; Alignment = 1; Participants = [] }
    let condition = boundaryCalleeFacts.Nodes[NodeId 2]
    let account : CallableAggregateDependencyAccount =
        { Occurrence = NodeId 3; Slots = []; Values = [selected]
          Sources = [{ Node = NodeId 2; Kind = condition.Kind; Type = condition.Type; Children = condition.Children; Anchors = [] }]
          Carriers = []; Contracts = []; Flows = []; Joins = []; Claims = []; Symbols = []; Inactivity = []
          MemoryPolicy = None; Participants = [] }
    let callable =
        { boundaryCalleeFacts.Emission.Callable with
            AggregateValues = Map.ofList [NodeId 3, [selected]]
            AggregateDependencies = Map.ofList [NodeId 3, account] }
    let tagId = NodeId 99
    let intType =
        TypeIdentity.Application(
            { Declaration = { Module = []; Name = "int" }
              Parameters = []
              NativeKind = Some(NTUKind.NTUint(NTUWidth.Resolved WidthDimension.Register)) },
            [])
    let actualType = boundaryCalleeFacts.Nodes[NodeId 3].Type
    let tagNode =
        { node 99 (SemanticKind.DUGetTag( (if defect = "wrong-projection-target" then NodeId 4 else NodeId 3), actualType )) [3] with
            Type = intType; ValueRange = Some(ValueRange.Bounded(0I, 1I)) }
    let callNode =
        let baseCall = boundaryCalleeFacts.Nodes[NodeId 1]
        if defect = "missing-call-child" then baseCall
        else { baseCall with Children = baseCall.Children @ [tagId] }
    let nodes =
        let withCall = boundaryCalleeFacts.Nodes.Add(NodeId 1, callNode)
        if defect = "missing-projection-node" then withCall else withCall.Add(tagId, tagNode)
    let tagCarrier : ScalarCarrier =
        { Site = tagId; SourceType = intType; Representation = boundaryCalleeFacts.Emission.Numeric.Values[NodeId 3].Representation
          Declaration = Some(NodeId 64); Slot = SettledSlot.Integer(64, Some "int"); Range = ValueRange.Bounded(0I, 1I)
          Participants = Set.ofList [tagId; NodeId 3]; Obligations = [] }
    let numeric =
        if defect = "missing-numeric-carrier" then boundaryCalleeFacts.Emission.Numeric
        else { boundaryCalleeFacts.Emission.Numeric with Values = boundaryCalleeFacts.Emission.Numeric.Values.Add(tagId, tagCarrier) }
    let choice = BoundaryOptionalEntryChoice.Conditional(NodeId 3, tagId, whenTrue, whenFalse)
    let operand = { call.Arguments.Head with Abi = BoundaryScalar.Entry(NodeId 72); OptionalEntry = Some choice }
    let participants = if defect = "missing-call-participant" then call.Participants else call.Participants.Add tagId
    let changedCall = { call with Arguments = operand :: call.Arguments.Tail; Participants = participants }
    let boundary = { boundaryCalleeFacts.Emission.Boundary with Calls = Map.ofList [call.Site, changedCall] }
    let stated = { boundaryCalleeFacts with Nodes = nodes; Emission = { boundaryCalleeFacts.Emission with Callable = callable; Numeric = numeric; Boundary = boundary } }
    let violations = Integrity.check stated
    if defect = "valid" then
        Assert.DoesNotContain(violations, fun v -> v.Part = "Emission.Boundary.Calls.OptionalEntry" && v.Reason.Contains("option-tag projection"))
    else
        Assert.Contains(violations, fun v -> v.Part = "Emission.Boundary.Calls.OptionalEntry" && v.Node = Some(NodeId 1) && v.Reason.Contains("option-tag projection"))

[<Theory>]
[<InlineData("empty")>]
[<InlineData("blank")>]
[<InlineData("whitespace")>]
[<InlineData("logic")>]
let ``Pending claims retain explicit reasons and cannot advertise solver logic`` change =
    let original = scopedFacts.CurrentClaims[NodeId 404]
    let reasons =
        match change with
        | "empty" -> []
        | "blank" -> [""]
        | "whitespace" -> [" "]
        | _ -> ["Selected-target optional-entry conversion remains Pending."]
    let claim = {original with Body = ObligationBody.Pending reasons; Logic = if change = "logic" then "QF_LIA" else ""}
    let changed = {scopedFacts with CurrentClaims = Map.ofList [NodeId 404, claim]; Obligations = [claim]}
    let violation = within "CurrentClaims.Pending" (Integrity.check changed)
    Assert.Equal("A Pending claim requires nonempty reason strings and no solver logic.", violation.Reason)

[<Fact>]
let ``a reasoned Pending claim cannot be detached from its current optional operand`` () =
    let claim =
        {scopedFacts.CurrentClaims[NodeId 404] with
            Kind = "foreign-optional-entry-conversion-0"; Logic = ""
            Body = ObligationBody.Pending ["Selected-target optional-entry conversion remains Pending."]}
    let changed = {scopedFacts with CurrentClaims = Map.ofList [NodeId 404, claim]; Obligations = [claim]}
    let violations = Integrity.check changed
    Assert.DoesNotContain(violations, fun violation -> violation.Part = "CurrentClaims.Pending")
    let violation = within "CurrentClaims.Pending.Owner" violations
    Assert.Equal("A Pending claim requires exactly one current optional-entry operand account.", violation.Reason)

[<Theory>]
[<InlineData("callee")>]
[<InlineData("declaration-type")>]
let ``a boundary declaration or current claim cannot substitute for an actual callee or conflicting type fact`` defect =
    let changed, part =
        if defect = "callee" then
            let call = boundaryCalleeFacts.Emission.Boundary.Calls[NodeId 1]
            let boundary = {boundaryCalleeFacts.Emission.Boundary with Calls = Map.ofList [NodeId 1, {call with Callee = NodeId 72}]}
            {boundaryCalleeFacts with Emission = {boundaryCalleeFacts.Emission with Boundary = boundary}}, "Emission.Boundary.Calls.Callee"
        else
            let numeric = {boundaryCalleeFacts.Emission.Numeric with SourceTypes = boundaryCalleeFacts.Emission.Numeric.SourceTypes.Add(NodeId 72, boolType)}
            {boundaryCalleeFacts with Emission = {boundaryCalleeFacts.Emission with Numeric = numeric}}, "Emission.Numeric.SourceTypes"
    Assert.Contains(Integrity.check changed, fun violation -> violation.Part = part && violation.Node = Some(NodeId 72))

let private referencedDataFacts =
    let target = NodeId 72
    let callable =
        {numericOperationFacts.Emission.Callable with
            ValueShapes = numericOperationFacts.Emission.Callable.ValueShapes.Add(NodeId 3, CallableValueShape.Data target).Add(target, CallableValueShape.Data target)
            AliasTargets = numericOperationFacts.Emission.Callable.AliasTargets.Add(NodeId 3, target).Add(target, target)
            ClosedData = Set.singleton target
            Supports = numericOperationFacts.Emission.Callable.Supports.Add(target, Set.singleton(NodeId 8000))}
    let numeric =
        {numericOperationFacts.Emission.Numeric with
            SourceTypes = numericOperationFacts.Emission.Numeric.SourceTypes.Add(target, numericOperationFacts.Emission.Numeric.SourceTypes[NodeId 3])
            OccurrenceRepresentations = numericOperationFacts.Emission.Numeric.OccurrenceRepresentations.Add(target, numericOperationFacts.Emission.Numeric.OccurrenceRepresentations[NodeId 3])}
    {numericOperationFacts with Emission = {numericOperationFacts.Emission with Callable = callable; Numeric = numeric}}

[<Fact>]
let ``a retained data reading has its exact canonical typed target without the target body`` () =
    Assert.Empty(Integrity.check referencedDataFacts)
    Assert.False(referencedDataFacts.Nodes.ContainsKey(NodeId 72))

[<Theory>]
[<InlineData("shape")>]
[<InlineData("alias")>]
[<InlineData("closed")>]
[<InlineData("type")>]
[<InlineData("representation")>]
[<InlineData("unresolved-representation")>]
[<InlineData("reference")>]
let ``data target metadata requires all current typed rows and an actual retained reference`` missing =
    let target = NodeId 72
    let callable = referencedDataFacts.Emission.Callable
    let numeric = referencedDataFacts.Emission.Numeric
    let changedCallable, changedNumeric =
        match missing with
        | "shape" -> {callable with ValueShapes = callable.ValueShapes.Add(target, CallableValueShape.Data(NodeId 8000))}, numeric
        | "alias" -> {callable with AliasTargets = callable.AliasTargets.Add(target, NodeId 8000)}, numeric
        | "closed" -> {callable with ClosedData = Set.empty}, numeric
        | "type" -> callable, {numeric with SourceTypes = numeric.SourceTypes.Remove target}
        | "representation" -> callable, {numeric with OccurrenceRepresentations = numeric.OccurrenceRepresentations.Remove target}
        | "unresolved-representation" -> callable, {numeric with OccurrenceRepresentations = numeric.OccurrenceRepresentations.Add(target, Error "not settled")}
        | _ -> {callable with ValueShapes = callable.ValueShapes.Add(NodeId 3, CallableValueShape.Data(NodeId 3)); AliasTargets = callable.AliasTargets.Add(NodeId 3, NodeId 3)}, numeric
    let changed = {referencedDataFacts with Emission = {referencedDataFacts.Emission with Callable = changedCallable; Numeric = changedNumeric}}
    Assert.Contains(Integrity.check changed, fun violation -> violation.Node = Some target)

[<Fact>]
let ``typed data metadata cannot substitute for an executable numeric operand`` () =
    let operation = referencedDataFacts.Emission.Numeric.Operations[NodeId 1]
    let changed = {operation with Operands = operation.Operands |> List.map(fun operand -> if operand.Actual = NodeId 3 then {operand with Actual = NodeId 72; Carrier = None; Adaptation = None} else operand)}
    let violations = Integrity.check (withNumericOperation changed referencedDataFacts)
    Assert.Contains(violations, fun violation -> violation.Part = "Emission.Numeric.Operations.Operands.Actual" && violation.Node = Some(NodeId 72))

// Typed MMIO positions retain their source role after generated name enumeration.
let private mmioRoleFacts =
    let held =
        revision [node 1 (SemanticKind.TupleExpr [NodeId 9; NodeId 2]) [9; 2]
                  node 2 (SemanticKind.Literal(NativeLiteral.Bool true)) []
                  node 3 (SemanticKind.TupleExpr [NodeId 10]) [10]]
    let omit parent ordinal identity (source: WitnessSourceReadings) =
        let children = source.Children[NodeId parent] |> List.map (fun child ->
            if child.Ordinal = ordinal then
                {child with Traversal = ChildTraversal.SourceOmitted(SupportKey.WholeOwningAnalysisRegion "mmio-fixture", NodeId identity)}
            else child)
        let key = NodeId parent, OccurrencePort.StructuralChild
        let port = source.Ports[key]
        {source with Children = source.Children.Add(NodeId parent, children)
                     Ports = source.Ports.Add(key, {port with Positions = port.Positions.Remove ordinal})}
    let source = held.SourceReadings |> omit 1 0 9 |> omit 3 0 10
    let binding : MmioBindingEvidence =
        {Plan = "plan"; Grant = "grant"; Register = "reg"; Region = "region"
         Mapping = "mapping"; AddressSpace = "space"; DeclarationNodes = [NodeId 90]
         Predicates = []; Premises = ["producer declaration account"]}
    let access : MmioAccessEvidence = {Operation = "bind32"; Address = 4096I; Bits = 32; Binding = Some binding}
    let operation : MmioOperation = {Site = NodeId 1; Operation = "bind32"; Arguments = [NodeId 9; NodeId 2]}
    {held with SourceReadings = source
               Codata = {held.Codata with Mmio = Map.ofList [NodeId 1, access]}
               Foreign = {held.Foreign with Mmio = Map.ofList [NodeId 1, operation]}}

let private mmioMissing part id violations =
    let violation = within part violations
    Assert.Equal(Some(NodeId id), violation.Node)
    Assert.Equal(sprintf "Node %d is named and is not held by the revision." id, violation.Reason)

[<Fact>]
let ``MMIO roles retain body-free declarations own-site omissions and live arguments`` () =
    Assert.Empty(Integrity.check mmioRoleFacts)
    Assert.False(mmioRoleFacts.Nodes.ContainsKey(NodeId 90))
    Assert.False(mmioRoleFacts.Nodes.ContainsKey(NodeId 9))
    Assert.True(mmioRoleFacts.Nodes.ContainsKey(NodeId 2))
    Assert.Equal<NodeId list>([NodeId 90], mmioRoleFacts.Codata.Mmio[NodeId 1].Binding.Value.DeclarationNodes)

[<Theory>]
[<InlineData("declaration")>]
[<InlineData("expression")>]
[<InlineData("dependency")>]
let ``MMIO predicate positions cannot borrow declaration provenance`` position =
    let predicate : PredicateEvidence =
        {Name = "condition"; Declaration = (if position = "declaration" then NodeId 90 else NodeId 2)
         Expression = (if position = "expression" then NodeId 90 else NodeId 2)
         Dependencies = [if position = "dependency" then NodeId 90 else NodeId 2]
         Status = Established; Message = "source checked"; Source = "fixture"}
    let access = mmioRoleFacts.Codata.Mmio[NodeId 1]
    let changed = {access with Binding = Some {access.Binding.Value with Predicates = [predicate]}}
    let stated = {mmioRoleFacts with Codata = {mmioRoleFacts.Codata with Mmio = Map.ofList [NodeId 1, changed]}}
    Integrity.check stated |> mmioMissing "Codata.Mmio.Binding" 90

[<Fact>]
let ``MMIO held predicate positions remain admissible`` () =
    let predicate : PredicateEvidence =
        {Name = "condition"; Declaration = NodeId 2; Expression = NodeId 2; Dependencies = [NodeId 2]
         Status = Established; Message = "source checked"; Source = "fixture"}
    let access = mmioRoleFacts.Codata.Mmio[NodeId 1]
    let changed = {access with Binding = Some {access.Binding.Value with Predicates = [predicate]}}
    Assert.Empty(Integrity.check {mmioRoleFacts with Codata = {mmioRoleFacts.Codata with Mmio = Map.ofList [NodeId 1, changed]}})

[<Theory>]
[<InlineData(10)>]
[<InlineData(91)>]
let ``MMIO arguments require their own site and exact omitted identity`` missing =
    let operation = {mmioRoleFacts.Foreign.Mmio[NodeId 1] with Arguments = [NodeId missing; NodeId 2]}
    let stated = {mmioRoleFacts with Foreign = {mmioRoleFacts.Foreign with Mmio = Map.ofList [NodeId 1, operation]}}
    let violations = Integrity.check stated
    Assert.DoesNotContain(violations, fun violation -> violation.Part = "SourceReadings.Children")
    violations |> mmioMissing "Foreign.Mmio.Arguments" missing

[<Fact>]
let ``MMIO live argument still requires its executable body`` () =
    let stated = {mmioRoleFacts with Nodes = mmioRoleFacts.Nodes.Remove(NodeId 2)}
    Integrity.check stated |> mmioMissing "Foreign.Mmio.Arguments" 2

[<Fact>]
let ``MMIO omitted argument retains the existing nonempty support refusal`` () =
    let children = mmioRoleFacts.SourceReadings.Children[NodeId 1] |> List.map (fun child ->
        if child.Ordinal = 0 then
            {child with Traversal = ChildTraversal.SourceOmitted(SupportKey.WholeOwningAnalysisRegion "", NodeId 9)}
        else child)
    let source = {mmioRoleFacts.SourceReadings with Children = mmioRoleFacts.SourceReadings.Children.Add(NodeId 1, children)}
    let violation = Integrity.check {mmioRoleFacts with SourceReadings = source} |> within "SourceReadings.Children"
    Assert.Equal(Some(NodeId 1), violation.Node)
    Assert.Equal("An omitted child has an empty source support identity.", violation.Reason)

[<Fact>]
let ``MMIO stored operation site must equal its held map key`` () =
    let operation = {mmioRoleFacts.Foreign.Mmio[NodeId 1] with Site = NodeId 3}
    let stated = {mmioRoleFacts with Foreign = {mmioRoleFacts.Foreign with Mmio = Map.ofList [NodeId 1, operation]}}
    let violation = Integrity.check stated |> only "Foreign.Mmio.Site"
    Assert.Equal(Some(NodeId 1), violation.Node)
    Assert.Equal("The MMIO operation is filed under a different site identity.", violation.Reason)

let private separatedWitnessRegionsFixture : Revision =
    let literal id parent =
        { node id (SemanticKind.Literal(NativeLiteral.Bool true)) [] with Parent = Some(NodeId parent); Type = boolType }
    let binding id name child =
        { node id (SemanticKind.Binding(name, false, false, None)) [child] with Type = boolType }
    let baseRevision =
        revision [
            binding 1 "localFn" 2; literal 2 1
            binding 3 "sharedFn" 4; literal 4 3
            binding 5 "globalFn" 6; literal 6 5
            binding 7 "commonTop" 8; literal 8 7 ]
    let localParticipant : ProofSupportParticipant =
        { Address = "module:App/binding:localFn/0"; Role = ParticipantRole.Site; Ordinal = 0; Group = "module:App/binding:localFn/0" }
    let sharedParticipant : ProofSupportParticipant =
        { Address = "module:App/binding:sharedFn/0"; Role = ParticipantRole.Callee; Ordinal = 0; Group = "module:App/binding:localFn/0" }
    let globalParticipant : ProofSupportParticipant =
        { Address = "module:App/binding:globalFn/0"; Role = ParticipantRole.RepresentationDeclaration; Ordinal = 0; Group = "module:App/binding:globalFn/0" }
    let censuses : ProofSupportCensus list =
        [ { Identity = "numericInterface:int32-comparison"; Kind = ProofSupportCensusKind.NumericInterface; Entries = Set.ofList ["Alloy.Core.Int32.compare"; "Alloy.Core.Int32.zero"] }
          { Identity = "platform:register-layout"; Kind = ProofSupportCensusKind.PlatformLayout; Entries = Set.singleton "x86_64:lp64" }
          { Identity = "platform:default-space"; Kind = ProofSupportCensusKind.PlatformSpace; Entries = Set.singleton "address-space:0" }
          { Identity = "boundary:callback-absence"; Kind = ProofSupportCensusKind.BoundaryAbsence; Entries = Set.singleton "Foreign.none" }
          { Identity = "domain:uniqueness"; Kind = ProofSupportCensusKind.DomainUniqueness; Entries = Set.singleton "module:App" } ]
    let claimInfo : ObligationInfo =
        { Id = "local-claim"; Kind = "range"; Logic = "QF_LIA"; Statement = "local range"; Source = "fixture"; Refs = []
          Body = ObligationBody.IntegerLiteralRange(1I, 0I, 2I) }
    let localRegion : WitnessRegion =
        { Identity = "callable:App:localFn"; Flavor = WitnessRegionKind.ScalarCallable
          Root = Some(NodeId 1); Anchor = Some(NodeId 1); Path = []
          Members = Set.ofList [NodeId 1; NodeId 2]; Supports = Set.ofList [NodeId 1; NodeId 2]
          OwnerSupport = SupportKey.WholeOwningAnalysisRegion "owner:localFn"
          CallableInterfaceDigest = CallableInterfaceDigest "callable-interface:localFn-sig-v1"
          SemanticRealizationDigest = SemanticRealizationDigest "semantic-realization:localFn-body-v1"
          CanonicalProofSupportDigest = CanonicalProofSupportDigest "proof-support:localFn-obligations-v1"
          ProofSupportCoverage = ProofSupportCoverage.Local([localParticipant], [])
          Dependencies = Set.empty }
    let sharedRegion : WitnessRegion =
        { Identity = "callable:App:sharedFn"; Flavor = WitnessRegionKind.ScalarCallable
          Root = Some(NodeId 3); Anchor = Some(NodeId 3); Path = []
          Members = Set.ofList [NodeId 3; NodeId 4]; Supports = Set.ofList [NodeId 1; NodeId 2; NodeId 3; NodeId 4]
          OwnerSupport = SupportKey.WholeOwningAnalysisRegion "owner:sharedFn"
          CallableInterfaceDigest = CallableInterfaceDigest "callable-interface:sharedFn-sig-v1"
          SemanticRealizationDigest = SemanticRealizationDigest "semantic-realization:sharedFn-body-v1"
          CanonicalProofSupportDigest = CanonicalProofSupportDigest "proof-support:sharedFn-obligations-v1"
          ProofSupportCoverage = ProofSupportCoverage.Shared(Set.ofList ["callable:App:localFn"; "callable:App:sharedFn"], [sharedParticipant], [])
          Dependencies = Set.singleton "callable:App:localFn" }
    let globalRegion : WitnessRegion =
        { Identity = "callable:App:globalFn"; Flavor = WitnessRegionKind.ScalarCallable
          Root = Some(NodeId 5); Anchor = Some(NodeId 5); Path = []
          Members = Set.ofList [NodeId 5; NodeId 6]; Supports = Set.ofList [NodeId 5; NodeId 6]
          OwnerSupport = SupportKey.WholeOwningAnalysisRegion "owner:globalFn"
          CallableInterfaceDigest = CallableInterfaceDigest "callable-interface:globalFn-sig-v1"
          SemanticRealizationDigest = SemanticRealizationDigest "semantic-realization:globalFn-body-v1"
          CanonicalProofSupportDigest = CanonicalProofSupportDigest "proof-support:globalFn-obligations-v1"
          ProofSupportCoverage = ProofSupportCoverage.Global([globalParticipant], censuses)
          Dependencies = Set.empty }
    let commonRegion : WitnessRegion =
        { Identity = "common"; Flavor = WitnessRegionKind.Common
          Root = None; Anchor = None; Path = []
          Members = Set.ofList [NodeId 7; NodeId 8]; Supports = Set.ofList [NodeId 1; NodeId 2; NodeId 3; NodeId 4; NodeId 5; NodeId 6; NodeId 7; NodeId 8]
          OwnerSupport = SupportKey.WholeOwningAnalysisRegion "owner:whole-revision"
          CallableInterfaceDigest = CallableInterfaceDigest "callable-interface:common-envelope-ci-v1"
          SemanticRealizationDigest = SemanticRealizationDigest "semantic-realization:common-envelope-sr-v1"
          CanonicalProofSupportDigest = CanonicalProofSupportDigest "proof-support:common-envelope-ps-v1"
          ProofSupportCoverage = ProofSupportCoverage.Unclassified("common-whole-revision-envelope", Set.ofList ["owner:whole-revision"; "module:App"])
          Dependencies = Set.ofList ["callable:App:localFn"; "callable:App:sharedFn"; "callable:App:globalFn"] }
    { baseRevision with
        CurrentClaims = Map.ofList [NodeId 2, claimInfo]
        Obligations = [claimInfo]
        ObligationSources = Map.ofList [NodeId 2, [[NodeId 1; NodeId 2]]]
        Codata = { baseRevision.Codata with WitnessSegmentation = Some { Version = 1; Regions = [localRegion; sharedRegion; globalRegion; commonRegion] } } }

let private updateRegion identity (change: WitnessRegion -> WitnessRegion) (stated: Revision) : Revision =
    let segmentation = stated.Codata.WitnessSegmentation.Value
    let updated = segmentation.Regions |> List.map (fun region -> if region.Identity = identity then change region else region)
    { stated with Codata = { stated.Codata with WitnessSegmentation = Some { segmentation with Regions = updated } } }

[<Fact>]
let ``witness segmentation accepts separated digests across scalar callable and common coverage scopes`` () =
    Assert.Empty(Integrity.check separatedWitnessRegionsFixture)

[<Theory>]
[<InlineData("callable", "")>]
[<InlineData("callable", "   ")>]
[<InlineData("callable", "callable-interface:")>]
[<InlineData("callable", "callable-interface:   ")>]
[<InlineData("realization", "")>]
[<InlineData("realization", "   ")>]
[<InlineData("realization", "semantic-realization:")>]
[<InlineData("proof", "")>]
[<InlineData("proof", "   ")>]
[<InlineData("proof", "proof-support:")>]
let ``witness region refuses missing empty or whitespace digests`` slot raw =
    let part, changed =
        match slot with
        | "callable" ->
            "Codata.WitnessSegmentation.Regions.CallableInterfaceDigest",
            updateRegion "callable:App:localFn" (fun r -> { r with CallableInterfaceDigest = CallableInterfaceDigest raw }) separatedWitnessRegionsFixture
        | "realization" ->
            "Codata.WitnessSegmentation.Regions.SemanticRealizationDigest",
            updateRegion "callable:App:localFn" (fun r -> { r with SemanticRealizationDigest = SemanticRealizationDigest raw }) separatedWitnessRegionsFixture
        | _ ->
            "Codata.WitnessSegmentation.Regions.CanonicalProofSupportDigest",
            updateRegion "callable:App:localFn" (fun r -> { r with CanonicalProofSupportDigest = CanonicalProofSupportDigest raw }) separatedWitnessRegionsFixture
    let violation = only part (Integrity.check changed)
    Assert.Equal(Some(NodeId 1), violation.Node)
    Assert.Contains("[WSEG-002]", violation.Reason)

[<Theory>]
[<InlineData("callable", "semantic-realization:localFn-body-v1", "SemanticRealizationDigest")>]
[<InlineData("callable", "proof-support:localFn-obligations-v1", "CanonicalProofSupportDigest")>]
[<InlineData("realization", "callable-interface:localFn-sig-v1", "CallableInterfaceDigest")>]
[<InlineData("realization", "proof-support:localFn-obligations-v1", "CanonicalProofSupportDigest")>]
[<InlineData("proof", "callable-interface:localFn-sig-v1", "CallableInterfaceDigest")>]
[<InlineData("proof", "semantic-realization:localFn-body-v1", "SemanticRealizationDigest")>]
let ``witness region refuses cross digest domain substitution`` slot substituted foreignName =
    let part, changed =
        match slot with
        | "callable" ->
            "Codata.WitnessSegmentation.Regions.CallableInterfaceDigest",
            updateRegion "callable:App:localFn" (fun r -> { r with CallableInterfaceDigest = CallableInterfaceDigest substituted }) separatedWitnessRegionsFixture
        | "realization" ->
            "Codata.WitnessSegmentation.Regions.SemanticRealizationDigest",
            updateRegion "callable:App:localFn" (fun r -> { r with SemanticRealizationDigest = SemanticRealizationDigest substituted }) separatedWitnessRegionsFixture
        | _ ->
            "Codata.WitnessSegmentation.Regions.CanonicalProofSupportDigest",
            updateRegion "callable:App:localFn" (fun r -> { r with CanonicalProofSupportDigest = CanonicalProofSupportDigest substituted }) separatedWitnessRegionsFixture
    let violation = only part (Integrity.check changed)
    Assert.Equal(Some(NodeId 1), violation.Node)
    Assert.Contains("[WSEG-003]", violation.Reason)
    Assert.Contains(foreignName, violation.Reason)

[<Theory>]
[<InlineData("realization-into-proof")>]
[<InlineData("interface-into-proof")>]
[<InlineData("interface-into-realization")>]
let ``witness region refuses cross digest inner payload reuse`` substitution =
    let part, changed =
        match substitution with
        | "realization-into-proof" ->
            "Codata.WitnessSegmentation.Regions.CanonicalProofSupportDigest",
            updateRegion "callable:App:localFn" (fun r ->
                { r with CanonicalProofSupportDigest = CanonicalProofSupportDigest "proof-support:localFn-body-v1" }) separatedWitnessRegionsFixture
        | "interface-into-proof" ->
            "Codata.WitnessSegmentation.Regions.CanonicalProofSupportDigest",
            updateRegion "callable:App:localFn" (fun r ->
                { r with CanonicalProofSupportDigest = CanonicalProofSupportDigest "proof-support:localFn-sig-v1" }) separatedWitnessRegionsFixture
        | _ ->
            "Codata.WitnessSegmentation.Regions.SemanticRealizationDigest",
            updateRegion "callable:App:localFn" (fun r ->
                { r with SemanticRealizationDigest = SemanticRealizationDigest "semantic-realization:localFn-sig-v1" }) separatedWitnessRegionsFixture
    let violation = only part (Integrity.check changed)
    Assert.Equal(Some(NodeId 1), violation.Node)
    Assert.Contains("[WSEG-003]", violation.Reason)

[<Theory>]
[<InlineData("callable")>]
[<InlineData("realization")>]
[<InlineData("proof")>]
let ``witness region refuses unprefixed raw digest strings`` slot =
    let part, changed =
        match slot with
        | "callable" ->
            "Codata.WitnessSegmentation.Regions.CallableInterfaceDigest",
            updateRegion "callable:App:localFn" (fun r -> { r with CallableInterfaceDigest = CallableInterfaceDigest "unprefixed-hash" }) separatedWitnessRegionsFixture
        | "realization" ->
            "Codata.WitnessSegmentation.Regions.SemanticRealizationDigest",
            updateRegion "callable:App:localFn" (fun r -> { r with SemanticRealizationDigest = SemanticRealizationDigest "unprefixed-hash" }) separatedWitnessRegionsFixture
        | _ ->
            "Codata.WitnessSegmentation.Regions.CanonicalProofSupportDigest",
            updateRegion "callable:App:localFn" (fun r -> { r with CanonicalProofSupportDigest = CanonicalProofSupportDigest "unprefixed-hash" }) separatedWitnessRegionsFixture
    let violation = only part (Integrity.check changed)
    Assert.Contains("[WSEG-004]", violation.Reason)

[<Theory>]
[<InlineData("empty-supports")>]
[<InlineData("blank-support-entry")>]
[<InlineData("blank-reason")>]
let ``unclassified proof support coverage refuses empty supports or blank reason`` defectKind =
    let coverage =
        match defectKind with
        | "empty-supports" -> ProofSupportCoverage.Unclassified("common-whole-revision-envelope", Set.empty)
        | "blank-support-entry" -> ProofSupportCoverage.Unclassified("common-whole-revision-envelope", Set.singleton "   ")
        | _ -> ProofSupportCoverage.Unclassified("   ", Set.singleton "owner:whole-revision")
    let changed = updateRegion "common" (fun r -> { r with ProofSupportCoverage = coverage }) separatedWitnessRegionsFixture
    let violation = only "Codata.WitnessSegmentation.Regions.ProofSupportCoverage" (Integrity.check changed)
    Assert.Equal(None, violation.Node)
    Assert.Contains("[WSEG-005]", violation.Reason)

[<Fact>]
let ``dropping a required numeric interface census dependency row fails integrity with coded diagnostic`` () =
    let numericCensus : ProofSupportCensus =
        { Identity = "numericInterface:int32-add"; Kind = ProofSupportCensusKind.NumericInterface
          Entries = Set.singleton "Alloy.Core.Int32.op_Addition" }
    let participant : ProofSupportParticipant =
        { Address = "module:App/binding:add/0"; Role = ParticipantRole.Site; Ordinal = 0; Group = "module:App/binding:add/0" }
    let validRegion : WitnessRegion =
        { Identity = "callable:App:numericAdd"; Flavor = WitnessRegionKind.ScalarCallable
          Root = Some(NodeId 1); Anchor = Some(NodeId 1); Path = []
          Members = Set.ofList [NodeId 1; NodeId 2; NodeId 3; NodeId 4]
          Supports = Set.ofList [NodeId 1; NodeId 2; NodeId 3; NodeId 4; NodeId 64; NodeId 404; NodeId 8000]
          OwnerSupport = SupportKey.WholeOwningAnalysisRegion "owner:numericAdd"
          CallableInterfaceDigest = CallableInterfaceDigest "callable-interface:numericAdd-sig"
          SemanticRealizationDigest = SemanticRealizationDigest "semantic-realization:numericAdd-body"
          CanonicalProofSupportDigest = CanonicalProofSupportDigest "proof-support:numericAdd-proof"
          ProofSupportCoverage = ProofSupportCoverage.Global([participant], [numericCensus])
          Dependencies = Set.empty }
    let withRegion region =
        { numericOperationFacts with
            Codata = { numericOperationFacts.Codata with WitnessSegmentation = Some { Version = 1; Regions = [region] } } }
    Assert.Empty(Integrity.check (withRegion validRegion))
    let platformOnly : ProofSupportCensus =
        { Identity = "platform:widths"; Kind = ProofSupportCensusKind.PlatformLayout; Entries = Set.singleton "lp64" }
    let droppedNumericCensus =
        { validRegion with ProofSupportCoverage = ProofSupportCoverage.Global([participant], [platformOnly]) }
    let violation = only "Codata.WitnessSegmentation.Regions.ProofSupportCoverage" (Integrity.check (withRegion droppedNumericCensus))
    Assert.Equal(Some(NodeId 1), violation.Node)
    Assert.Contains("[WSEG-007]", violation.Reason)
    Assert.Contains("NumericInterface", violation.Reason)

[<Theory>]
[<InlineData("global-empty-censuses")>]
[<InlineData("census-blank-id")>]
[<InlineData("census-empty-entries")>]
[<InlineData("participant-blank-address")>]
[<InlineData("participant-negative-ordinal")>]
[<InlineData("owned-claim-missing-participants")>]
[<InlineData("shared-empty-regions")>]
[<InlineData("shared-self-only")>]
[<InlineData("shared-unknown-sibling")>]
let ``proof support coverage refuses malformed census participant and shared scope accounts`` caseName =
    let expectedCode, changed =
        match caseName with
        | "global-empty-censuses" ->
            "[WSEG-007]",
            updateRegion "callable:App:globalFn" (fun r -> { r with ProofSupportCoverage = ProofSupportCoverage.Global([], []) }) separatedWitnessRegionsFixture
        | "census-blank-id" ->
            let bad : ProofSupportCensus = { Identity = "  "; Kind = ProofSupportCensusKind.PlatformLayout; Entries = Set.singleton "lp64" }
            "[WSEG-007]",
            updateRegion "callable:App:globalFn" (fun r -> { r with ProofSupportCoverage = ProofSupportCoverage.Global([], [bad]) }) separatedWitnessRegionsFixture
        | "census-empty-entries" ->
            let bad : ProofSupportCensus = { Identity = "platform:widths"; Kind = ProofSupportCensusKind.PlatformLayout; Entries = Set.empty }
            "[WSEG-007]",
            updateRegion "callable:App:globalFn" (fun r -> { r with ProofSupportCoverage = ProofSupportCoverage.Global([], [bad]) }) separatedWitnessRegionsFixture
        | "participant-blank-address" ->
            let bad : ProofSupportParticipant = { Address = ""; Role = ParticipantRole.Site; Ordinal = 0; Group = "g" }
            let keep : ProofSupportParticipant = { Address = "module:App/binding:localFn/0"; Role = ParticipantRole.Site; Ordinal = 0; Group = "g" }
            "[WSEG-006]",
            updateRegion "callable:App:localFn" (fun r -> { r with ProofSupportCoverage = ProofSupportCoverage.Local([keep; bad], []) }) separatedWitnessRegionsFixture
        | "participant-negative-ordinal" ->
            let bad : ProofSupportParticipant = { Address = "module:App/binding:localFn/0"; Role = ParticipantRole.Site; Ordinal = -1; Group = "g" }
            "[WSEG-006]",
            updateRegion "callable:App:localFn" (fun r -> { r with ProofSupportCoverage = ProofSupportCoverage.Local([bad], []) }) separatedWitnessRegionsFixture
        | "owned-claim-missing-participants" ->
            "[WSEG-006]",
            updateRegion "callable:App:localFn" (fun r -> { r with ProofSupportCoverage = ProofSupportCoverage.Local([], []) }) separatedWitnessRegionsFixture
        | "shared-empty-regions" ->
            "[WSEG-008]",
            updateRegion "callable:App:sharedFn" (fun r -> { r with ProofSupportCoverage = ProofSupportCoverage.Shared(Set.empty, [], []) }) separatedWitnessRegionsFixture
        | "shared-self-only" ->
            "[WSEG-008]",
            updateRegion "callable:App:sharedFn" (fun r -> { r with ProofSupportCoverage = ProofSupportCoverage.Shared(Set.singleton "callable:App:sharedFn", [], []) }) separatedWitnessRegionsFixture
        | _ ->
            "[WSEG-008]",
            updateRegion "callable:App:sharedFn" (fun r -> { r with ProofSupportCoverage = ProofSupportCoverage.Shared(Set.ofList ["callable:App:sharedFn"; "callable:App:ghost"], [], []) }) separatedWitnessRegionsFixture
    let violation = only "Codata.WitnessSegmentation.Regions.ProofSupportCoverage" (Integrity.check changed)
    Assert.Contains(expectedCode, violation.Reason)

[<Fact>]
let ``witness segmentation refuses blank and duplicate region identities`` () =
    let blanked =
        let segmentation = separatedWitnessRegionsFixture.Codata.WitnessSegmentation.Value
        let regions = segmentation.Regions |> List.map (fun r ->
            if r.Identity = "common" then { r with Identity = "   " } else r)
        { separatedWitnessRegionsFixture with Codata = { separatedWitnessRegionsFixture.Codata with WitnessSegmentation = Some { segmentation with Regions = regions } } }
    let blankViolation = only "Codata.WitnessSegmentation.Regions.Identity" (Integrity.check blanked)
    Assert.Contains("[WSEG-001]", blankViolation.Reason)
    let duplicated =
        let segmentation = separatedWitnessRegionsFixture.Codata.WitnessSegmentation.Value
        let target = segmentation.Regions |> List.find (fun r -> r.Identity = "callable:App:globalFn")
        { separatedWitnessRegionsFixture with Codata = { separatedWitnessRegionsFixture.Codata with WitnessSegmentation = Some { segmentation with Regions = segmentation.Regions @ [target] } } }
    let dupViolations = Integrity.check duplicated |> List.filter (fun v -> v.Part = "Codata.WitnessSegmentation.Regions.Identity")
    Assert.Equal(2, dupViolations.Length)
    Assert.All(dupViolations, fun v -> Assert.Contains("[WSEG-001]", v.Reason))

// Tranche 2: finite plans and their fault-injection checks.
let private optionalPlanRetirement : CallableAggregateResultRetirement =
    { Application = NodeId 10; Caller = NodeId 11; Construction = NodeId 12
      Actual = NodeId 13; Receiver = NodeId 14
      Policy = { ProjectPath = "fixture.fidproj"; SourceVersion = String.replicate 64 "a"; Model = "Standard" }
      Uses = [NodeId 10; NodeId 13; NodeId 14] }

let private presentPlan retirement : OptionalEntryArgumentConversionModel =
    { Call = NodeId 14; Parameter = 0; Actual = NodeId 13; Construction = NodeId 12
      SourceCase = 1; Payload = NodeId 15; Formation = NodeId 16; Invocation = NodeId 17
      Arms = [{ CaseOrdinal = 0; Choice = OptionalEntryPlanChoice.PendingAbsence; Formation = None }
              { CaseOrdinal = 1; Choice = OptionalEntryPlanChoice.ClosedEntry; Formation = Some(NodeId 16) }]
      ResultRetirement = retirement }

let private absentPlan retirement : OptionalEntryAbsenceArgumentConversionModel =
    { Call = NodeId 14; Parameter = 0; Actual = NodeId 13; Construction = NodeId 12
      SourceCase = 0; Absence = NodeId 18
      Arms = [{ CaseOrdinal = 0; Choice = OptionalEntryAbsencePlanChoice.AbsentEntry }
              { CaseOrdinal = 1; Choice = OptionalEntryAbsencePlanChoice.RequiresClosedEntry }]
      ResultRetirement = retirement }

let private projected = function
    | Ok value -> value
    | Error reason -> failwith reason

[<Theory>]
[<InlineData(false, false)>]
[<InlineData(false, true)>]
[<InlineData(true, false)>]
[<InlineData(true, true)>]
let ``finite optional plans project Some and None with and without result retirement`` absent retired =
    let retirement = if retired then Some optionalPlanRetirement else None
    let projection =
        if absent then OptionalEntryArgumentProof.projectAbsence (absentPlan retirement) |> projected
        else OptionalEntryArgumentProof.project (presentPlan retirement) |> projected
    let name = if absent then "optional_entry_absence_case" else "optional_entry_case"
    Assert.Contains((name, ResourceProof.Sort.Integer), projection.Declarations)
    Assert.Equal<ResourceProof.Expr list>(
        [ResourceProof.Expr.Equal(ResourceProof.Expr.Variable name, ResourceProof.Expr.Integer(if absent then 0I else 1I))],
        projection.Alternatives)
    let retirementFields = projection.Declarations |> List.filter (fun (name, _) -> name.StartsWith("optional_retirement_"))
    Assert.Equal((if retired then 11 else 0), retirementFields.Length)
    if absent then
        Assert.Contains(("optional_entry_absence_accepted_18", ResourceProof.Sort.Boolean), projection.Declarations)
    if retired then
        Assert.Contains(("retirement_receiver", "optional_retirement_receiver"), projection.ParticipantRoles)

[<Theory>]
[<InlineData("missing")>]
[<InlineData("duplicate")>]
[<InlineData("ordinal")>]
[<InlineData("choice")>]
[<InlineData("formation")>]
let ``finite Some plan rejects invalid arms`` defect =
    let model = presentPlan None
    let arms =
        match defect with
        | "missing" -> [model.Arms.Head]
        | "duplicate" -> model.Arms @ [model.Arms.Head]
        | "ordinal" -> [{model.Arms.Head with CaseOrdinal = 1}; model.Arms[1]]
        | "choice" -> [{model.Arms.Head with Choice = OptionalEntryPlanChoice.ClosedEntry}; model.Arms[1]]
        | _ -> [model.Arms.Head; {model.Arms[1] with Formation = None}]
    Assert.Equal<Result<ResourceProof.Projection, string>>(
        Error "The optional entry conversion plan requires exact None and Some arms.",
        OptionalEntryArgumentProof.project {model with Arms = arms})

[<Theory>]
[<InlineData("missing")>]
[<InlineData("duplicate")>]
[<InlineData("ordinal")>]
[<InlineData("choice")>]
let ``finite None plan rejects invalid arms`` defect =
    let model = absentPlan None
    let arms =
        match defect with
        | "missing" -> [model.Arms.Head]
        | "duplicate" -> model.Arms @ [model.Arms.Head]
        | "ordinal" -> [{model.Arms.Head with CaseOrdinal = 1}; model.Arms[1]]
        | _ -> [{model.Arms.Head with Choice = OptionalEntryAbsencePlanChoice.RequiresClosedEntry}; model.Arms[1]]
    Assert.Equal<Result<ResourceProof.Projection, string>>(
        Error "The optional entry absence conversion plan requires exact AbsentEntry and RequiresClosedEntry arms.",
        OptionalEntryArgumentProof.projectAbsence {model with Arms = arms})

[<Theory>]
[<InlineData("receiver")>]
[<InlineData("actual")>]
[<InlineData("construction")>]
[<InlineData("application")>]
[<InlineData("first-use")>]
[<InlineData("last-use")>]
[<InlineData("missing-actual")>]
[<InlineData("duplicate-use")>]
[<InlineData("policy-path")>]
[<InlineData("policy-version")>]
[<InlineData("policy-model")>]
let ``finite optional plans reject incomplete result retirement`` defect =
    let row = optionalPlanRetirement
    let changed =
        match defect with
        | "receiver" -> {row with Receiver = NodeId 99}
        | "actual" -> {row with Actual = NodeId 99}
        | "construction" -> {row with Construction = NodeId 99}
        | "application" -> {row with Application = row.Receiver}
        | "first-use" -> {row with Uses = row.Uses.Tail}
        | "last-use" -> {row with Uses = [row.Application; row.Actual]}
        | "missing-actual" -> {row with Uses = [row.Application; row.Receiver]}
        | "duplicate-use" -> {row with Uses = [row.Application; row.Actual; row.Actual; row.Receiver]}
        | "policy-path" -> {row with Policy = {row.Policy with ProjectPath = ""}}
        | "policy-version" -> {row with Policy = {row.Policy with SourceVersion = ""}}
        | _ -> {row with Policy = {row.Policy with Model = ""}}
    let expected = Error "The optional entry aggregate result retirement account is incomplete."
    Assert.Equal<Result<ResourceProof.Projection, string>>(expected, OptionalEntryArgumentProof.project (presentPlan (Some changed)))
    Assert.Equal<Result<ResourceProof.Projection, string>>(expected, OptionalEntryArgumentProof.projectAbsence (absentPlan (Some changed)))

let private bufferAbsencePlan sourceCase : BufferAbsenceArgumentConversionModel =
    { Call = NodeId 1
      Parameter = 0
      Actual = NodeId 3
      Construction = NodeId 3
      SourceCase = sourceCase
      Absence = NodeId 700
      Arms =
          [ { CaseOrdinal = 0; Choice = BufferAbsencePlanChoice.AbsentNull }
            { CaseOrdinal = 1; Choice = BufferAbsencePlanChoice.RequiresNonNullBuffer } ] }

[<Theory>]
[<InlineData(0)>]
[<InlineData(1)>]
let ``buffer absence plans project None and Some with canonical participant roles and refutation`` sourceCase =
    let model = bufferAbsencePlan sourceCase
    let projection = BufferAbsenceArgumentProof.project model |> projected
    let expectedRoles =
        [ "source_case", "buffer_absence_case"
          "choice", "buffer_absence_choice"
          "absence", "buffer_absence_accepted_700" ]
    Assert.Equal<(string * ResourceProof.Sort) list>(
        [ "buffer_absence_case", ResourceProof.Sort.Integer
          "buffer_absence_choice", ResourceProof.Sort.Integer
          "buffer_absence_accepted_700", ResourceProof.Sort.Boolean ],
        projection.Declarations)
    Assert.Equal<(string * string) list>(expectedRoles, projection.ParticipantRoles)
    Assert.Equal<(string * string) list>(
        expectedRoles,
        ObligationBody.participantRoles (ObligationBody.BufferAbsenceArgumentConversion model))
    Assert.Equal<ResourceProof.Expr list>(
        [ ResourceProof.Expr.Equal(ResourceProof.Expr.Variable "buffer_absence_case", ResourceProof.Expr.Integer(bigint sourceCase)) ],
        projection.Alternatives)
    Assert.Empty(ResourceProof.missingParticipantVariables projection)
    let smt = ResourceProof.refutation "buf_abs_ctrl" projection
    Assert.Equal(6, smt.Length)
    let premises = ResourceProof.anchoredPremisesQueries "buf_abs_ctrl" projection
    Assert.Single(premises) |> ignore
    Assert.Contains(sprintf "(= buffer_absence_case %d)" sourceCase, premises.Head)
    let nonVacuity = ResourceProof.anchoredNonVacuityQueries "buf_abs_ctrl" projection
    Assert.Equal(2, nonVacuity.Length)

[<Theory>]
[<InlineData("parameter")>]
[<InlineData("missing")>]
[<InlineData("duplicate")>]
[<InlineData("ordinal")>]
[<InlineData("choice")>]
let ``buffer absence plan rejects negative parameter or invalid arms`` defect =
    let model = bufferAbsencePlan 0
    let badModel, expectedMsg =
        match defect with
        | "parameter" ->
            { model with Parameter = -1 }, "The buffer absence conversion requires a non-negative parameter ordinal."
        | "missing" ->
            { model with Arms = [ model.Arms.Head ] }, "The buffer absence conversion plan requires exact AbsentNull and RequiresNonNullBuffer arms."
        | "duplicate" ->
            { model with Arms = model.Arms @ [ model.Arms.Head ] }, "The buffer absence conversion plan requires exact AbsentNull and RequiresNonNullBuffer arms."
        | "ordinal" ->
            { model with Arms = [ { model.Arms.Head with CaseOrdinal = 1 }; model.Arms[1] ] }, "The buffer absence conversion plan requires exact AbsentNull and RequiresNonNullBuffer arms."
        | _ ->
            { model with Arms = [ { model.Arms.Head with Choice = BufferAbsencePlanChoice.RequiresNonNullBuffer }; model.Arms[1] ] }, "The buffer absence conversion plan requires exact AbsentNull and RequiresNonNullBuffer arms."
    Assert.Equal<Result<ResourceProof.Projection, string>>(
        Error expectedMsg,
        BufferAbsenceArgumentProof.project badModel)
    Assert.Equal<(string * string) list>(
        [ "source_case", "buffer_absence_case"
          "choice", "buffer_absence_choice"
          "absence", "buffer_absence_accepted_700" ],
        ObligationBody.participantRoles (ObligationBody.BufferAbsenceArgumentConversion badModel))

let private foreignResultControl () =
    let held = boundaryCalleeFacts
    let hypothesis : ForeignResultHypothesis =
        { Quote = NodeId 4; Declaration = NodeId 2; Identity = "read-result"; Version = "1"; Source = "fixture"
          Lower = ForeignResultBound.Constant -1I; Upper = ForeignResultBound.Argument 0 }
    let application : ForeignResultApplication =
        { Declaration = NodeId 2; Call = NodeId 1; Context = []; Hypothesis = Some hypothesis
          Arguments = [{Index = 0; Node = NodeId 3; Enclosure = ValueRange.Bounded(1I,4I)}
                       {Index = 1; Node = NodeId 4; Enclosure = ValueRange.Bounded(3I,4I)}] }
    let model role : ForeignResultCoverageModel =
        { Application = application; Role = role; ResultRange = ValueRange.Bounded(-1I,4I)
          Destination = ValueRange.Bounded(-(1I <<< 31), (1I <<< 31)-1I); DestinationDeclaration = Some(NodeId 64)
          Abi = Some(NodeId 72); AbiRange = ValueRange.Bounded(-(1I <<< 31), (1I <<< 31)-1I)
          AbiIdentity = Some "fixture-abi-1"; DestinationIdentity = Some "fixture-destination-1" }
    let p role ordinal id : Participant = {Role = role; Ordinal = ordinal; Group = NodeId 1; Node = NodeId id}
    let participants =
        [p ParticipantRole.ForeignResultDeclaration 0 2; p ParticipantRole.ForeignResultCall 0 1
         p ParticipantRole.ForeignResultHypothesis 0 4; p ParticipantRole.ForeignResultActual 0 3
         p ParticipantRole.ForeignResultActual 1 4; p ParticipantRole.ForeignResultAbi 0 72
         p ParticipantRole.ForeignResultDestination 0 64; p ParticipantRole.ForeignResultAbi 1 72
         p ParticipantRole.ForeignResultDestination 1 64]
    let claims = [ForeignResultProofRole.LogicalCoverage, NodeId 940; ForeignResultProofRole.AbiNarrowing, NodeId 941]
    let account : ForeignResultUse = {Application = application; Participants = ParticipantEvidence.Established participants; Claims = claims}
    let additions = claims |> List.map (fun (role, id) ->
        id, {Id = sprintf "result-%A" role; Kind = "foreign-result-coverage"; Logic = "QF_LIA"
             Statement = "The result is covered under the external hypothesis."; Source = "fixture"; Refs = []
             Body = ObligationBody.ForeignResultCoverage(model role)})
    { held with
        CurrentClaims = additions |> List.fold (fun rows (id, claim) -> Map.add id claim rows) held.CurrentClaims
        Obligations = held.Obligations @ List.map snd additions
        ObligationSources = claims |> List.fold (fun rows (_, id) -> Map.add id [participants |> List.map _.Node] rows) held.ObligationSources
        Emission = {held.Emission with
                        Boundary = {held.Emission.Boundary with ResultHypotheses = [hypothesis]}
                        Numeric = {held.Emission.Numeric with ForeignResultUses = [account]}} }

let private foreignControlModel () =
    match (foreignResultControl ()).CurrentClaims[NodeId 940].Body with
    | ObligationBody.ForeignResultCoverage model -> model
    | _ -> failwith "Expected a foreign-result model."

[<Fact>]
let ``foreign result rows retain two ordered current claims and complete sources`` () =
    Assert.Empty(Integrity.check (foreignResultControl ()))

[<Theory>]
[<InlineData("duplicate-account", "Application", "duplicated")>]
[<InlineData("hypothesis", "Hypothesis", "declaration census")>]
[<InlineData("ordinal", "Arguments", "consecutive")>]
[<InlineData("missing-role", "Claims", "two distinct ordered")>]
[<InlineData("duplicate-citizen", "Claims", "two distinct ordered")>]
[<InlineData("participants", "Participants", "ordered declaration")>]
[<InlineData("sources", "Sources", "complete ordered source vector")>]
[<InlineData("missing-account", "Claims", "exact invocation account")>]
[<InlineData("wrong-model", "Claims", "exact current conditional model")>]
let ``foreign result rows reject detached or mismatched invocation evidence`` defect suffix (reason: string) =
    let held = foreignResultControl ()
    let account = held.Emission.Numeric.ForeignResultUses.Head
    let uses =
        match defect with
        | "duplicate-account" -> [account; account]
        | "hypothesis" -> [{account with Application = {account.Application with Hypothesis = None}}]
        | "ordinal" -> [{account with Application = {account.Application with Arguments = [{account.Application.Arguments.Head with Index = 3}]}}]
        | "missing-role" -> [{account with Claims = [account.Claims.Head]}]
        | "duplicate-citizen" -> [{account with Claims = [account.Claims.Head; ForeignResultProofRole.AbiNarrowing, snd account.Claims.Head]}]
        | "participants" -> [{account with Participants = ParticipantEvidence.Established []}]
        | "missing-account" -> []
        | _ -> [account]
    let changed = {held with Emission = {held.Emission with Numeric = {held.Emission.Numeric with ForeignResultUses = uses}}}
    let changed =
        if defect = "sources" then {changed with ObligationSources = changed.ObligationSources.Add(NodeId 940, [[NodeId 1]])}
        elif defect = "wrong-model" then
            let claim = {changed.CurrentClaims[NodeId 940] with Body = ObligationBody.ForeignResultCoverage {foreignControlModel () with Role = ForeignResultProofRole.AbiNarrowing}}
            {changed with CurrentClaims = changed.CurrentClaims.Add(NodeId 940, claim)
                          Obligations = changed.Obligations |> List.map (fun row -> if row.Id = claim.Id then claim else row)}
        else changed
    Assert.Contains(Integrity.check changed, fun v ->
        v.Part = "Emission.Numeric.ForeignResultUses." + suffix && v.Node = Some(NodeId 1) && v.Reason.Contains reason)

[<Theory>]
[<InlineData("hypothesis")>]
[<InlineData("abi")>]
[<InlineData("unbounded-destination")>]
[<InlineData("argument")>]
[<InlineData("unbounded-result")>]
let ``foreign result projection rejects incomplete finite premises`` defect =
    let model = foreignControlModel ()
    let changed =
        match defect with
        | "hypothesis" -> {model with Application = {model.Application with Hypothesis = None}}
        | "abi" -> {model with Abi = None}
        | "unbounded-destination" -> {model with Destination = ValueRange.Unbounded}
        | "argument" -> {model with Application = {model.Application with Arguments = []}}
        | _ -> {model with ResultRange = ValueRange.Unbounded}
    match ForeignResultCoverage.ofModel changed with
    | Error reason -> Assert.False(System.String.IsNullOrWhiteSpace reason)
    | Ok _ -> failwithf "The %s negative control was accepted." defect

[<Fact>]
let ``foreign result queries preserve premises anchors refutation and nonvacuity`` () =
    let projection = ForeignResultCoverage.ofModel (foreignControlModel ()) |> projected
    let premises = ForeignResultCoverage.premisesQuery projection
    let anchored = ForeignResultCoverage.anchoredPremisesQuery "result_control" projection
    let refutation = ForeignResultCoverage.refutation "result_control" projection
    let nonvacuity = ForeignResultCoverage.nonVacuityQuery projection
    Assert.Contains("(set-logic QF_LIA)", premises)
    Assert.Contains("(<= foreign_result foreign_arg_0)", premises)
    Assert.DoesNotContain("(assert (not result_control))", premises)
    Assert.Equal(premises.Replace("(check-sat)", "(declare-fun result_control () Bool)\n(check-sat)"), anchored)
    Assert.Equal("(assert (not result_control))", List.last refutation)
    Assert.Contains(refutation, fun line -> line.StartsWith("(assert (= result_control "))
    Assert.Contains("(assert (not " + ForeignResultCoverage.smtLib projection.Conclusion + "))", nonvacuity)
    Assert.DoesNotContain("(assert " + ForeignResultCoverage.smtLib projection.Premises + ")", nonvacuity)
    let changed = {projection with Conclusion = ForeignResultCoverage.Predicate.And []}
    Assert.NotEqual<string>(nonvacuity, ForeignResultCoverage.nonVacuityQuery changed)
    Assert.NotEqual<string list>(refutation, ForeignResultCoverage.refutation "result_control" changed)
    let changed = {projection with Premises = ForeignResultCoverage.Predicate.And []}
    Assert.NotEqual<string>(premises, ForeignResultCoverage.premisesQuery changed)
    Assert.NotEqual<string>(anchored, ForeignResultCoverage.anchoredPremisesQuery "result_control" changed)

let private conditionalOptionalCallback () =
    let held = boundaryCalleeFacts
    let callbackType = held.Nodes[NodeId 3].Type
    let fnType = TypeIdentity.Function(callbackType, callbackType)
    let entryType = TypeIdentity.Application({Declaration = {Module = []; Name = "FnPtr"}; Parameters = []; NativeKind = Some NTUKind.NTUfnptr}, [fnType])
    let optionType = TypeIdentity.Application({Declaration = {Module = []; Name = "option"}; Parameters = [TypeParamKind.Type]; NativeKind = None}, [entryType])
    let intType = TypeIdentity.Application(
        {Declaration = {Module = []; Name = "int"}; Parameters = []
         NativeKind = Some(NTUKind.NTUint(NTUWidth.Resolved WidthDimension.Register))}, [])
    let p role ordinal group number : Participant =
        {Role = role; Ordinal = ordinal; Group = NodeId group; Node = NodeId number}
    let fact form text numbers refs parent : BoundaryDeclarationFact =
        let nodeRefs = refs |> List.map NodeId
        {Form = form; Text = text; Numbers = numbers; References = nodeRefs; Children = nodeRefs; Parent = parent |> Option.map NodeId; SourceType = unitType}
    let record fields refs parent = fact "record" fields [] refs (Some parent)
    let text value parent = fact "string" [value] [] [] (Some parent)
    let declBinding name child = fact "binding" [name] [0I; 0I] [child] (Some 400)
    let contractType name = TypeIdentity.Application({Declaration = {Module = ["BAREWire"; "Descriptors"]; Name = name}; Parameters = []; NativeKind = None}, [])
    let header = {held.SourceReadings.ContextHeaders[NodeId 50] with Identity = NodeId 400; Name = "OptionalControl"}
    let target : BoundaryPlatformPremise =
        {Id = "optional-control"; Description = None; Loading = None; LibraryPath = None; SourcePaths = Set.singleton "fixture"
         Architecture = Some "x86_64"; OS = Some "linux"; RuntimeClaim = None; Substrate = None
         Dimensions = Map.ofList ["Pointer", 64; "Register", 64]; Representations = Map.empty; EndpointReturns = Map.empty}
    let premise shape embedded reachable : BoundarySourcePremise =
        {Shape = shape; EmbeddedTypes = embedded; ConstructorFacts = []; Reachable = reachable; Range = None; ExternLibrary = None; ExternSymbol = None; HasExtern = false; Metadata = Map.empty}
    let lifetime : ProgramImageCodeLifetime = {Module = NodeId 400; Binding = NodeId 401; Implementation = NodeId 10}
    let lifetimeParts = [p ParticipantRole.CallableLifetime 0 100 400; p ParticipantRole.CallableLifetime 1 100 401; p ParticipantRole.CallableLifetime 2 100 10]
    let sourcePremises =
        [NodeId 400, premise {fact "module" ["OptionalControl"] [] [401] None with Children = []} [] false
         NodeId 401, premise {fact "binding" ["callback"; "no-declaration-root"] [0I; 0I] [10] (Some 400) with SourceType = fnType} [] true
         NodeId 10, premise {fact "lambda" ["RegularClosure"; "argument"] [1I; 0I; 0I] [41; 11] (Some 401) with SourceType = fnType} [callbackType] true] |> Map.ofList
    let contract : CallableContract =
        {Identity = NodeId 100; Kind = CallableKind.NativeEntry
         Convention = CallableConvention.CompilerOwnedPortable
            {Target = target; ParameterConversions = [0, CallableConversion.Identity(ValueRepresentation.Scalar(SettledSlot.Integer(32, None)))]
             ResultConversion = CallableConversion.Identity(ValueRepresentation.Scalar(SettledSlot.Integer(32, None))); CodeLifetime = lifetime}
         ParameterTypes = [callbackType]; OmittedParameters = []; ParameterRepresentations = [0, ValueRepresentation.Scalar(SettledSlot.Integer(32, None))]
         ResultType = callbackType; ResultRepresentation = ValueRepresentation.Scalar(SettledSlot.Integer(32, None)); EnvironmentBytes = None; SourcePremises = sourcePremises
         Participants = [p ParticipantRole.CallableContract 0 100 100; p ParticipantRole.Source 0 100 400; p ParticipantRole.Source 1 100 401; p ParticipantRole.Source 2 100 10] @ lifetimeParts}
    let carrier : CallableCarrier =
        {Occurrence = NodeId 30; Kind = CallableKind.NativeEntry; Formation = NodeId 30; EnvironmentValue = None
         Contract = Ok(NodeId 100); Lifetime = lifetimeParts; SourceType = entryType; Implementation = NodeId 10
         Parameters = ["argument", callbackType, NodeId 41]; ParameterShapes = [CallableValueShape.Data(NodeId 41)]
         OmittedParameters = Set.empty; Result = NodeId 11; ResultShape = CallableValueShape.Data(NodeId 11); Environment = None}
    let slot : CallableAggregateSlot =
        {Identity = NodeId 101; AggregateType = optionType; Declaration = None; DeclarationFacts = []
         Path = [CallableAggregatePathStep.UnionPayload(1, 0)]; SourceType = entryType; Contract = Ok(NodeId 100)
         Participants = [p ParticipantRole.AggregateSlot 0 101 101; p ParticipantRole.CallableContract 0 101 100]}
    let alternative : CallableAggregateAlternative =
        {Ordinal = 0; Carrier = NodeId 30; Formation = NodeId 30; EnvironmentValue = None; Contract = NodeId 100; Adapter = None; EnvironmentPlacement = None}
    let selector = Some {Lower = 0; UpperExclusive = 1; Storage = None; Slot = None; ByteOffset = None}
    let tagSome : CallableAggregateTag =
        {Constructor = NodeId 2; TagRead = None; CaseOrdinal = 1; PayloadOrdinal = Some 0; Payload = Some(NodeId 30)
         Participants = [p ParticipantRole.AggregateConstructor 0 2 2; p ParticipantRole.AggregatePayload 0 2 30]}
    let tagNone : CallableAggregateTag =
        {Constructor = NodeId 4; TagRead = None; CaseOrdinal = 0; PayloadOrdinal = None; Payload = None
         Participants = [p ParticipantRole.AggregateConstructor 0 4 4]}
    let constructSome : CallableAggregateValue =
        {Occurrence = NodeId 2; Aggregate = NodeId 2; Slot = NodeId 101; Alternatives = [alternative]; Selector = selector
         FormationInputs = [NodeId 30]; Value = Some(NodeId 30); SelectedAlternative = Some 0
         Operation = CallableAggregateOperation.Construct; Frontier = None; Tag = Some tagSome; Selection = None
         ResultRetirement = None; Bytes = 0; Alignment = 1
         Participants =
            [p ParticipantRole.AggregateValue 0 2 2; p ParticipantRole.AggregateSource 0 2 2
             p ParticipantRole.AggregateSlot 0 2 101; p ParticipantRole.AggregateInput 0 2 30
             p ParticipantRole.AggregateWrite 0 2 30; p ParticipantRole.CallableCarrier 0 2 30
             p ParticipantRole.CallableFormation 0 2 30; p ParticipantRole.CallableContract 0 2 100]}
    let constructNone : CallableAggregateValue =
        {Occurrence = NodeId 4; Aggregate = NodeId 4; Slot = NodeId 101; Alternatives = []; Selector = None
         FormationInputs = []; Value = None; SelectedAlternative = None
         Operation = CallableAggregateOperation.Construct; Frontier = None; Tag = Some tagNone; Selection = None
         ResultRetirement = None; Bytes = 0; Alignment = 1
         Participants =
            [p ParticipantRole.AggregateValue 0 4 4; p ParticipantRole.AggregateSource 0 4 4
             p ParticipantRole.AggregateSlot 0 4 101]}
    let selected : CallableAggregateValue =
        {Occurrence = NodeId 3; Aggregate = NodeId 3; Slot = NodeId 101; Alternatives = [alternative]; Selector = selector
         FormationInputs = [NodeId 20; NodeId 2; NodeId 4]; Value = None; SelectedAlternative = None
         Operation = CallableAggregateOperation.Select; Frontier = None; Tag = None
         Selection = Some {Condition = NodeId 20; WhenTrue = NodeId 2; WhenFalse = NodeId 4}
         ResultRetirement = None; Bytes = 0; Alignment = 1
         Participants =
            [p ParticipantRole.AggregateValue 0 3 3; p ParticipantRole.AggregateSource 0 3 3
             p ParticipantRole.AggregateSlot 0 3 101; p ParticipantRole.CallableCarrier 0 3 30
             p ParticipantRole.CallableFormation 0 3 30; p ParticipantRole.CallableContract 0 3 100
             p ParticipantRole.AggregateInput 0 3 20; p ParticipantRole.AggregateInput 1 3 2; p ParticipantRole.AggregateInput 2 3 4
             p ParticipantRole.Source 0 3 21; p ParticipantRole.Source 1 3 300]}
    let nodes =
        [{node 1 (SemanticKind.Application(NodeId 201, [NodeId 3])) [201; 3; 99] with Type = unitType; Parent = Some(NodeId 300)}
         node 201 (SemanticKind.VarRef("receive", None)) []
         {node 99 (SemanticKind.DUGetTag(NodeId 3, optionType)) [3] with Type = intType; ValueRange = Some(ValueRange.Bounded(0I, 1I)); Parent = Some(NodeId 1)}
         {node 3 (SemanticKind.IfThenElse(NodeId 20, NodeId 2, Some(NodeId 4))) [20; 2; 4] with Type = optionType; Parent = Some(NodeId 1)}
         {node 20 (SemanticKind.VarRef("flag", Some(NodeId 21))) [] with Type = boolType; Parent = Some(NodeId 3)}
         {node 2 (SemanticKind.UnionCase("Some", 1, Some(NodeId 30))) [30] with Type = optionType; Parent = Some(NodeId 3)}
         {node 4 (SemanticKind.UnionCase("None", 0, None)) [] with Type = optionType; Parent = Some(NodeId 3)}
         {node 30 (SemanticKind.Application(NodeId 403, [NodeId 402])) [403; 402] with Type = entryType; Parent = Some(NodeId 2)}
         {node 402 (SemanticKind.VarRef("callback", Some(NodeId 401))) [] with Type = fnType}
         node 403 (SemanticKind.Intrinsic {Module = IntrinsicModule.FnPtr; Operation = "ofFunction"; Category = IntrinsicCategory.Pure; FullName = "FnPtr.ofFunction"}) []
         {node 401 (SemanticKind.Binding("callback", false, false, None)) [10] with Type = fnType; Parent = Some(NodeId 400)}
         {node 10 (SemanticKind.Lambda(["argument", callbackType, NodeId 41], NodeId 11, [], Some "callback", LambdaContext.RegularClosure)) [41; 11] with Type = fnType; Parent = Some(NodeId 401)}
         {node 41 (SemanticKind.PatternBinding "argument") [] with Type = callbackType; Parent = Some(NodeId 10)}
         {node 11 (SemanticKind.Literal(NativeLiteral.Int(1L, NTUKind.NTUint(NTUWidth.Fixed 32)))) [] with Type = callbackType; Parent = Some(NodeId 10)}
         {node 21 (SemanticKind.PatternBinding "flag") [] with Type = boolType; Parent = Some(NodeId 300)}
         {node 300 (SemanticKind.Lambda(["flag", boolType, NodeId 21], NodeId 1, [], Some "caller", LambdaContext.RegularClosure)) [21; 1] with Type = TypeIdentity.Function(boolType, unitType)}]
    let baseRevision = revision nodes
    let allNodes = baseRevision.Nodes
    let declName = CallableSymbolName.RootBinding "callback"
    let declaration : CallableEmissionDeclaration =
        {Lookup = NodeId 10; Implementation = NodeId 10; Parameters = ["argument", callbackType, NodeId 41]; Result = NodeId 11
         Context = LambdaContext.RegularClosure; Captures = []; Name = declName; Parent = Some(NodeId 401)
         Participants = Set.ofList [NodeId 10; NodeId 11; NodeId 41; NodeId 401]}
    let mkAccount site (accountValues: CallableAggregateValue list) : CallableAggregateDependencyAccount =
        let accountCarriers = if accountValues |> List.exists (fun row -> not row.Alternatives.IsEmpty) then [carrier] else []
        let participants =
            slot.Participants @
            (accountValues |> List.collect (fun row -> row.Participants @ (row.Tag |> Option.map _.Participants |> Option.defaultValue []))) @
            (accountCarriers |> List.collect _.Lifetime) @
            contract.Participants
        let sources =
            participants |> List.map _.Node |> List.distinct |> List.filter (sourcePremises.ContainsKey >> not)
            |> List.choose (fun id -> allNodes.TryFind id |> Option.map (fun n -> {Node = id; Kind = n.Kind; Type = n.Type; Children = n.Children; Anchors = n.ObligationAnchors}))
        let symbols = if accountCarriers.IsEmpty then [] else [NodeId 10, declName]
        {Occurrence = site; Slots = [slot]; Values = accountValues; Carriers = accountCarriers; Contracts = [contract]
         Flows = []; Joins = []; Participants = participants; Sources = sources; Claims = []; Symbols = symbols
         Inactivity = []; MemoryPolicy = None}
    let accounts =
        Map.ofList
            [NodeId 2, mkAccount (NodeId 2) [constructSome]
             NodeId 3, mkAccount (NodeId 3) [selected; constructSome; constructNone]
             NodeId 4, mkAccount (NodeId 4) [constructNone]]
    let callable =
        {baseRevision.Emission.Callable with
            Contracts = Map.ofList [NodeId 100, contract]
            Carriers = Map.ofList [NodeId 30, carrier]
            AggregateSlots = Map.ofList [NodeId 101, slot]
            AggregateValues = Map.ofList [NodeId 2, [constructSome]; NodeId 3, [selected]; NodeId 4, [constructNone]]
            AggregateDependencies = accounts
            Declarations = Map.ofList [NodeId 10, declaration]
            SignatureData = Map.ofList [NodeId 10, Set.ofList [NodeId 41; NodeId 11]]
            ClosedData = Set.ofList [NodeId 11; NodeId 41]
            NativeEntries = Map.ofList [NodeId 10, "callback"]
            Symbols = Map.ofList [NodeId 10, declName; NodeId 300, CallableSymbolName.Anonymous(NodeId 300)]}
    let facts =
        [210, record ["Parameters"] [212] 213
         213, fact "quotation" [] [] [210] (Some 214)
         214, declBinding "receiveDescriptor" 213
         211, {fact "formal" ["callback"] [] [] (Some 215) with SourceType = optionType}
         215, fact "lambda" ["receive"; "callback"] [1I; 0I; 0I] [211; 216] (Some 217)
         216, fact "unit" [] [] [] (Some 215)
         217, declBinding "receive" 215
         212, fact "array" [] [] [218] (Some 210)
         218, record ["Type"; "PassBy"] [219; 229] 212
         219, fact "case" ["Entry"] [] [220] (Some 218)
         229, fact "case" ["Value"] [] [] (Some 218)
         220, {fact "quotation" [] [1I] [222] (Some 221) with SourceType = contractType "CallbackInvocationContract"}
         221, {declBinding "receiveCallbackInvocation" 220 with SourceType = contractType "CallbackInvocationContract"}
         222, {record ["Binding"; "Parameter"; "Signature"; "Hypothesis"; "Scope"] [223; 224; 225; 226; 227] 220 with SourceType = contractType "CallbackInvocationContract"}
         223, text "OptionalControl.receive" 222
         224, fact "integer" [] [0I] [] (Some 222)
         225, record ["Parameters"; "ReturnType"; "CallingConvention"] [233; 238; 235] 222
         233, fact "array" [] [] [236] (Some 225)
         235, fact "case" ["CDecl"] [] [] (Some 225)
         236, record ["Name"; "Type"; "PassBy"] [237; 238; 239] 233
         237, text "argument" 236
         238, fact "case" ["Integer"] [] [240] (Some 236)
         239, fact "case" ["Value"] [] [] (Some 236)
         240, fact "tuple" [] [] [241; 242] (Some 238)
         241, fact "case" ["Signed"] [] [] (Some 240)
         242, fact "integer" [] [32I] [] (Some 240)
         226, record ["Identity"; "Version"; "Source"] [230; 231; 232] 222
         227, text "during_call" 222
         230, text "invoke" 226; 231, text "1" 226; 232, text "fixture" 226
         400, sourcePremises[NodeId 400].Shape
         401, sourcePremises[NodeId 401].Shape
         500, {fact "quotation" [] [1I] [502] (Some 501) with SourceType = contractType "Descriptors.CallbackAbsenceContract"}
         501, {declBinding "receiveCallbackAbsence" 500 with SourceType = contractType "Descriptors.CallbackAbsenceContract"}
         502, {record ["Binding"; "Parameter"; "Hypothesis"] [503; 504; 505] 500 with SourceType = contractType "Descriptors.CallbackAbsenceContract"}
         503, text "OptionalControl.receive" 502
         504, fact "integer" [] [0I] [] (Some 502)
         505, record ["Identity"; "Version"; "Source"] [506; 507; 508] 502
         506, text "absence" 505; 507, text "1" 505; 508, text "fixture" 505
         600, {fact "quotation" [] [1I] [602] (Some 601) with SourceType = contractType "ScopedCallbackDescriptor"}
         601, {declBinding "during_call" 600 with SourceType = contractType "ScopedCallbackDescriptor"}
         602, {record ["Binding"; "Parameter"] [603; 604] 600 with SourceType = contractType "ScopedCallbackDescriptor"}
         603, text "OptionalControl.receive" 602; 604, text "callback" 602]
        |> List.map (fun (id, item) -> NodeId id, item) |> Map.ofList
    let imported : BoundaryImport =
        {Identity = NodeId 210; Binding = NodeId 217; Scope = NodeId 400; Library = "c"; Symbol = "receive"; CallingConvention = "CDecl"
         DeclarationPath = [NodeId 217]; Parameters = [NodeId 211, BoundaryScalar.Entry(NodeId 220)]; Result = None
         Participants = facts.Keys |> Set.ofSeq; SourceTypes = Map.ofList [NodeId 211, optionType]; DeclarationFacts = facts}
    let receiver : BoundaryCallbackInvocation =
        {Identity = NodeId 220; Import = NodeId 210; Parameter = 0; Formal = NodeId 211; Scope = NodeId 600
         Contract = {Binding = "OptionalControl.receive"; Parameter = 0
                     Signature = {Parameters = [|{Name = "argument"; Type = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 32); PassBy = BAREWire.Descriptors.PassBy.Value}|]
                                  ReturnType = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 32); CallingConvention = BAREWire.Descriptors.CallConv.CDecl}
                     Hypothesis = {Identity = "invoke"; Version = "1"; Source = "fixture"}; Scope = "during_call"}
         Signature = {Parameters = [BoundaryScalar.Integer(32, true)]; Result = Some(BoundaryScalar.Integer(32, true)); CallingConvention = "CDecl"}
         Extent = BoundaryCallbackExtent.DuringCall; Participants = facts.Keys |> Set.ofSeq}
    let absence : BoundaryCallbackAbsence =
        {Quote = NodeId 500; DescriptorBinding = NodeId 501; Record = NodeId 502; Import = NodeId 210; Parameter = 0; Formal = NodeId 211; Invocation = NodeId 220
         Contract = {Binding = "OptionalControl.receive"; Parameter = 0; Hypothesis = {Identity = "absence"; Version = "1"; Source = "fixture"}}
         SourcePath = [NodeId 500; NodeId 502]
         Inputs = [CallbackAbsenceInputRole.Binding, [NodeId 503]; CallbackAbsenceInputRole.Parameter, [NodeId 504]
                   CallbackAbsenceInputRole.Hypothesis, [NodeId 505]; CallbackAbsenceInputRole.HypothesisIdentity, [NodeId 506]
                   CallbackAbsenceInputRole.HypothesisVersion, [NodeId 507]; CallbackAbsenceInputRole.HypothesisSource, [NodeId 508]]
         DeclarationFacts = [500..508] |> List.map (fun id -> NodeId id, facts[NodeId id]) |> Map.ofList}
    let entry : BoundaryClosedEntry =
        {Formation = NodeId 30; Operand = NodeId 402; Declaration = NodeId 401; Implementation = NodeId 10; Formals = [NodeId 41]; Body = NodeId 11
         Lifetime = lifetime; Invocation = NodeId 220; ParameterAdaptations = [None]; ResultAdaptation = None; Registrations = Map.empty
         Transport = Set.ofList [NodeId 30; NodeId 402]
         Participants = Set.union receiver.Participants (Set.ofList [NodeId 30; NodeId 402; NodeId 403; NodeId 10; NodeId 401; NodeId 41; NodeId 11; NodeId 400; NodeId 100; NodeId 220])}
    let whenTrue : BoundaryOptionalEntry =
        {Construction = NodeId 2; CaseOrdinal = 1; Payload = Some(NodeId 30); Formation = Some(NodeId 30)
         Transport = Set.ofList [NodeId 2; NodeId 3]; Obligation = NodeId 404}
    let whenFalse : BoundaryOptionalEntry =
        {Construction = NodeId 4; CaseOrdinal = 0; Payload = None; Formation = None
         Transport = Set.ofList [NodeId 4; NodeId 3]; Obligation = NodeId 405}
    let choice = BoundaryOptionalEntryChoice.Conditional(NodeId 3, NodeId 99, whenTrue, whenFalse)
    let own = accounts[NodeId 3].Sources |> List.map _.Node |> Set.ofList
    let extra = [500..508] |> List.map NodeId |> Set.ofList
    let supportTrue = Set.unionMany [own; whenTrue.Transport; Set.ofList [NodeId 1; NodeId 210; NodeId 201; NodeId 3; NodeId 211; NodeId 2]; imported.Participants; receiver.Participants]
    let supportFalse = Set.unionMany [own; whenFalse.Transport; Set.ofList [NodeId 1; NodeId 210; NodeId 201; NodeId 3; NodeId 211; NodeId 4]; imported.Participants; receiver.Participants; extra]
    let pendingClaim id reasons : ObligationInfo =
        {Id = id; Kind = "foreign-optional-entry-conversion-0"; Logic = ""
         Statement = "The exact source Option selection requires an admitted target boundary conversion."
         Source = "integrity-control"; Refs = []; Body = ObligationBody.Pending reasons}
    let claimTrue = pendingClaim "optional-conditional-some" ["Selected-target optional-entry conversion remains Pending."]
    let claimFalse = pendingClaim "optional-conditional-none" ["Selected-target optional-entry conversion and the foreign nullable-acceptance premise remain Pending."]
    let call : BoundaryCall =
        {Site = NodeId 1; Import = NodeId 210; Callee = NodeId 201; Entry = None; Resource = None
         Arguments = [{Actual = NodeId 3; Formal = NodeId 211; Abi = BoundaryScalar.Entry(NodeId 220); Adaptation = None; OptionalEntry = Some choice; BufferAbsence = None}]
         ErasedUnitArguments = []; Result = None; ResultAdaptation = None
         Participants = Set.unionMany [supportTrue; supportFalse; Set.ofList [NodeId 99; NodeId 404; NodeId 405]]
         SourceTypes = Map.ofList [NodeId 3, optionType]}
    let boundary =
        {baseRevision.Emission.Boundary with
            Imports = Map.ofList [NodeId 210, imported]
            Calls = Map.ofList [NodeId 1, call]
            CallbackInvocations = Map.ofList [NodeId 220, receiver]
            CallbackAbsences = Map.ofList [NodeId 500, absence]
            ClosedEntries = Map.ofList [NodeId 30, entry]}
    let optionRep = ValueRepresentation.Union(["None", []; "Some", [ValueRepresentation.CallableComponent(NodeId 101, ValueRepresentation.Record([], Some([], 0, 1)))]], Some(1, 1, 1))
    let prepared =
        {baseRevision with
            Platform = {Register = Ok 64; Pointer = Ok 64}
            CurrentClaims = Map.ofList [NodeId 404, claimTrue; NodeId 405, claimFalse]
            Obligations = [claimTrue; claimFalse]
            ObligationSources = Map.ofList [NodeId 404, [List.distinct (NodeId 1 :: Set.toList supportTrue)]; NodeId 405, [List.distinct (NodeId 1 :: Set.toList supportFalse)]]
            Codata = {baseRevision.Codata with
                        CallableContracts = callable.Contracts; CallableCarriers = callable.Carriers
                        CallableAggregateSlots = callable.AggregateSlots; CallableAggregateValues = callable.AggregateValues
                        CallableAggregateDependencies = callable.AggregateDependencies
                        FunctionPointers = Map.ofList [NodeId 30, FunctionPointerPlan.Address("callback", NodeId 10)]}
            Emission = {baseRevision.Emission with Callable = callable; Boundary = boundary}}
        |> covered
    let source =
        {prepared.SourceReadings with
            ContextHeaders = prepared.SourceReadings.ContextHeaders.Add(NodeId 400, header)
            Contexts = prepared.SourceReadings.Contexts.Add(NodeId 400, [[]])
            Ports = prepared.SourceReadings.Ports.Add((NodeId 400, OccurrencePort.ModuleDeclaration), header.Ports[OccurrencePort.ModuleDeclaration])}
    let tagCarrier : ScalarCarrier =
        {held.Emission.Numeric.Values[NodeId 3] with
            Site = NodeId 99; SourceType = intType
            Slot = SettledSlot.Integer(64, Some "int"); Range = ValueRange.Bounded(0I, 1I)
            Participants = Set.ofList [NodeId 99; NodeId 3]; Obligations = []}
    let scalar site =
        {held.Emission.Numeric.Values[NodeId 3] with
            Site = NodeId site; SourceType = callbackType; Declaration = None
            Participants = Set.singleton(NodeId site); Obligations = []}
    let numeric = prepared.Emission.Numeric
    {prepared with
        SourceReadings = source
        Emission = {prepared.Emission with
                        Numeric = {numeric with
                                       Values = numeric.Values.Add(NodeId 99, tagCarrier).Add(NodeId 11, scalar 11).Add(NodeId 41, scalar 41)
                                       OccurrenceRepresentations =
                                           numeric.OccurrenceRepresentations
                                               .Add(NodeId 2, Ok optionRep)
                                               .Add(NodeId 3, Ok optionRep)
                                               .Add(NodeId 4, Ok optionRep)
                                               .Add(NodeId 11, Ok(ValueRepresentation.Scalar(SettledSlot.Integer(32, None))))
                                               .Add(NodeId 41, Ok(ValueRepresentation.Scalar(SettledSlot.Integer(32, None))))}}}

[<Theory>]
[<InlineData("valid")>]
[<InlineData("swapped-arms")>]
[<InlineData("duplicate-obligation")>]
[<InlineData("missing-select")>]
[<InlineData("select-true")>]
[<InlineData("select-false")>]
[<InlineData("transport")>]
let ``conditional optional callback retains exact arm order select row and transport`` defect =
    let held = conditionalOptionalCallback ()
    let boundary = held.Emission.Boundary
    let call = boundary.Calls[NodeId 1]
    let operand = call.Arguments.Head
    let choice =
        match operand.OptionalEntry.Value with
        | BoundaryOptionalEntryChoice.Conditional(selection, tag, whenTrue, whenFalse) ->
            let left, right =
                match defect with
                | "swapped-arms" -> whenFalse, whenTrue
                | "duplicate-obligation" -> whenTrue, {whenFalse with Obligation = whenTrue.Obligation}
                | "transport" -> {whenTrue with Transport = Set.empty}, whenFalse
                | _ -> whenTrue, whenFalse
            BoundaryOptionalEntryChoice.Conditional(selection, tag, left, right)
        | _ -> failwith "Expected a conditional optional callback."
    let callable = held.Emission.Callable
    let selected = callable.AggregateValues[NodeId 3].Head
    let selected =
        match defect with
        | "select-true" -> {selected with Selection = selected.Selection |> Option.map (fun row -> {row with WhenTrue = NodeId 4})}
        | "select-false" -> {selected with Selection = selected.Selection |> Option.map (fun row -> {row with WhenFalse = NodeId 3})}
        | _ -> selected
    let values = if defect = "missing-select" then [] else [selected]
    let account3 = callable.AggregateDependencies[NodeId 3]
    let accountValues =
        if defect = "missing-select" then account3.Values |> List.filter (fun row -> row.Operation <> CallableAggregateOperation.Select)
        else account3.Values |> List.map (fun row -> if row.Operation = CallableAggregateOperation.Select then selected else row)
    let changedCallable =
        {callable with
            AggregateValues = callable.AggregateValues.Add(NodeId 3, values)
            AggregateDependencies = callable.AggregateDependencies.Add(NodeId 3, {account3 with Values = accountValues})}
    let changed =
        {held with Emission = {held.Emission with
                                  Boundary = {boundary with Calls = boundary.Calls.Add(call.Site, {call with Arguments = {operand with OptionalEntry = Some choice} :: call.Arguments.Tail})}
                                  Callable = changedCallable}}
    let violations = Integrity.check changed
    let selectionViolation (v: IntegrityViolation) =
        v.Part = "Emission.Boundary.Calls.OptionalEntry" && v.Node = Some(NodeId 1) &&
        v.Reason = "The conditional optional entry differs from its exact source selection, option-tag projection, actual transport, arm order or claim identities."
    if defect = "valid" then Assert.Empty(violations)
    else Assert.Contains(violations, selectionViolation)

[<Theory>]
[<InlineData(false, false)>]
[<InlineData(false, true)>]
[<InlineData(true, false)>]
[<InlineData(true, true)>]
let ``finite optional claims reject detached and duplicate operand owners`` absent duplicate =
    let held = conditionalOptionalCallback ()
    let boundary = held.Emission.Boundary
    let call = boundary.Calls[NodeId 1]
    let original = held.CurrentClaims[NodeId 404]
    let body =
        if absent then ObligationBody.OptionalEntryAbsenceArgumentConversion(absentPlan None)
        else ObligationBody.OptionalEntryArgumentConversion(presentPlan None)
    let claim = {original with Body = body}
    let operand = call.Arguments.Head
    let optional =
        match operand.OptionalEntry.Value with
        | BoundaryOptionalEntryChoice.Conditional(selection, tag, whenTrue, whenFalse) ->
            if duplicate then BoundaryOptionalEntryChoice.Conditional(selection, tag, whenTrue, {whenFalse with Obligation = whenTrue.Obligation})
            else BoundaryOptionalEntryChoice.Conditional(selection, tag, {whenTrue with Obligation = NodeId 405}, whenFalse)
        | _ -> failwith "Expected a conditional optional callback."
    let changed =
        {held with CurrentClaims = held.CurrentClaims.Add(NodeId 404, claim)
                   Obligations = held.Obligations |> List.map (fun row -> if row.Id = original.Id then claim else row)
                   Emission = {held.Emission with Boundary = {boundary with Calls = boundary.Calls.Add(call.Site, {call with Arguments = {operand with OptionalEntry = Some optional} :: call.Arguments.Tail})}}}
    let violation = within "CurrentClaims.OptionalEntry" (Integrity.check changed)
    Assert.Equal(Some(NodeId 404), violation.Node)
    Assert.Equal("A finite optional-entry source plan requires one exact current per-call operand owner.", violation.Reason)

let private stackCheckedText () =
    let held = snapshotFacts
    let memory = held.Emission.Memory
    let view =
        match memory.Operations[NodeId 1] with
        | MemoryWitnessOperation.StringView row -> row
        | _ -> failwith "Expected the snapshot fixture's string view."
    let allocation =
        match memory.Operations[NodeId 11] with
        | MemoryWitnessOperation.ArrayAllocation row -> row
        | _ -> failwith "Expected the snapshot fixture's allocation."
    let construction : CheckedStringConstruction =
        { Owner = NodeId 21; Input = NodeId 1; Snapshot = NodeId 6; Length = NodeId 5
          Validation = NodeId 24; Decision = NodeId 26; Text = NodeId 20
          Success = NodeId 22; Failure = NodeId 23; Retirement = NodeId 25
          Validator = "RFC3629-v1"; Returned = None }
    let unionType = TypeIdentity.Application(
        {Declaration = {Module = []; Name = "CheckedTextControl"}; Parameters = []; NativeKind = None}, [])
    let intrinsic id operation =
        let info : IntrinsicInfo =
            {Module = IntrinsicModule.String; Operation = operation
             Category = IntrinsicCategory.StringOp; FullName = "String." + operation}
        node id (SemanticKind.Intrinsic info) []
    let nodes =
        [node 20 (SemanticKind.Application(NodeId 29, [NodeId 6])) [29;6]
         node 21 (SemanticKind.Sequential [NodeId 26]) [26]
         {node 22 (SemanticKind.DUConstruct("ValueSome", 1, Some(NodeId 20), None)) [20] with Type = unionType}
         {node 23 (SemanticKind.DUConstruct("ValueNone", 0, None, None)) [] with Type = unionType}
         node 24 (SemanticKind.Application(NodeId 28, [NodeId 6])) [28;6]
         node 25 (SemanticKind.Application(NodeId 31, [NodeId 6])) [31;6]
         node 26 (SemanticKind.IfThenElse(NodeId 24, NodeId 22, Some(NodeId 27))) [24;22;27]
         node 27 (SemanticKind.Sequential [NodeId 25; NodeId 23]) [25;23]
         intrinsic 28 "validateUtf8"; intrinsic 29 "fromBytes"; intrinsic 31 "retireSnapshot"
         node 30 (SemanticKind.Lambda([], NodeId 21, [], Some "checked", LambdaContext.RegularClosure)) [21]]
    let residence = MemoryResidence.Stack(NodeId 30, NodeId 5521)
    let allocation = {allocation with Residence = residence; Participants = allocation.Participants.Add(NodeId 901)}
    let storage = MemoryCheckedSnapshotStorage.Allocated allocation
    let copy = memory.ArrayCopies[NodeId 6]
    let stored site layout capacity : MemoryConstructedValueWitness =
        {Site = NodeId site; Owner = construction.Owner; SourceType = unionType; Residence = residence
         Uses = Set.singleton(NodeId site); Construction = construction; Platform = NodeId 8000
         Layout = NodeId layout; Capacity = NodeId capacity}
    let operations =
        [NodeId 11, MemoryWitnessOperation.ArrayAllocation allocation
         NodeId 20, MemoryWitnessOperation.StringView
             {view with
                 Site = NodeId 20; Source = NodeId 6; Owner = construction.Owner
                 Direction = MemoryStringViewDirection.FromBytes; Checked = Some construction}
         NodeId 22, MemoryWitnessOperation.ConstructedValue(stored 22 902 903)
         NodeId 23, MemoryWitnessOperation.ConstructedValue(stored 23 904 905)
         NodeId 24, MemoryWitnessOperation.Utf8Validation {Site = NodeId 24; Construction = construction; Copy = copy; Storage = storage; SourceCarrier = view.SourceCarrier}
         NodeId 25, MemoryWitnessOperation.SnapshotRetirement {Site = NodeId 25; Construction = construction; Storage = storage}]
        |> Map.ofList
    let claims =
        [901, ObligationBody.CapacityFits(16L, 128L), [11;30;5521]
         902, ObligationBody.ContinuationLayout([0,16,8],16,8), [22;8000;30;5521]
         903, ObligationBody.CapacityFits(16L,128L), [22;8000;30;5521]
         904, ObligationBody.ContinuationLayout([0,16,8],16,8), [23;8000;30;5521]
         905, ObligationBody.CapacityFits(16L,128L), [23;8000;30;5521]]
        |> List.map (fun (id, body, sources) ->
            NodeId id, {Id = sprintf "checked-%d" id; Kind = "checked-text-control"; Logic = "QF_LIA"
                        Statement = "The stored checked text layout fits its declared space."; Source = "fixture"; Refs = []; Body = body},
            [sources |> List.map NodeId])
    let numeric = held.Emission.Numeric
    {held with
        Nodes = nodes |> List.fold (fun rows node -> Map.add node.Id node rows) held.Nodes
        CurrentClaims = claims |> List.fold (fun rows (id, claim, _) -> Map.add id claim rows) held.CurrentClaims
        Obligations = held.Obligations @ (claims |> List.map (fun (_, claim, _) -> claim))
        ObligationSources = claims |> List.fold (fun rows (id, _, sources) -> Map.add id sources rows) held.ObligationSources
        Emission = {held.Emission with
                        Memory = {memory with Operations = operations; Required = Set.ofList [NodeId 11; NodeId 20]}
                        Numeric = {numeric with
                                       SourceTypes = nodes |> List.fold (fun rows node -> Map.add node.Id node.Type rows) numeric.SourceTypes
                                       Layouts = numeric.Layouts.Add(unionType, SettledLayout.Union(["ValueNone",None; "ValueSome",Some SettledSlot.Bool], Some 8, Some 16, Some 8))
                                       OccurrenceRepresentations = numeric.OccurrenceRepresentations.Add(NodeId 6, Ok view.SourceCarrier).Add(NodeId 20, Ok view.ResultCarrier)}}}
    |> covered

[<Fact>]
let ``stack checked text retains validation private snapshot storage and retirement`` () =
    Assert.Empty(Integrity.check (stackCheckedText ()))

[<Theory>]
[<InlineData("validator", "validator/view/retirement")>]
[<InlineData("retire-snapshot", "validator/view/retirement")>]
[<InlineData("cleanup-order", "discard-before-ValueNone")>]
[<InlineData("capacity", "capacity proof")>]
let ``stack checked text rejects validator retirement ordering and capacity defects`` defect (reason: string) =
    let held = stackCheckedText ()
    let memory = held.Emission.Memory
    let changeConstruction (row: CheckedStringConstruction) = {row with Validator = "other-validator"}
    let changed =
        match defect with
        | "validator" ->
            let operations = memory.Operations |> Map.map (fun _ operation ->
                match operation with
                | MemoryWitnessOperation.StringView row -> MemoryWitnessOperation.StringView {row with Checked = row.Checked |> Option.map changeConstruction}
                | MemoryWitnessOperation.Utf8Validation row -> MemoryWitnessOperation.Utf8Validation {row with Construction = changeConstruction row.Construction}
                | MemoryWitnessOperation.ConstructedValue row -> MemoryWitnessOperation.ConstructedValue {row with Construction = changeConstruction row.Construction}
                | MemoryWitnessOperation.SnapshotRetirement row -> MemoryWitnessOperation.SnapshotRetirement {row with Construction = changeConstruction row.Construction}
                | _ -> operation)
            {held with Emission = {held.Emission with Memory = {memory with Operations = operations}}}
        | "retire-snapshot" ->
            {held with Nodes = held.Nodes.Add(NodeId 25, {held.Nodes[NodeId 25] with Kind = SemanticKind.Application(NodeId 31, [NodeId 1]); Children = [NodeId 31; NodeId 1]})}
        | "cleanup-order" ->
            {held with Nodes = held.Nodes.Add(NodeId 27, {held.Nodes[NodeId 27] with Kind = SemanticKind.Sequential [NodeId 23; NodeId 25]; Children = [NodeId 23; NodeId 25]})}
        | _ ->
            let old = held.CurrentClaims[NodeId 903]
            let claim = {old with Body = ObligationBody.CapacityFits(16L, 8L)}
            {held with CurrentClaims = held.CurrentClaims.Add(NodeId 903, claim)
                       Obligations = held.Obligations |> List.map (fun row -> if row.Id = old.Id then claim else row)}
    Assert.Contains(Integrity.check changed, fun v ->
        v.Part.StartsWith("Emission.Memory.Operations.") && v.Reason.Contains reason)

let private returnedCheckedText empty =
    let held = stackCheckedText ()
    let memory = held.Emission.Memory
    let validation =
        match memory.Operations[NodeId 24] with
        | MemoryWitnessOperation.Utf8Validation row -> row
        | _ -> failwith "Expected a checked validator."
    let allocation =
        match validation.Storage with
        | MemoryCheckedSnapshotStorage.Allocated row -> row
        | _ -> failwith "Expected an allocated snapshot."
    let unionType = held.Nodes[NodeId 22].Type
    let lifetime : MemoryCheckedResultLifetime =
        {Application = NodeId 40; Callee = NodeId 41; Declaration = NodeId 42; Implementation = NodeId 30
         Argument = NodeId 1; Formal = NodeId 43; Body = NodeId 21; Caller = NodeId 44; Actual = NodeId 45
         Elimination = NodeId 46; SomeUse = NodeId 49; NoneUse = NodeId 65
         SomeBackingRetirement = NodeId 53; SomeCarrierRetirement = NodeId 54; NoneCarrierRetirement = NodeId 55
         Uses = [NodeId 40; NodeId 45]; Policy = optionalPlanRetirement.Policy
         Platform = NodeId 8000; Space = NodeId 5521; MaximumLiveBytes = if empty then 16L else 32L
         Capacity = NodeId 906}
    let construction = {validation.Construction with Returned = Some lifetime}
    let residence = MemoryResidence.Heap(lifetime.Application, lifetime.Space)
    let count = if empty then {validation.Copy.CountCarrier with Range = ValueRange.Bounded(0I,0I)} else validation.Copy.CountCarrier
    let copy = {validation.Copy with CountCarrier = count}
    let allocation = {allocation with Residence = residence}
    let emptyStorage : MemoryEmptySnapshotWitness =
        {Site = NodeId 11; Snapshot = NodeId 6; Owner = NodeId 21; Count = NodeId 5
         SourceType = held.Nodes[NodeId 11].Type; Declaration = NodeId 64}
    let storage = if empty then MemoryCheckedSnapshotStorage.Empty emptyStorage else MemoryCheckedSnapshotStorage.Allocated allocation
    let arm pattern body : CaseArm = {Pattern = pattern; Bindings = []; Guard = None; Body = NodeId body}
    let somePattern = Pattern.Union("ValueSome", 1, Some Pattern.Wildcard, unionType)
    let nonePattern = Pattern.Union("ValueNone", 0, None, unionType)
    let intrinsic id operation =
        let info : IntrinsicInfo =
            {Module = IntrinsicModule.String; Operation = operation; Category = IntrinsicCategory.StringOp; FullName = "String." + operation}
        node id (SemanticKind.Intrinsic info) []
    let nodes =
        [node 30 (SemanticKind.Lambda(["input", unitType, NodeId 43], NodeId 21, [], Some "checked", LambdaContext.RegularClosure)) [43;21]
         node 40 (SemanticKind.Application(NodeId 41, [NodeId 1])) [41;1]
         node 41 (SemanticKind.VarRef("checked", Some(NodeId 42))) []
         node 42 (SemanticKind.Binding("checked", false, false, None)) [30]
         node 43 (SemanticKind.PatternBinding "input") []
         node 44 (SemanticKind.Lambda([], NodeId 46, [], Some "caller", LambdaContext.RegularClosure)) [46]
         node 45 (SemanticKind.VarRef("result", Some(NodeId 68))) []
         node 68 (SemanticKind.Binding("result", false, false, None)) [40]
         node 46 (SemanticKind.CaseElimination(NodeId 45, [arm somePattern 47; arm Pattern.Wildcard 60])) [45;47;60]
         node 47 (SemanticKind.Sequential [NodeId 48;NodeId 53;NodeId 54;NodeId 52]) [48;53;54;52]
         node 48 (SemanticKind.Binding("length", false, false, None)) [49]
         node 49 (SemanticKind.Application(NodeId 50, [NodeId 51])) [50;51]
         intrinsic 50 "length"
         node 51 (SemanticKind.DUEliminate(NodeId 45, 1, "ValueSome", unionType)) [45]
         node 52 (SemanticKind.VarRef("length", Some(NodeId 48))) []
         node 53 (SemanticKind.Application(NodeId 56, [NodeId 51])) [56;51]
         node 54 (SemanticKind.Application(NodeId 57, [NodeId 45])) [57;45]
         node 55 (SemanticKind.Application(NodeId 57, [NodeId 45])) [57;45]
         intrinsic 56 "retireCheckedBacking"; intrinsic 57 "retireCheckedCarrier"
         node 58 (SemanticKind.Literal NativeLiteral.Unit) []
         node 59 (SemanticKind.CaseElimination(NodeId 45, [arm nonePattern 66; arm Pattern.Wildcard 67])) [45;66;67]
         node 60 (SemanticKind.Sequential [NodeId 58;NodeId 61]) [58;61]
         node 61 (SemanticKind.CaseElimination(NodeId 45, [arm nonePattern 62])) [45;62]
         node 62 (SemanticKind.Sequential [NodeId 63;NodeId 55;NodeId 64]) [63;55;64]
         node 63 (SemanticKind.Binding("none", false, false, None)) [65]
         node 64 (SemanticKind.VarRef("none", Some(NodeId 63))) []
         node 65 (SemanticKind.Literal NativeLiteral.Unit) []
         node 66 (SemanticKind.Literal(NativeLiteral.Bool true)) []
         node 67 (SemanticKind.Literal(NativeLiteral.Bool false)) []]
    let operations = memory.Operations |> Map.map (fun _ operation ->
        match operation with
        | MemoryWitnessOperation.ArrayAllocation _ ->
            if empty then MemoryWitnessOperation.EmptySnapshot emptyStorage else MemoryWitnessOperation.ArrayAllocation allocation
        | MemoryWitnessOperation.StringView row -> MemoryWitnessOperation.StringView {row with Checked = Some construction; Extent = count}
        | MemoryWitnessOperation.Utf8Validation row -> MemoryWitnessOperation.Utf8Validation {row with Construction = construction; Storage = storage; Copy = copy}
        | MemoryWitnessOperation.SnapshotRetirement row -> MemoryWitnessOperation.SnapshotRetirement {row with Construction = construction; Storage = storage}
        | MemoryWitnessOperation.ConstructedValue row -> MemoryWitnessOperation.ConstructedValue {row with Construction = construction; Residence = residence}
        | _ -> operation)
    let cleanup site value target : MemoryWitnessOperation =
        MemoryWitnessOperation.CheckedResultRetirement {Site = NodeId site; Value = NodeId value; Target = target; Construction = construction}
    let operations =
        operations.Add(NodeId 53, cleanup 53 51 (if empty then MemoryCheckedRetirementTarget.EmptyBacking else MemoryCheckedRetirementTarget.Backing))
                  .Add(NodeId 54, cleanup 54 45 MemoryCheckedRetirementTarget.Carrier)
                  .Add(NodeId 55, cleanup 55 45 MemoryCheckedRetirementTarget.Carrier)
    let requirement : RequirementWitness =
        {Site = NodeId 58; Condition = NodeId 59; Diagnostic = "Expected ValueNone"; Frontier = NodeId 60
         Continuation = NodeId 61; PatternTest = Some(NodeId 59); Participants = [NodeId 60;NodeId 58;NodeId 59;NodeId 61]}
    let capacity =
        {held.CurrentClaims[NodeId 903] with Id = "checked-return-capacity"; Body = ObligationBody.CapacityFits(lifetime.MaximumLiveBytes,128L)}
    let sources = held.ObligationSources |> Map.map (fun id groups ->
        if List.contains id [NodeId 901;NodeId 902;NodeId 903;NodeId 904;NodeId 905] then
            groups |> List.map (List.map (fun node -> if node = NodeId 30 then NodeId 40 else node))
        else groups)
    {held with
        Nodes = nodes |> List.fold (fun rows node -> Map.add node.Id node rows) held.Nodes
        CurrentClaims = held.CurrentClaims.Add(NodeId 906, capacity)
        Obligations = held.Obligations @ [capacity]
        ObligationSources = sources.Add(NodeId 906, [[NodeId 40;NodeId 8000;NodeId 5521]])
        Emission =
            {held.Emission with
                Memory = {memory with Operations = operations; ArrayCopies = memory.ArrayCopies.Add(NodeId 6, copy)}
                Numeric = {held.Emission.Numeric with Values = held.Emission.Numeric.Values.Add(NodeId 5, count)}
                Callable = {held.Emission.Callable with AliasTargets = held.Emission.Callable.AliasTargets.Add(NodeId 45, NodeId 40)}
                Storage = {held.Emission.Storage with
                               Requirements = held.Emission.Storage.Requirements.Add(NodeId 58, requirement)
                               PatternRequirements = held.Emission.Storage.PatternRequirements.Add(NodeId 61, NodeId 58)}}}
    |> covered
    |> fun revision ->
        {revision with Emission = {revision.Emission with
                                      Callable = {revision.Emission.Callable with AliasTargets = revision.Emission.Callable.AliasTargets.Add(NodeId 45,NodeId 40)}}}

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``returned checked text retains heap or empty snapshot and complete caller cleanup`` empty =
    Assert.Empty(Integrity.check (returnedCheckedText empty))

[<Theory>]
[<InlineData("some-order", "scalar-before-cleanup ordering on its exact Some arm")>]
[<InlineData("none-order", "scalar-before-cleanup ordering on its exact None arm")>]
[<InlineData("capacity", "combined live-byte capacity claim")>]
[<InlineData("residence", "allocated or affirmative empty snapshot")>]
let ``returned checked text rejects cleanup capacity and residence defects`` defect (reason: string) =
    let held = returnedCheckedText false
    let changed =
        match defect with
        | "some-order" | "none-order" ->
            let site, order = if defect = "some-order" then 47, [53;48;54;52] else 62, [55;63;64]
            let ids = List.map NodeId order
            {held with Nodes = held.Nodes.Add(NodeId site, {held.Nodes[NodeId site] with Kind = SemanticKind.Sequential ids; Children = ids})}
        | "capacity" ->
            let old = held.CurrentClaims[NodeId 906]
            let claim = {old with Body = ObligationBody.CapacityFits(32L, 8L)}
            {held with CurrentClaims = held.CurrentClaims.Add(NodeId 906, claim)
                       Obligations = held.Obligations |> List.map (fun row -> if row.Id = old.Id then claim else row)}
        | _ ->
            let memory = held.Emission.Memory
            let operation =
                match memory.Operations[NodeId 11] with
                | MemoryWitnessOperation.ArrayAllocation row -> MemoryWitnessOperation.ArrayAllocation {row with Residence = MemoryResidence.Stack(NodeId 30,NodeId 5521)}
                | _ -> failwith "Expected the returned snapshot allocation."
            {held with Emission = {held.Emission with Memory = {memory with Operations = memory.Operations.Add(NodeId 11, operation)}}}
    let expectedNode = if defect = "none-order" then NodeId 61 else NodeId 21
    Assert.Contains(Integrity.check changed, fun v ->
        v.Part.EndsWith(".Returned") && v.Node = Some expectedNode && v.Reason.Contains reason)

// Declaration quotations are stored source facts, including their exact parents.
let private controlFact form text numbers references parent : BoundaryDeclarationFact =
    {Form = form; Text = text; Numbers = numbers; References = List.map NodeId references
     Children = List.map NodeId references; Parent = Option.map NodeId parent; SourceType = unitType}

let private controlClaim id kind body : ObligationInfo =
    {Id = id; Kind = kind; Logic = "QF_LIA"; Statement = "Current source correspondence."
     Source = "integrity-control"; Refs = []; Body = body}

let private writableBufferControl relational =
    let held = snapshotFacts
    let basis = boundaryCalleeFacts.Emission.Boundary
    let integerType name kind =
        TypeIdentity.Application({Declaration = {Module = []; Name = name}; Parameters = []; NativeKind = Some kind}, [])
    let byteType = integerType "uint8" (NTUKind.NTUuint(NTUWidth.Fixed 8))
    let countType = integerType "uint64" (NTUKind.NTUuint(NTUWidth.Fixed 64))
    let resultType = integerType "int64" (NTUKind.NTUint(NTUWidth.Fixed 64))
    let arrayType = TypeIdentity.Application({Declaration = {Module = []; Name = "array"}; Parameters = [TypeParamKind.Type]; NativeKind = None}, [byteType])
    let header = boundaryCalleeFacts.SourceReadings.ContextHeaders[NodeId 50]
    let bindingName = header.Name + ".fill"
    let record fields ids parent = controlFact "record" fields [] ids (Some parent)
    let binding name child = controlFact "binding" [name] [0I;0I] [child] (Some 50)
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let number value parent = controlFact "integer" [] [value] [] (Some parent)
    let case name refs parent = controlFact "case" [name] [] refs (Some parent)
    let facts =
        [2, binding "fill" 1003
         1003, controlFact "lambda" ["fill";"buffer";"count"] [2I;0I;0I] [1004;1005;1006] (Some 2)
         1004, {controlFact "formal" ["buffer"] [] [] (Some 1003) with SourceType = arrayType}
         1005, {controlFact "formal" ["count"] [] [] (Some 1003) with SourceType = countType}
         1006, controlFact "unit" [] [] [] (Some 1003)
         1073, binding "fillDescriptor" 1072
         1072, controlFact "quotation" [] [] [72] (Some 1073)
         72, record ["Parameters";"CName"] [1010;1020] 1072
         1010, controlFact "array" [] [] [1011;1012] (Some 72)
         1011, record ["Type";"PassBy"] [1013;1016] 1010
         1012, record ["Type";"PassBy"] [1017;1019] 1010
         1013, case "Integer" [1014] 1011
         1014, controlFact "tuple" [] [] [1015;1018] (Some 1013)
         1015, case "Unsigned" [] 1014
         1018, number 8I 1014
         1016, case "Reference" [] 1011
         1017, case "Integer" [1021] 1012
         1021, controlFact "tuple" [] [] [1022;1023] (Some 1017)
         1022, case "Unsigned" [] 1021
         1023, number 64I 1021
         1019, case "Value" [] 1012
         1020, text "fill" 72
         1101, binding "fillWritableBufferDescriptor" 1100
         1100, controlFact "quotation" [] [] [1102] (Some 1101)
         1102, record ["Binding";"Parameter";"CountParameter";"Hypothesis"] [1103;1104;1105;1106] 1100
         1103, text bindingName 1102
         1104, number 0I 1102
         1105, number 1I 1102
         1106, record ["Identity";"Version";"Source"] [1107;1108;1109] 1102
         1107, text "writable-fill" 1106
         1108, text "1" 1106
         1109, text "fixture" 1106
         1200, record ["Name";"Family";"Bits"] [1201;1202;1203] 72
         1201, text "uint8" 1200
         1202, text "uint" 1200
         1203, number 8I 1200]
        |> List.map (fun (id, fact) -> NodeId id, fact) |> Map.ofList
    let declaration : BoundaryWritableBufferDeclaration =
        {Identity = NodeId 1100; Declaration = NodeId 2; Body = NodeId 1006
         Formals = [NodeId 1004;NodeId 1005]; Descriptor = NodeId 72; Parameter = 0; CountParameter = 1
         BufferFormal = NodeId 1004; CountFormal = NodeId 1005
         Contract = {Binding = bindingName; Parameter = 0; CountParameter = 1
                     Hypothesis = {Identity = "writable-fill"; Version = "1"; Source = "fixture"}}
         DeclarationFacts = facts; Participants = facts.Keys |> Set.ofSeq}
    let imported =
        {basis.Imports[NodeId 72] with
            Symbol = "fill"; Parameters = [NodeId 1004, BoundaryScalar.WritableBytes(NodeId 1100);NodeId 1005, BoundaryScalar.Integer(64,false)]
            Result = if relational then Some(BoundaryScalar.Integer(64,true)) else None
            DeclarationFacts = facts; Participants = declaration.Participants
            SourceTypes = Map.ofList [NodeId 1004,arrayType;NodeId 1005,countType;NodeId 1,(if relational then resultType else unitType)]}
    let call =
        {basis.Calls[NodeId 1] with
            Arguments = [{Actual = NodeId 3; Formal = NodeId 1004; Abi = BoundaryScalar.WritableBytes(NodeId 1100); Adaptation = None; OptionalEntry = None; BufferAbsence = None}
                         {Actual = NodeId 4; Formal = NodeId 1005; Abi = BoundaryScalar.Integer(64,false); Adaptation = None; OptionalEntry = None; BufferAbsence = None}]
            Result = imported.Result; SourceTypes = imported.SourceTypes; Participants = declaration.Participants}
    let allocation =
        match held.Emission.Memory.Operations[NodeId 11] with
        | MemoryWitnessOperation.ArrayAllocation row -> row
        | _ -> failwith "Expected the original allocation."
    let capacity = {allocation.CountCarrier with Range = ValueRange.Bounded(4I,4I); Obligations = []}
    let allocation =
        {allocation with Element = SettledSlot.Integer(8,Some "uint8"); ElementBytes = 1; Alignment = 1
                         MinimumCount = 4I; MaximumCount = 4I; CountCarrier = capacity}
    let count =
        {held.Emission.Numeric.Values[NodeId 4] with
            Slot = SettledSlot.Integer(64,Some "uint64"); SourceType = countType
            Range = ValueRange.Bounded(4I,4I); Obligations = []}
    let result =
        {held.Emission.Numeric.Values[NodeId 1] with
            Slot = SettledSlot.Integer(64,Some "int64"); SourceType = resultType
            Range = ValueRange.Bounded(-1I,4I); Obligations = []}
    let hypothesis : ForeignResultHypothesis =
        {Quote = NodeId 1106; Declaration = NodeId 2; Identity = "fill-result"; Version = "1"; Source = "fixture"
         Lower = ForeignResultBound.Constant -1I; Upper = ForeignResultBound.Argument 1}
    let application : ForeignResultApplication =
        {Declaration = NodeId 2; Call = NodeId 1; Context = []; Hypothesis = Some hypothesis
         Arguments = [{Index = 0; Node = NodeId 3; Enclosure = ValueRange.Unbounded};{Index = 1; Node = NodeId 4; Enclosure = count.Range}]}
    let p role ordinal id : Participant = {Role = role; Ordinal = ordinal; Group = NodeId 1; Node = NodeId id}
    let participants =
        [p ParticipantRole.ForeignResultDeclaration 0 2; p ParticipantRole.ForeignResultCall 0 1
         p ParticipantRole.ForeignResultHypothesis 0 1106; p ParticipantRole.ForeignResultActual 0 3; p ParticipantRole.ForeignResultActual 1 4
         p ParticipantRole.ForeignResultAbi 0 72; p ParticipantRole.ForeignResultDestination 0 64
         p ParticipantRole.ForeignResultAbi 1 72; p ParticipantRole.ForeignResultDestination 1 64]
    let resultClaims =
        if not relational then [] else
        [ForeignResultProofRole.LogicalCoverage,NodeId 941; ForeignResultProofRole.AbiNarrowing,NodeId 942]
        |> List.map (fun (role,id) ->
            let model : ForeignResultCoverageModel =
                {Application = application; Role = role; ResultRange = result.Range; Destination = ValueRange.Bounded(-(1I<<<63),(1I<<<63)-1I)
                 DestinationDeclaration = Some(NodeId 64); Abi = Some(NodeId 72); AbiRange = ValueRange.Bounded(-(1I<<<63),(1I<<<63)-1I)
                 AbiIdentity = Some "fill-abi-1"; DestinationIdentity = Some "fill-result-1"}
            id, controlClaim (sprintf "fill-%A" role) "foreign-result-coverage" (ObligationBody.ForeignResultCoverage model))
    let resultUse : ForeignResultUse =
        {Application = application; Participants = ParticipantEvidence.Established participants
         Claims = [ForeignResultProofRole.LogicalCoverage,NodeId 941; ForeignResultProofRole.AbiNarrowing,NodeId 942]}
    let support = [NodeId 1;NodeId 1100;NodeId 3;NodeId 4;NodeId 11;NodeId 5;NodeId 1200]
    let proof role body =
        {controlClaim ("fill-"+role) ("foreign-writable-buffer-"+role) body with Refs = ["writable-fill";"1";"fixture"]}
    let claims =
        [NodeId 931,proof "count" (ObligationBody.IntegerRepresentationCoverage(4I,4I,0I,4I))
         NodeId 932,proof "storage" (ObligationBody.IntegerRepresentationCoverage(0I,255I,0I,255I))] @ resultClaims
    let use' : BoundaryWritableBufferUse =
        {Call = NodeId 1; Declaration = NodeId 1100; Parameter = 0; CountParameter = 1; Buffer = NodeId 3; Count = NodeId 4
         Allocation = NodeId 11; Capacity = NodeId 5; ByteFormat = NodeId 1200; CountCoverage = NodeId 931; StorageCoverage = NodeId 932
         Participants = Set.ofList (support @ List.map fst claims @ (if relational then List.map (fun (p: Participant) -> p.Node) participants else []))}
    let nodes =
        [ {held.Nodes[NodeId 1] with Type = if relational then resultType else unitType}
          {node 3 (SemanticKind.VarRef("buffer",Some(NodeId 1300))) [] with Type = arrayType}
          {node 4 (SemanticKind.Literal(NativeLiteral.UInt(4UL,NTUKind.NTUuint(NTUWidth.Fixed 64)))) [] with Type = countType}
          {node 11 (SemanticKind.ArrayAllocate(NodeId 5)) [5] with Type = arrayType}
          {node 1300 (SemanticKind.Binding("buffer",false,false,None)) [1301] with Type = arrayType}
          {node 1301 (SemanticKind.TypeAnnotation(NodeId 11,arrayType)) [11] with Type = arrayType}]
    let numeric = held.Emission.Numeric
    let values = numeric.Values.Remove(NodeId 3).Remove(NodeId 1).Add(NodeId 4,count).Add(NodeId 5,capacity)
    let memory = held.Emission.Memory
    {held with
        Nodes = nodes |> List.fold (fun rows node -> Map.add node.Id node rows) held.Nodes
        CurrentClaims = claims |> List.fold (fun rows (id,claim) -> Map.add id claim rows) held.CurrentClaims
        Obligations = held.Obligations @ List.map snd claims
        ObligationSources = claims |> List.fold (fun rows (id,_) -> Map.add id [if id=NodeId 931 || id=NodeId 932 then support else List.map (fun (p: Participant) -> p.Node) participants] rows) held.ObligationSources
        SourceReadings = {held.SourceReadings with
                              ContextHeaders = held.SourceReadings.ContextHeaders.Add(NodeId 50,header)
                              Contexts = held.SourceReadings.Contexts.Add(NodeId 50,[[]])
                              Ports = held.SourceReadings.Ports.Add((NodeId 50,OccurrencePort.ModuleDeclaration),header.Ports[OccurrencePort.ModuleDeclaration])}
        Emission =
            {held.Emission with
                Boundary = {basis with Imports = Map.ofList [NodeId 72,imported]; Calls = Map.ofList [NodeId 1,call]
                                       WritableBufferDeclarations = Map.ofList [NodeId 1100,declaration]
                                       WritableBufferUses = Map.ofList [(NodeId 1,0),use']
                                       ResultHypotheses = if relational then [hypothesis] else []}
                Numeric = {numeric with Operations = Map.empty; OperationRequired = Set.empty
                                        ResultSites = if relational then Set.singleton(NodeId 1) else Set.empty
                                        Required = Set.ofList (if relational then [NodeId 1;NodeId 4;NodeId 5] else [NodeId 4;NodeId 5])
                                        Values = if relational then values.Add(NodeId 1,result) else values
                                        Elements = numeric.Elements.Add(NodeId 3,allocation.Element)
                                        ForeignResultUses = if relational then [resultUse] else []}
                Memory = {memory with Operations = Map.ofList [NodeId 11,MemoryWitnessOperation.ArrayAllocation allocation]
                                      Required = Set.singleton(NodeId 11)
                                      ArrayCopies = memory.ArrayCopies.Add(NodeId 6,{memory.ArrayCopies[NodeId 6] with CountCarrier = capacity})}}}
    |> covered
    |> fun revision ->
        let source =
            {revision.SourceReadings with
                ContextHeaders = revision.SourceReadings.ContextHeaders.Add(NodeId 50,header)
                Contexts = revision.SourceReadings.Contexts.Add(NodeId 50,[[]])
                Ports = revision.SourceReadings.Ports.Add((NodeId 50,OccurrencePort.ModuleDeclaration),header.Ports[OccurrencePort.ModuleDeclaration])}
        {revision with SourceReadings = source}

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``writable buffers retain fixed storage and exact nonrelational or relational accounts`` relational =
    Assert.Empty(Integrity.check (writableBufferControl relational))

[<Theory>]
[<InlineData("quote", "WritableBufferDeclarations.Contract", "immutable quotation")>]
[<InlineData("sibling", "WritableBufferDeclarations.Declaration", "sibling FunctionDescriptor")>]
[<InlineData("reference", "WritableBufferDeclarations.Element", "unsigned-8 Reference")>]
[<InlineData("signed-byte", "WritableBufferDeclarations.Element", "unsigned-8 Reference")>]
[<InlineData("byte-width", "WritableBufferDeclarations.Element", "unsigned-8 Reference")>]
[<InlineData("alias", "WritableBufferUses.Storage", "alias lineage")>]
[<InlineData("element-bytes", "WritableBufferUses.Storage", "alias lineage")>]
[<InlineData("format", "WritableBufferUses.Storage", "selected byte declaration")>]
[<InlineData("missing-use", "Calls.WritableBuffer", "per-use account")>]
[<InlineData("different-use", "Calls.WritableBuffer", "per-use account")>]
[<InlineData("count-proof", "WritableBufferUses.Claims", "count/storage proof citizens")>]
[<InlineData("storage-proof", "WritableBufferUses.Claims", "count/storage proof citizens")>]
[<InlineData("count-range", "WritableBufferUses.Bounds", "byte capacity")>]
let ``writable buffers reject declaration storage call and proof defects`` defect (part: string) (reason: string) =
    for relational in [false;true] do
        let held = writableBufferControl relational
        let boundary = held.Emission.Boundary
        let declaration = boundary.WritableBufferDeclarations[NodeId 1100]
        let use' = boundary.WritableBufferUses[NodeId 1,0]
        let facts = declaration.DeclarationFacts
        let withFacts facts =
            let changedBoundary =
                {boundary with
                    WritableBufferDeclarations = boundary.WritableBufferDeclarations.Add(NodeId 1100,{declaration with DeclarationFacts = facts})
                    Imports = boundary.Imports.Add(NodeId 72,{boundary.Imports[NodeId 72] with DeclarationFacts = facts})}
            {held with Emission = {held.Emission with Boundary = changedBoundary}}
        let withClaim id body =
            let old = held.CurrentClaims[NodeId id]
            let claim = {old with Body = body}
            {held with CurrentClaims = held.CurrentClaims.Add(NodeId id,claim)
                       Obligations = held.Obligations |> List.map (fun row -> if row.Id=old.Id then claim else row)}
        let changed =
            match defect with
            | "quote" -> withFacts (facts.Add(NodeId 1103,{facts[NodeId 1103] with Text = ["wrong.fill"]}))
            | "sibling" -> withFacts (facts.Add(NodeId 1073,{facts[NodeId 1073] with Text = ["otherDescriptor"]}))
            | "reference" -> withFacts (facts.Add(NodeId 1016,{facts[NodeId 1016] with Text = ["Value"]}))
            | "signed-byte" -> withFacts (facts.Add(NodeId 1015,{facts[NodeId 1015] with Text = ["Signed"]}))
            | "byte-width" -> withFacts (facts.Add(NodeId 1018,{facts[NodeId 1018] with Numbers = [16I]}))
            | "alias" -> {held with Nodes = held.Nodes.Add(NodeId 1301,{held.Nodes[NodeId 1301] with Kind = SemanticKind.Literal NativeLiteral.Unit; Children = []})}
            | "element-bytes" ->
                let memory = held.Emission.Memory
                let operation =
                    match memory.Operations[NodeId 11] with
                    | MemoryWitnessOperation.ArrayAllocation row -> MemoryWitnessOperation.ArrayAllocation {row with ElementBytes = 2}
                    | _ -> failwith "Expected the writable allocation."
                {held with Emission = {held.Emission with Memory = {memory with Operations = memory.Operations.Add(NodeId 11,operation)}}}
            | "format" -> withFacts (facts.Add(NodeId 1203,{facts[NodeId 1203] with Numbers = [16I]}))
            | "missing-use" -> {held with Emission = {held.Emission with Boundary = {boundary with WritableBufferUses = Map.empty}}}
            | "different-use" ->
                {held with Emission = {held.Emission with Boundary = {boundary with WritableBufferUses = boundary.WritableBufferUses.Add((NodeId 1,0),{use' with Declaration = NodeId 72})}}}
            | "count-proof" -> withClaim 931 (ObligationBody.IntegerRepresentationCoverage(5I,5I,0I,4I))
            | "storage-proof" -> withClaim 932 (ObligationBody.IntegerRepresentationCoverage(0I,256I,0I,255I))
            | _ ->
                let numeric = held.Emission.Numeric
                {held with Emission = {held.Emission with Numeric = {numeric with Values = numeric.Values.Add(NodeId 4,{numeric.Values[NodeId 4] with Range = ValueRange.Bounded(5I,5I)})}}}
        let expectedReason = if defect="count-range" && not relational then "four-byte capacity" else reason
        Assert.Contains(Integrity.check changed, fun v ->
            v.Part="Emission.Boundary."+part && v.Node=Some(if part.StartsWith("WritableBufferDeclarations") then NodeId 1100 else NodeId 1) &&
            v.Reason.Contains expectedReason)

[<Theory>]
[<InlineData("missing")>]
[<InlineData("endpoint")>]
[<InlineData("claim")>]
let ``relational writable buffers require their exact foreign result use`` defect =
    let held = writableBufferControl true
    let numeric = held.Emission.Numeric
    let account = numeric.ForeignResultUses.Head
    let uses =
        match defect with
        | "missing" -> []
        | "endpoint" -> [{account with Application = {account.Application with Hypothesis = account.Application.Hypothesis |> Option.map (fun h -> {h with Upper = ForeignResultBound.Constant 4I})}}]
        | _ -> [{account with Claims = [account.Claims.Head]}]
    let changed = {held with Emission = {held.Emission with Numeric = {numeric with ForeignResultUses = uses}}}
    Assert.Contains(Integrity.check changed, fun v ->
        v.Part="Emission.Boundary.WritableBufferUses.Account" && v.Node=Some(NodeId 1) && v.Reason.Contains "current result account")

let private optionalBoundaryControl absent =
    let held = ordinaryResultReturnedWrite ()
    let callbackType = boundaryCalleeFacts.Nodes[NodeId 3].Type
    let fnType = TypeIdentity.Function(callbackType,callbackType)
    let entryType = TypeIdentity.Application({Declaration = {Module = [];Name = "FnPtr"};Parameters = [];NativeKind = Some NTUKind.NTUfnptr},[fnType])
    let optionType = TypeIdentity.Application({Declaration = {Module = [];Name = "option"};Parameters = [TypeParamKind.Type];NativeKind = None},[entryType])
    let p role ordinal group id : Participant = {Role=role;Ordinal=ordinal;Group=NodeId group;Node=NodeId id}
    let lifetime : ProgramImageCodeLifetime = {Module=NodeId 400;Binding=NodeId 401;Implementation=NodeId 10}
    let lifetimeParts = [p ParticipantRole.CallableLifetime 0 100 400;p ParticipantRole.CallableLifetime 1 100 401;p ParticipantRole.CallableLifetime 2 100 10]
    let header = {boundaryCalleeFacts.SourceReadings.ContextHeaders[NodeId 50] with Identity=NodeId 400;Name="OptionalControl"}
    let target : BoundaryPlatformPremise =
        {Id="optional-control";Description=None;Loading=None;LibraryPath=None;SourcePaths=Set.singleton "fixture"
         Architecture=Some "x86_64";OS=Some "linux";RuntimeClaim=None;Substrate=None
         Dimensions=Map.ofList ["Pointer",64;"Register",64];Representations=Map.empty;EndpointReturns=Map.empty}
    let premise shape embedded reachable : BoundarySourcePremise =
        {Shape=shape;EmbeddedTypes=embedded;ConstructorFacts=[];Reachable=reachable;Range=None;ExternLibrary=None;ExternSymbol=None;HasExtern=false;Metadata=Map.empty}
    let sourcePremises =
        [NodeId 400,premise {controlFact "module" ["OptionalControl"] [] [401] None with Children=[]} [] false
         NodeId 401,premise {controlFact "binding" ["callback";"no-declaration-root"] [0I;0I] [10] (Some 400) with SourceType=fnType} [] true
         NodeId 10,premise {controlFact "lambda" ["RegularClosure";"argument"] [1I;0I;0I] [41;11] (Some 401) with SourceType=fnType} [callbackType] true] |> Map.ofList
    let contract =
        {held.Emission.Callable.Contracts[NodeId 100] with
            Kind=CallableKind.NativeEntry
            Convention=CallableConvention.CompilerOwnedPortable
                {Target=target;ParameterConversions=[0,CallableConversion.Identity(ValueRepresentation.Scalar(SettledSlot.Integer(32,None)))]
                 ResultConversion=CallableConversion.Identity(ValueRepresentation.Scalar(SettledSlot.Integer(32,None)));CodeLifetime=lifetime}
            ParameterTypes=[callbackType];ParameterRepresentations=[0,ValueRepresentation.Scalar(SettledSlot.Integer(32,None))]
            ResultType=callbackType;ResultRepresentation=ValueRepresentation.Scalar(SettledSlot.Integer(32,None));SourcePremises=sourcePremises
            Participants=[p ParticipantRole.CallableContract 0 100 100;p ParticipantRole.Source 0 100 400;p ParticipantRole.Source 1 100 401;p ParticipantRole.Source 2 100 10] @ lifetimeParts}
    let carrier =
        {held.Emission.Callable.Carriers[NodeId 30] with
            Kind=CallableKind.NativeEntry;SourceType=entryType;Lifetime=lifetimeParts
            Parameters=["argument",callbackType,NodeId 41];ParameterShapes=[CallableValueShape.Data(NodeId 41)]}
    let retirement : CallableAggregateResultRetirement =
        {Application=NodeId 1;Caller=NodeId 300;Construction=NodeId 2;Actual=NodeId 1;Receiver=NodeId 200
         Policy=optionalPlanRetirement.Policy;Uses=[NodeId 1;NodeId 200]}
    let tag : CallableAggregateTag =
        {Constructor=NodeId 2;TagRead=None;CaseOrdinal=if absent then 0 else 1
         PayloadOrdinal=(if absent then None else Some 0);Payload=(if absent then None else Some(NodeId 30))
         Participants=[p ParticipantRole.AggregateConstructor 0 2 2] @ (if absent then [] else [p ParticipantRole.AggregatePayload 0 2 30])}
    let slot = {held.Emission.Callable.AggregateSlots[NodeId 101] with AggregateType=optionType;SourceType=entryType;Path=[CallableAggregatePathStep.UnionPayload(1,0)]}
    let changeValue (row: CallableAggregateValue) =
        let inputs = if absent then row.FormationInputs |> List.filter ((<>) (NodeId 30)) else row.FormationInputs
        let parts =
            row.Participants |> List.filter (fun part ->
                not absent || not(List.contains part.Role [ParticipantRole.AggregateWrite;ParticipantRole.CallableCarrier;ParticipantRole.CallableFormation;ParticipantRole.AggregatePayload]) &&
                              not(part.Role=ParticipantRole.AggregateInput && part.Node=NodeId 30))
        let parts =
            parts @ (if row.Operation=CallableAggregateOperation.Result then
                         [p ParticipantRole.Source 10 1 300;p ParticipantRole.Source 11 1 1;p ParticipantRole.Source 12 1 200]
                     else [])
        {row with Tag=Some tag;FormationInputs=inputs;Participants=parts
                  Value=if absent then None else row.Value
                  Alternatives=if absent then [] else row.Alternatives
                  SelectedAlternative=if absent then None else row.SelectedAlternative
                  Selector=if absent then None else row.Selector
                  ResultRetirement=if row.Operation=CallableAggregateOperation.Result then Some(Ok retirement) else None}
    let values = held.Emission.Callable.AggregateValues |> Map.map (fun _ rows -> List.map changeValue rows)
    let nodes =
        [ {held.Nodes[NodeId 1] with Type=optionType;Parent=Some(NodeId 200)}
          {held.Nodes[NodeId 2] with
              Kind=SemanticKind.UnionCase((if absent then "None" else "Some"),(if absent then 0 else 1),(if absent then None else Some(NodeId 30)))
              Children=(if absent then [] else [NodeId 30]);Type=optionType}
          {held.Nodes[NodeId 5] with Type=TypeIdentity.Function(unitType,optionType)}
          {node 10 (SemanticKind.Lambda(["argument",callbackType,NodeId 41],NodeId 11,[],Some "callback",LambdaContext.RegularClosure)) [41;11] with Type=fnType;Parent=Some(NodeId 401)}
          {node 11 (SemanticKind.Literal(NativeLiteral.Int(1L,NTUKind.NTUint(NTUWidth.Fixed 32)))) [] with Type=callbackType;Parent=Some(NodeId 10)}
          {node 30 (SemanticKind.Application(NodeId 403,[NodeId 402])) [403;402] with Type=entryType}
          {node 402 (SemanticKind.VarRef("callback",Some(NodeId 401))) [] with Type=fnType}
          node 403 (SemanticKind.Intrinsic {Module=IntrinsicModule.FnPtr;Operation="ofFunction";Category=IntrinsicCategory.Pure;FullName="FnPtr.ofFunction"}) []
          {node 41 (SemanticKind.PatternBinding "argument") [] with Type=callbackType;Parent=Some(NodeId 10)}
          {node 200 (SemanticKind.Application(NodeId 201,[NodeId 1])) [201;1] with Parent=Some(NodeId 300)}
          node 201 (SemanticKind.VarRef("receive",None)) []
          node 300 (SemanticKind.Lambda([],NodeId 200,[],Some "caller",LambdaContext.RegularClosure)) [200]
          {node 401 (SemanticKind.Binding("callback",false,false,None)) [10] with Type=fnType;Parent=Some(NodeId 400)} ]
    let allNodes = nodes |> List.fold (fun rows node -> Map.add node.Id node rows) held.Nodes
    let declaration =
        {held.Emission.Callable.Declarations[NodeId 10] with
            Parameters=["argument",callbackType,NodeId 41];Parent=Some(NodeId 401)
            Participants=Set.ofList [NodeId 10;NodeId 11;NodeId 41;NodeId 401]}
    let callable =
        {held.Emission.Callable with
            Contracts=Map.ofList [NodeId 100,contract];Carriers=Map.ofList [NodeId 30,carrier]
            AggregateSlots=Map.ofList [NodeId 101,slot];AggregateValues=values
            Declarations=Map.ofList [NodeId 10,declaration]
            SignatureData=held.Emission.Callable.SignatureData.Add(NodeId 10,Set.ofList [NodeId 41;NodeId 11])
            ClosedData=held.Emission.Callable.ClosedData.Add(NodeId 41)
            NativeEntries=Map.ofList [NodeId 10,"callback"]
            Symbols=held.Emission.Callable.Symbols.Add(NodeId 300,CallableSymbolName.Anonymous(NodeId 300))}
    let accounts = callable.AggregateDependencies |> Map.map (fun _ account ->
        let accountValues = account.Values |> List.map changeValue
        let participants = slot.Participants @ (accountValues |> List.collect (fun row -> row.Participants @ tag.Participants)) @ (if absent then [] else lifetimeParts) @ contract.Participants
        let sources = participants |> List.map _.Node |> List.distinct |> List.filter (sourcePremises.ContainsKey >> not) |> List.choose (fun id ->
            allNodes.TryFind id |> Option.map (fun node -> {Node=id;Kind=node.Kind;Type=node.Type;Children=node.Children;Anchors=node.ObligationAnchors}))
        {account with Slots=[slot];Values=accountValues;Carriers=(if absent then [] else [carrier]);Contracts=[contract];Participants=participants;Sources=sources
                      Symbols=if absent then account.Symbols |> List.filter (fun (id,_) -> id<>NodeId 10) else account.Symbols
                      MemoryPolicy=if account.Occurrence=NodeId 1 then Some retirement.Policy else None})
    let callable = {callable with AggregateDependencies=accounts}
    let record fields refs parent = controlFact "record" fields [] refs (Some parent)
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let binding name child = controlFact "binding" [name] [0I;0I] [child] (Some 400)
    let contractType name = TypeIdentity.Application({Declaration={Module=["BAREWire";"Descriptors"];Name=name};Parameters=[];NativeKind=None},[])
    let facts =
        [210,record ["Parameters"] [212] 213
         213,controlFact "quotation" [] [] [210] (Some 214)
         214,binding "receiveDescriptor" 213
         211,{controlFact "formal" ["callback"] [] [] (Some 215) with SourceType=optionType}
         215,controlFact "lambda" ["receive";"callback"] [1I;0I;0I] [211;216] (Some 217)
         216,controlFact "unit" [] [] [] (Some 215)
         217,binding "receive" 215
         212,controlFact "array" [] [] [218] (Some 210)
         218,record ["Type";"PassBy"] [219;229] 212
         219,controlFact "case" ["Entry"] [] [220] (Some 218)
         229,controlFact "case" ["Value"] [] [] (Some 218)
         220,{controlFact "quotation" [] [1I] [222] (Some 221) with SourceType=contractType "CallbackInvocationContract"}
         221,{binding "receiveCallbackInvocation" 220 with SourceType=contractType "CallbackInvocationContract"}
         222,{record ["Binding";"Parameter";"Signature";"Hypothesis";"Scope"] [223;224;225;226;227] 220 with SourceType=contractType "CallbackInvocationContract"}
         223,text "OptionalControl.receive" 222
         224,controlFact "integer" [] [0I] [] (Some 222)
         225,record ["Parameters";"ReturnType";"CallingConvention"] [233;238;235] 222
         233,controlFact "array" [] [] [236] (Some 225)
         235,controlFact "case" ["CDecl"] [] [] (Some 225)
         236,record ["Name";"Type";"PassBy"] [237;238;239] 233
         237,text "argument" 236
         238,controlFact "case" ["Integer"] [] [240] (Some 236)
         239,controlFact "case" ["Value"] [] [] (Some 236)
         240,controlFact "tuple" [] [] [241;242] (Some 238)
         241,controlFact "case" ["Signed"] [] [] (Some 240)
         242,controlFact "integer" [] [32I] [] (Some 240)
         226,record ["Identity";"Version";"Source"] [230;231;232] 222
         227,text "during_call" 222
         230,text "invoke" 226;231,text "1" 226;232,text "fixture" 226
         400,sourcePremises[NodeId 400].Shape
         401,sourcePremises[NodeId 401].Shape
         500,{controlFact "quotation" [] [1I] [502] (Some 501) with SourceType=contractType "Descriptors.CallbackAbsenceContract"}
         501,{binding "receiveCallbackAbsence" 500 with SourceType=contractType "Descriptors.CallbackAbsenceContract"}
         502,{record ["Binding";"Parameter";"Hypothesis"] [503;504;505] 500 with SourceType=contractType "Descriptors.CallbackAbsenceContract"}
         503,text "OptionalControl.receive" 502
         504,controlFact "integer" [] [0I] [] (Some 502)
         505,record ["Identity";"Version";"Source"] [506;507;508] 502
         506,text "absence" 505;507,text "1" 505;508,text "fixture" 505
         600,{controlFact "quotation" [] [1I] [602] (Some 601) with SourceType=contractType "ScopedCallbackDescriptor"}
         601,{binding "during_call" 600 with SourceType=contractType "ScopedCallbackDescriptor"}
         602,{record ["Binding";"Parameter"] [603;604] 600 with SourceType=contractType "ScopedCallbackDescriptor"}
         603,text "OptionalControl.receive" 602;604,text "callback" 602]
        |> List.map (fun (id,fact) -> NodeId id,fact) |> Map.ofList
    let imported : BoundaryImport =
        {Identity=NodeId 210;Binding=NodeId 217;Scope=NodeId 400;Library="c";Symbol="receive";CallingConvention="CDecl"
         DeclarationPath=[NodeId 217];Parameters=[NodeId 211,BoundaryScalar.Entry(NodeId 220)];Result=None
         Participants=facts.Keys |> Set.ofSeq;SourceTypes=Map.ofList [NodeId 211,optionType];DeclarationFacts=facts}
    let receiver : BoundaryCallbackInvocation =
        {Identity=NodeId 220;Import=NodeId 210;Parameter=0;Formal=NodeId 211;Scope=NodeId 600
         Contract={Binding="OptionalControl.receive";Parameter=0
                   Signature={Parameters=[|{Name="argument";Type=BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed,32);PassBy=BAREWire.Descriptors.PassBy.Value}|]
                              ReturnType=BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed,32);CallingConvention=BAREWire.Descriptors.CallConv.CDecl}
                   Hypothesis={Identity="invoke";Version="1";Source="fixture"};Scope="during_call"}
         Signature={Parameters=[BoundaryScalar.Integer(32,true)];Result=Some(BoundaryScalar.Integer(32,true));CallingConvention="CDecl"}
         Extent=BoundaryCallbackExtent.DuringCall;Participants=facts.Keys |> Set.ofSeq}
    let absence : BoundaryCallbackAbsence =
        {Quote=NodeId 500;DescriptorBinding=NodeId 501;Record=NodeId 502;Import=NodeId 210;Parameter=0;Formal=NodeId 211;Invocation=NodeId 220
         Contract={Binding="OptionalControl.receive";Parameter=0;Hypothesis={Identity="absence";Version="1";Source="fixture"}}
         SourcePath=[NodeId 500;NodeId 502]
         Inputs=[CallbackAbsenceInputRole.Binding,[NodeId 503];CallbackAbsenceInputRole.Parameter,[NodeId 504]
                 CallbackAbsenceInputRole.Hypothesis,[NodeId 505];CallbackAbsenceInputRole.HypothesisIdentity,[NodeId 506]
                 CallbackAbsenceInputRole.HypothesisVersion,[NodeId 507];CallbackAbsenceInputRole.HypothesisSource,[NodeId 508]]
         DeclarationFacts=[500..508] |> List.map(fun id -> NodeId id,facts[NodeId id]) |> Map.ofList}
    let entry : BoundaryClosedEntry =
        {Formation=NodeId 30;Operand=NodeId 402;Declaration=NodeId 401;Implementation=NodeId 10;Formals=[NodeId 41];Body=NodeId 11
         Lifetime=lifetime;Invocation=NodeId 220;ParameterAdaptations=[None];ResultAdaptation=None;Registrations=Map.empty
         Transport=Set.ofList [NodeId 30;NodeId 402]
         Participants=Set.union receiver.Participants (Set.ofList [NodeId 30;NodeId 402;NodeId 403;NodeId 10;NodeId 401;NodeId 41;NodeId 11;NodeId 400;NodeId 100;NodeId 220])}
    let selected : BoundaryOptionalEntry =
        {Construction=NodeId 2;CaseOrdinal=(if absent then 0 else 1);Payload=(if absent then None else Some(NodeId 30))
         Formation=(if absent then None else Some(NodeId 30));Transport=Set.ofList (if absent then [NodeId 1;NodeId 2] else [NodeId 1;NodeId 2;NodeId 30]);Obligation=NodeId 301}
    let support =
        Set.unionMany
            [accounts[NodeId 1].Sources |> List.map _.Node |> Set.ofList
             selected.Transport
             Set.ofList [NodeId 200;NodeId 210;NodeId 201;NodeId 1;NodeId 211;NodeId 2]
             imported.Participants
             receiver.Participants]
    let claim =
        if absent then
            {controlClaim "optional-none" "foreign-optional-entry-conversion-0"
                (ObligationBody.OptionalEntryAbsenceArgumentConversion
                    {Call=NodeId 200;Parameter=0;Actual=NodeId 1;Construction=NodeId 2;SourceCase=0;Absence=NodeId 500
                     Arms=(absentPlan None).Arms;ResultRetirement=Some retirement}) with
                Statement="The exact source None selection has complete finite absence-choice correspondence under its external binding hypothesis; target realization remains an artifact obligation."}
        else
            {controlClaim "optional-some" "foreign-optional-entry-conversion-0"
                (ObligationBody.OptionalEntryArgumentConversion
                    {Call=NodeId 200;Parameter=0;Actual=NodeId 1;Construction=NodeId 2;SourceCase=1;Payload=NodeId 30;Formation=NodeId 30;Invocation=NodeId 220
                     Arms=[{CaseOrdinal=0;Choice=OptionalEntryPlanChoice.PendingAbsence;Formation=None};{CaseOrdinal=1;Choice=OptionalEntryPlanChoice.ClosedEntry;Formation=Some(NodeId 30)}]
                     ResultRetirement=Some retirement}) with
                Statement="The exact source Some selection has complete finite native-choice plan correspondence; target realization remains an artifact obligation."}
    let call : BoundaryCall =
        {Site=NodeId 200;Import=NodeId 210;Callee=NodeId 201;Entry=None;Resource=None
         Arguments=[{Actual=NodeId 1;Formal=NodeId 211;Abi=BoundaryScalar.Entry(NodeId 220);Adaptation=None;OptionalEntry=Some(BoundaryOptionalEntryChoice.Direct selected);BufferAbsence=None}]
         ErasedUnitArguments=[];Result=None;ResultAdaptation=None;Participants=support.Add(NodeId 301);SourceTypes=Map.ofList [NodeId 1,optionType]}
    let boundary =
        {held.Emission.Boundary with
            Imports=Map.ofList [NodeId 210,imported];Calls=Map.ofList [NodeId 200,call]
            CallbackInvocations=Map.ofList [NodeId 220,receiver]
            CallbackAbsences=if absent then Map.ofList [NodeId 500,absence] else Map.empty
            ClosedEntries=if absent then Map.empty else Map.ofList [NodeId 30,entry]}
    let representation = ValueRepresentation.Union(["None",[];"Some",[ValueRepresentation.CallableComponent(NodeId 101,ValueRepresentation.Record([],Some([],0,1)))]],Some(1,1,1))
    {held with
        Nodes=allNodes;Platform={Register=Ok 64;Pointer=Ok 64}
        CurrentClaims=Map.ofList [NodeId 301,claim];Obligations=[claim]
        ObligationSources=Map.ofList [NodeId 301,[List.distinct(NodeId 200 :: Set.toList support)]]
        Codata={held.Codata with
                    CallableContracts=callable.Contracts;CallableCarriers=callable.Carriers;CallableAggregateSlots=callable.AggregateSlots
                    FunctionPointers=Map.ofList [NodeId 30,FunctionPointerPlan.Address("callback",NodeId 10)]
                    CallableAggregateValues=callable.AggregateValues;CallableAggregateDependencies=accounts}
        Emission={held.Emission with
                      Callable=callable;Boundary=boundary
                      Numeric={held.Emission.Numeric with OccurrenceRepresentations=held.Emission.Numeric.OccurrenceRepresentations.Add(NodeId 1,Ok representation).Add(NodeId 2,Ok representation)}}}
    |> covered
    |> fun revision ->
        let source =
            {revision.SourceReadings with
                ContextHeaders=revision.SourceReadings.ContextHeaders.Add(NodeId 400,header)
                Contexts=revision.SourceReadings.Contexts.Add(NodeId 400,[[]])
                Ports=revision.SourceReadings.Ports.Add((NodeId 400,OccurrencePort.ModuleDeclaration),header.Ports[OccurrencePort.ModuleDeclaration])}
        let numeric = revision.Emission.Numeric
        let scalar site = {boundaryCalleeFacts.Emission.Numeric.Values[NodeId 3] with Site=NodeId site;SourceType=callbackType;Declaration=None;Participants=Set.singleton(NodeId site);Obligations=[]}
        {revision with SourceReadings=source
                       Emission={revision.Emission with Numeric={numeric with
                                                                   Values=numeric.Values.Add(NodeId 11,scalar 11).Add(NodeId 41,scalar 41)
                                                                   OccurrenceRepresentations=numeric.OccurrenceRepresentations.Add(NodeId 1,Ok representation).Add(NodeId 2,Ok representation)
                                                                       .Add(NodeId 11,Ok(ValueRepresentation.Scalar(SettledSlot.Integer(32,None))))
                                                                       .Add(NodeId 41,Ok(ValueRepresentation.Scalar(SettledSlot.Integer(32,None))))}}}

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``finite optional boundary plans retain exact Some or None ownership and retirement`` absent =
    Assert.Empty(Integrity.check (optionalBoundaryControl absent))

let private changeOptionalClaim change (held: Revision) =
    let old = held.CurrentClaims[NodeId 301]
    let claim = change old
    {held with CurrentClaims = held.CurrentClaims.Add(NodeId 301,claim)
               Obligations = held.Obligations |> List.map (fun row -> if row.Id=old.Id then claim else row)}

[<Theory>]
[<InlineData("case-ordinal")>]
[<InlineData("choice")>]
[<InlineData("logic")>]
[<InlineData("missing-retirement")>]
[<InlineData("retirement-mismatch")>]
[<InlineData("sources-missing")>]
[<InlineData("sources-order")>]
let ``finite optional boundary plans reject changed arms logic retirement and sources`` defect =
    for absent in [false;true] do
        let held = optionalBoundaryControl absent
        Assert.Empty(Integrity.check held)
        let bodyChange = function
            | ObligationBody.OptionalEntryArgumentConversion model ->
                let changed =
                    match defect with
                    | "case-ordinal" -> {model with Arms = {model.Arms.Head with CaseOrdinal = 1} :: model.Arms.Tail}
                    | "choice" -> {model with Arms = {model.Arms.Head with Choice = OptionalEntryPlanChoice.ClosedEntry} :: model.Arms.Tail}
                    | "missing-retirement" -> {model with ResultRetirement = None}
                    | "retirement-mismatch" -> {model with ResultRetirement = model.ResultRetirement |> Option.map (fun row -> {row with Actual = NodeId 2})}
                    | _ -> model
                ObligationBody.OptionalEntryArgumentConversion changed
            | ObligationBody.OptionalEntryAbsenceArgumentConversion model ->
                let changed =
                    match defect with
                    | "case-ordinal" -> {model with Arms = {model.Arms.Head with CaseOrdinal = 1} :: model.Arms.Tail}
                    | "choice" -> {model with Arms = {model.Arms.Head with Choice = OptionalEntryAbsencePlanChoice.RequiresClosedEntry} :: model.Arms.Tail}
                    | "missing-retirement" -> {model with ResultRetirement = None}
                    | "retirement-mismatch" -> {model with ResultRetirement = model.ResultRetirement |> Option.map (fun row -> {row with Actual = NodeId 2})}
                    | _ -> model
                ObligationBody.OptionalEntryAbsenceArgumentConversion changed
            | _ -> failwith "Expected a finite optional plan."
        let changed =
            held |> changeOptionalClaim (fun claim ->
                {claim with Body = bodyChange claim.Body; Logic = if defect="logic" then "QF_BV" else claim.Logic})
        let changed =
            if defect="sources-missing" then {changed with ObligationSources = changed.ObligationSources.Remove(NodeId 301)}
            elif defect="sources-order" then
                {changed with ObligationSources = changed.ObligationSources.Add(NodeId 301,changed.ObligationSources[NodeId 301] |> List.map List.rev)}
            else changed
        Assert.Contains(Integrity.check changed, fun v ->
            v.Part="Emission.Boundary.Calls.OptionalEntry.Obligation" && v.Node=Some(NodeId 200) &&
            v.Reason="The optional callback requires its exact existing Pending per-call conversion claim.")

[<Theory>]
[<InlineData("missing")>]
[<InlineData("invocation")>]
[<InlineData("hypothesis")>]
let ``finite None boundary plan requires its exact independent absence quotation`` defect =
    let held = optionalBoundaryControl true
    Assert.Empty(Integrity.check held)
    let boundary = held.Emission.Boundary
    let absence = boundary.CallbackAbsences[NodeId 500]
    let absences =
        match defect with
        | "missing" -> Map.empty
        | "invocation" -> Map.ofList [NodeId 500,{absence with Invocation = NodeId 210}]
        | _ -> Map.ofList [NodeId 500,{absence with Contract = {absence.Contract with Hypothesis = {absence.Contract.Hypothesis with Version = "changed"}}}]
    let changed = {held with Emission = {held.Emission with Boundary = {boundary with CallbackAbsences = absences}}}
    Assert.Contains(Integrity.check changed, fun v ->
        v.Part="Emission.Boundary.Calls.OptionalEntry.Obligation" && v.Node=Some(NodeId 200))

[<Theory>]
[<InlineData("empty-uses")>]
[<InlineData("duplicate-use")>]
[<InlineData("receiver")>]
let ``finite optional boundary plans reject incomplete shared retirement accounts`` defect =
    for absent in [false;true] do
        let held = optionalBoundaryControl absent
        Assert.Empty(Integrity.check held)
        let change (row: CallableAggregateResultRetirement) =
            match defect with
            | "empty-uses" -> {row with Uses = []}
            | "duplicate-use" -> {row with Uses = row.Application :: row.Uses}
            | _ -> {row with Receiver = NodeId 201}
        let changed = held |> changeOptionalClaim (fun claim ->
            let body =
                match claim.Body with
                | ObligationBody.OptionalEntryArgumentConversion model ->
                    ObligationBody.OptionalEntryArgumentConversion {model with ResultRetirement = model.ResultRetirement |> Option.map change}
                | ObligationBody.OptionalEntryAbsenceArgumentConversion model ->
                    ObligationBody.OptionalEntryAbsenceArgumentConversion {model with ResultRetirement = model.ResultRetirement |> Option.map change}
                | _ -> failwith "Expected a finite optional plan."
            {claim with Body = body})
        let rowChange (row: CallableAggregateValue) =
            {row with ResultRetirement = row.ResultRetirement |> Option.map (Result.map change)}
        let callable = changed.Emission.Callable
        let values = callable.AggregateValues |> Map.map (fun _ rows -> List.map rowChange rows)
        let accounts = callable.AggregateDependencies |> Map.map (fun _ account -> {account with Values = List.map rowChange account.Values})
        let changed =
            {changed with
                Codata = {changed.Codata with CallableAggregateValues = values; CallableAggregateDependencies = accounts}
                Emission = {changed.Emission with Callable = {callable with AggregateValues = values; AggregateDependencies = accounts}}}
        Assert.Contains(Integrity.check changed, fun v ->
            v.Part="Emission.Callable.Aggregates.I5" && v.Node=Some(NodeId 1) &&
            v.Reason="The returned optional retirement differs from its exact caller, instance, receiver or closed use inventory.")

let private resourceReleaseSignatureControl returnKind =
    let held = moduleUnitFacts
    let header = held.SourceReadings.ContextHeaders[NodeId 50]
    let handleType = TypeIdentity.NativePointer unitType
    let resultType =
        TypeIdentity.Application(
            {Declaration={Module=[];Name="option"};Parameters=[TypeParamKind.Type];NativeKind=None},
            [handleType])
    let acquisitionType = TypeIdentity.Function(unitType,resultType)
    let releaseResultType =
        match returnKind with
        | "void" -> unitType
        | "pointer64" -> handleType
        | "signed32" | "unsigned32" | "signed64" ->
            let bits = if returnKind="signed64" then 64 else 32
            let kind = if returnKind="unsigned32" then NTUKind.NTUuint(NTUWidth.Fixed bits) else NTUKind.NTUint(NTUWidth.Fixed bits)
            TypeIdentity.Application({Declaration={Module=[];Name=returnKind};Parameters=[];NativeKind=Some kind},[])
        | _ -> invalidArg "returnKind" "Unknown resource release signature control."
    let releaseType = TypeIdentity.Function(handleType,releaseResultType)
    let record fields refs parent = controlFact "record" fields [] refs (Some parent)
    let binding name child ty = {controlFact "binding" [name] [0I;0I] [child] (Some 50) with SourceType=ty}
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let releaseReturn =
        match returnKind with
        | "void" -> controlFact "case" ["Void"] [] [] (Some 7032)
        | "pointer64" -> controlFact "case" ["Pointer"] [] [7044] (Some 7032)
        | _ -> controlFact "case" ["Integer"] [] [7041] (Some 7032)
    let facts =
        [7000,controlFact "quotation" [] [1I] [7002] (Some 7001)
         7001,binding "acquireResourceDescriptor" 7000 unitType
         7002,record ["Resource";"Hypothesis"] [7003;7007] 7000
         7003,controlFact "case" ["OwnedNullableReturn"] [] [7004] (Some 7002)
         7004,record ["Binding";"Parameter"] [7005;7006] 7003
         7005,text (header.Name+".release") 7004
         7006,controlFact "integer" [] [0I] [] (Some 7004)
         7007,record ["Identity";"Version";"Source"] [7008;7009;7010] 7002
         7008,text "owned-resource" 7007;7009,text "1" 7007;7010,text "fixture" 7007
         7011,binding "acquire" 7012 acquisitionType
         7012,{controlFact "lambda" ["acquire";"unit"] [1I;0I;0I] [7013;7014] (Some 7011) with SourceType=acquisitionType}
         7013,controlFact "formal" ["unit"] [] [] (Some 7012)
         7014,{controlFact "unit" [] [] [] (Some 7012) with SourceType=resultType}
         7020,controlFact "quotation" [] [1I] [7022] (Some 7021)
         7021,binding "acquireDescriptor" 7020 unitType
         7022,record ["ReturnType";"CallingConvention"] [7023;7025] 7020
         7023,controlFact "case" ["Pointer"] [] [7024] (Some 7022)
         7024,controlFact "integer" [] [64I] [] (Some 7023)
         7025,controlFact "case" ["CDecl"] [] [] (Some 7022)
         7026,binding "release" 7027 releaseType
         7027,{controlFact "lambda" ["release";"handle"] [1I;0I;0I] [7028;7029] (Some 7026) with SourceType=releaseType}
         7028,{controlFact "formal" ["handle"] [] [] (Some 7027) with SourceType=handleType}
         7029,{controlFact "unit" [] [] [] (Some 7027) with SourceType=releaseResultType}
         7030,controlFact "quotation" [] [1I] [7032] (Some 7031)
         7031,binding "releaseDescriptor" 7030 unitType
         7032,record ["ReturnType";"CallingConvention";"Parameters"] [7040;7033;7034] 7030
         7033,controlFact "case" ["CDecl"] [] [] (Some 7032)
         7034,controlFact "array" [] [] [7035] (Some 7032)
         7035,record ["Type";"PassBy"] [7036;7038] 7034
         7036,controlFact "case" ["Pointer"] [] [7037] (Some 7035)
         7037,controlFact "integer" [] [64I] [] (Some 7036)
         7038,controlFact "case" ["Value"] [] [] (Some 7035)
         7040,releaseReturn
         7041,controlFact "tuple" [] [] [7042;7043] (Some 7040)
         7042,controlFact "case" [(if returnKind="unsigned32" then "Unsigned" else "Signed")] [] [] (Some 7041)
         7043,controlFact "integer" [] [(if returnKind="signed64" then 64I else 32I)] [] (Some 7041)
         7044,controlFact "integer" [] [64I] [] (Some 7040)]
        |> List.map(fun(id,fact)->NodeId id,fact) |> Map.ofList
    let resource : BoundaryResourceDeclaration =
        {Identity=NodeId 7000;Acquisition=NodeId 7011;AcquisitionBody=NodeId 7014;AcquisitionDescriptor=NodeId 7022
         Release=NodeId 7026;ReleaseBody=NodeId 7029;ReleaseDescriptor=NodeId 7032;ReleaseFormal=NodeId 7028
         ReleaseOrdinal=0;PointerBits=64;AcquisitionType=acquisitionType;ResultType=resultType;HandleType=handleType
         Contract={Resource=BAREWire.Descriptors.ResourceProtocol.OwnedNullableReturn {Binding=header.Name+".release";Parameter=0}
                   Hypothesis={Identity="owned-resource";Version="1";Source="fixture"}}
         DeclarationFacts=facts;Participants=facts.Keys |> Set.ofSeq}
    {held with Emission={held.Emission with Boundary={held.Emission.Boundary with ResourceDeclarations=Map.ofList [resource.Identity,resource]}}}

[<Theory>]
[<InlineData("void")>]
[<InlineData("signed32")>]
let ``owned nullable resources admit void or signed32 release results`` returnKind =
    Assert.Empty(Integrity.check (resourceReleaseSignatureControl returnKind))

[<Theory>]
[<InlineData("unsigned32")>]
[<InlineData("signed64")>]
[<InlineData("pointer64")>]
let ``owned nullable resources reject unsigned wide or pointer release results`` returnKind =
    Assert.Empty(Integrity.check (resourceReleaseSignatureControl "void"))
    Assert.Empty(Integrity.check (resourceReleaseSignatureControl "signed32"))
    let violation = only "Emission.Boundary.ResourceDeclarations.Signature" (Integrity.check (resourceReleaseSignatureControl returnKind))
    Assert.Equal(Some(NodeId 7000),violation.Node)

[<Fact>]
let ``writable buffer profile admits non-initial positional splits across four parameters`` () =
    let held = writableBufferControl false
    let boundary = held.Emission.Boundary
    let integerType name kind =
        TypeIdentity.Application({Declaration = {Module = []; Name = name}; Parameters = []; NativeKind = Some kind}, [])
    let byteType = integerType "uint8" (NTUKind.NTUuint(NTUWidth.Fixed 8))
    let intType = integerType "int32" (NTUKind.NTUint(NTUWidth.Fixed 32))
    let countType = integerType "uint64" (NTUKind.NTUuint(NTUWidth.Fixed 64))
    let arrayType = TypeIdentity.Application({Declaration = {Module = []; Name = "array"}; Parameters = [TypeParamKind.Type]; NativeKind = None}, [byteType])
    let decl = boundary.WritableBufferDeclarations[NodeId 1100]
    let header = held.SourceReadings.ContextHeaders[NodeId 50]
    let record fields ids parent = controlFact "record" fields [] ids (Some parent)
    let case name refs parent = controlFact "case" [name] [] refs (Some parent)
    let number value parent = controlFact "integer" [] [value] [] (Some parent)
    let facts =
        decl.DeclarationFacts
        |> Map.add (NodeId 1003) (controlFact "lambda" ["fill"; "fd"; "buffer"; "count"; "flags"] [4I; 0I; 0I] [1001; 1004; 1005; 1002; 1006] (Some 2))
        |> Map.add (NodeId 1001) {controlFact "formal" ["fd"] [] [] (Some 1003) with SourceType = intType}
        |> Map.add (NodeId 1002) {controlFact "formal" ["flags"] [] [] (Some 1003) with SourceType = intType}
        |> Map.add (NodeId 1010) (controlFact "array" [] [] [1030; 1011; 1012; 1031] (Some 72))
        |> Map.add (NodeId 1030) (record ["Type"; "PassBy"] [1032; 1033] 1010)
        |> Map.add (NodeId 1031) (record ["Type"; "PassBy"] [1034; 1035] 1010)
        |> Map.add (NodeId 1032) (case "Integer" [1036] 1030)
        |> Map.add (NodeId 1036) (controlFact "tuple" [] [] [1037; 1038] (Some 1032))
        |> Map.add (NodeId 1037) (case "Signed" [] 1036)
        |> Map.add (NodeId 1038) (number 32I 1036)
        |> Map.add (NodeId 1033) (case "Value" [] 1030)
        |> Map.add (NodeId 1034) (case "Integer" [1039] 1031)
        |> Map.add (NodeId 1039) (controlFact "tuple" [] [] [1040; 1041] (Some 1034))
        |> Map.add (NodeId 1040) (case "Signed" [] 1039)
        |> Map.add (NodeId 1041) (number 32I 1039)
        |> Map.add (NodeId 1035) (case "Value" [] 1031)
        |> Map.add (NodeId 1104) (number 1I 1102)
        |> Map.add (NodeId 1105) (number 2I 1102)
    let updatedDecl =
        { decl with
            Formals = [NodeId 1001; NodeId 1004; NodeId 1005; NodeId 1002]
            Parameter = 1; CountParameter = 2
            Contract = { decl.Contract with Binding = header.Name + ".fill"; Parameter = 1; CountParameter = 2 }
            DeclarationFacts = facts
            Participants = facts.Keys |> Set.ofSeq }
    let use' = { boundary.WritableBufferUses[NodeId 1, 0] with Parameter = 1; CountParameter = 2 }
    let oldImport = boundary.Imports[NodeId 72]
    let newParams =
        [ NodeId 1001, BoundaryScalar.Integer(32, true)
          NodeId 1004, BoundaryScalar.WritableBytes(NodeId 1100)
          NodeId 1005, BoundaryScalar.Integer(64, false)
          NodeId 1002, BoundaryScalar.Integer(32, true) ]
    let updatedImport =
        { oldImport with
            Parameters = newParams
            DeclarationFacts = facts
            Participants = updatedDecl.Participants
            SourceTypes = Map.ofList [NodeId 1001, intType; NodeId 1004, arrayType; NodeId 1005, countType; NodeId 1002, intType; NodeId 1, unitType] }
    let newArgs =
        [ { Actual = NodeId 31; Formal = NodeId 1001; Abi = BoundaryScalar.Integer(32, true); Adaptation = None; OptionalEntry = None; BufferAbsence = None }
          boundary.Calls[NodeId 1].Arguments.[0]
          boundary.Calls[NodeId 1].Arguments.[1]
          { Actual = NodeId 32; Formal = NodeId 1002; Abi = BoundaryScalar.Integer(32, true); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
    let updatedCall = { boundary.Calls[NodeId 1] with Arguments = newArgs; Participants = updatedDecl.Participants; SourceTypes = updatedImport.SourceTypes }
    let n31 = { node 31 (SemanticKind.Literal(NativeLiteral.Int(1L, NTUKind.NTUint(NTUWidth.Fixed 32)))) [] with Type = intType }
    let n32 = { node 32 (SemanticKind.Literal(NativeLiteral.Int(0L, NTUKind.NTUint(NTUWidth.Fixed 32)))) [] with Type = intType }
    let callNode = { held.Nodes[NodeId 1] with Kind = SemanticKind.Application(NodeId 2, [NodeId 31; NodeId 3; NodeId 4; NodeId 32]); Children = [NodeId 2; NodeId 31; NodeId 3; NodeId 4; NodeId 32] }
    let revision =
        { held with
            Nodes = held.Nodes.Add(NodeId 1, callNode).Add(NodeId 31, n31).Add(NodeId 32, n32)
            Emission =
                { held.Emission with
                    Boundary =
                        { boundary with
                            Imports = Map.ofList [NodeId 72, updatedImport]
                            Calls = Map.ofList [NodeId 1, updatedCall]
                            WritableBufferDeclarations = Map.ofList [NodeId 1100, updatedDecl]
                            WritableBufferUses = Map.ofList [(NodeId 1, 1), use'] } } }
        |> covered
    let revision =
        { revision with
            SourceReadings =
                { revision.SourceReadings with
                    ContextHeaders = revision.SourceReadings.ContextHeaders.Add(NodeId 50, header)
                    Contexts = revision.SourceReadings.Contexts.Add(NodeId 50, [[]])
                    Ports = revision.SourceReadings.Ports.Add((NodeId 50, OccurrencePort.ModuleDeclaration), header.Ports[OccurrencePort.ModuleDeclaration]) } }
    Assert.Empty(Integrity.check revision)

[<Theory>]
[<InlineData("valid-explicit-during", "")>]
[<InlineData("valid-explicit-retained", "")>]
[<InlineData("valid-static-nul", "")>]
[<InlineData("valid-staged-nul", "")>]
[<InlineData("nonzero-copy", "Emission.Boundary.ReadOnlyBufferUses.Account")>]
[<InlineData("count-over-extent", "Emission.Boundary.ReadOnlyBufferUses.Crossing")>]
[<InlineData("retention-after-retire", "Emission.Boundary.ReadOnlyBufferUses.Retention")>]
[<InlineData("interior-nul-static", "Emission.Boundary.ReadOnlyBufferUses.Crossing")>]
[<InlineData("staged-too-small", "Emission.Boundary.ReadOnlyBufferUses.Crossing")>]
[<InlineData("missing-use", "Emission.Boundary.Calls.ReadOnlyBuffer")>]
let ``read-only zero-copy and uncounted path crossings enforce extent termination and retention`` mode expectedPart =
    let held = snapshotFacts
    let basis = boundaryCalleeFacts.Emission.Boundary
    let integerType name kind =
        TypeIdentity.Application({Declaration = {Module = []; Name = name}; Parameters = []; NativeKind = Some kind}, [])
    let byteType = integerType "uint8" (NTUKind.NTUuint(NTUWidth.Fixed 8))
    let countType = integerType "uint64" (NTUKind.NTUuint(NTUWidth.Fixed 64))
    let arrayType = TypeIdentity.Application({Declaration = {Module = []; Name = "array"}; Parameters = [TypeParamKind.Type]; NativeKind = None}, [byteType])
    let header = boundaryCalleeFacts.SourceReadings.ContextHeaders[NodeId 50]
    let isUncounted = mode = "valid-static-nul" || mode = "valid-staged-nul" || mode = "interior-nul-static" || mode = "staged-too-small"
    let isRetained = mode = "valid-explicit-retained" || mode = "retention-after-retire"
    let bindingName = header.Name + ".readFn"
    let record fields ids parent = controlFact "record" fields [] ids (Some parent)
    let binding name child = controlFact "binding" [name] [0I;0I] [child] (Some 50)
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let number value parent = controlFact "integer" [] [value] [] (Some parent)
    let case name refs parent = controlFact "case" [name] [] refs (Some parent)
    let formals = if isUncounted then [NodeId 1004] else [NodeId 1004; NodeId 1005]
    let extentFact =
        if isUncounted then case "UncountedNulTerminated" [] 1102
        else case "ExplicitCount" [1110] 1102
    let retentionFact =
        if isRetained then case "RetainedUntil" [1112] 1102
        else case "DuringCall" [] 1102
    let extraFacts =
        [ if not isUncounted then
            yield 1110, number 1I 1105
          if isRetained then
            yield 1112, controlFact "tuple" [] [] [1113; 1114] (Some 1111)
            yield 1113, number 1I 1112
            yield 1114, controlFact "array" [] [] [1116] (Some 1112)
            yield 1116, case "OwnerRelease" [1117] 1114
            yield 1117, record ["Binding"; "Parameter"] [1118; 1119] 1116
            yield 1118, text (header.Name + ".close") 1117
            yield 1119, number 0I 1117 ]
    let lambdaText = if isUncounted then ["readFn"; "buf"] else ["readFn"; "buf"; "count"]
    let paramEntries = if isUncounted then [1011] else [1011; 1012]
    let facts =
        ([ 2, binding "readFn" 1003
           1003, controlFact "lambda" lambdaText [bigint formals.Length; 0I; 0I] ((formals |> List.map NodeId.value) @ [1006]) (Some 2)
           1004, {controlFact "formal" ["buf"] [] [] (Some 1003) with SourceType = arrayType}
           1006, controlFact "unit" [] [] [] (Some 1003)
           1073, binding "readFnDescriptor" 1072
           1072, controlFact "quotation" [] [] [72] (Some 1073)
           72, record ["Parameters"; "CName"] [1010; 1020] 1072
           1010, controlFact "array" [] [] paramEntries (Some 72)
           1011, record ["Type"; "PassBy"] [1013; 1016] 1010
           1013, case "Integer" [1014] 1011
           1014, controlFact "tuple" [] [] [1015; 1018] (Some 1013)
           1015, case "Unsigned" [] 1014
           1018, number 8I 1014
           1016, case "ReadOnlyReference" [] 1011
           1020, text "readFn" 72
           1101, binding "readFnReadOnlyDescriptor" 1100
           1100, controlFact "quotation" [] [] [1102] (Some 1101)
           1102, record ["Binding"; "Parameter"; "Extent"; "Content"; "Retention"; "Hypothesis"] [1103; 1104; 1105; 1115; 1111; 1106] 1100
           1103, text bindingName 1102
           1104, number 0I 1102
           1105, extentFact
           1115, case "RawBytes" [] 1102
           1111, retentionFact
           1106, record ["Identity"; "Version"; "Source"] [1107; 1108; 1109] 1102
           1107, text "ro-test" 1106
           1108, text "1" 1106
           1109, text "fixture" 1106 ]
         @ (if isUncounted then [] else
            [ 1005, {controlFact "formal" ["count"] [] [] (Some 1003) with SourceType = countType}
              1012, record ["Type"; "PassBy"] [1017; 1019] 1010
              1017, case "Integer" [1021] 1012
              1021, controlFact "tuple" [] [] [1022; 1023] (Some 1017)
              1022, case "Unsigned" [] 1021
              1023, number 64I 1021
              1019, case "Value" [] 1012 ])
         @ extraFacts)
        |> List.map (fun (id, fact) -> NodeId id, fact) |> Map.ofList
    let extent = if isUncounted then BAREWire.Descriptors.ReadOnlyBufferExtent.UncountedNulTerminated else BAREWire.Descriptors.ReadOnlyBufferExtent.ExplicitCount 1
    let releaseSpec = [| BAREWire.Descriptors.RetentionRelease.OwnerRelease { Binding = header.Name + ".close"; Parameter = 0 } |]
    let retention = if isRetained then BAREWire.Descriptors.BufferRetention.RetainedUntil(1, releaseSpec) else BAREWire.Descriptors.BufferRetention.DuringCall
    let roDecl : BoundaryReadOnlyBufferDeclaration =
        { Identity = NodeId 1100; Declaration = NodeId 2; Body = NodeId 1006; Formals = formals; Descriptor = NodeId 72
          Parameter = 0; CountParameter = (if isUncounted then None else Some 1)
          BufferFormal = NodeId 1004; CountFormal = (if isUncounted then None else Some(NodeId 1005))
          Contract =
            { Binding = bindingName; Parameter = 0; Extent = extent
              Content = BAREWire.Descriptors.BorrowedContent.RawBytes
              Retention = retention
              Hypothesis = { Identity = "ro-test"; Version = "1"; Source = "fixture" } }
          DeclarationFacts = facts
          Participants = ParticipantEvidence.Established
            ([ { Role = ParticipantRole.ReadOnlyBufferDeclaration; Node = NodeId 1100; Ordinal = 0; Group = NodeId 1100 }
               { Role = ParticipantRole.ReadOnlyBufferFormal; Node = NodeId 1004; Ordinal = 0; Group = NodeId 1100 } ] @
             if isUncounted then [] else [ { Role = ParticipantRole.ReadOnlyBufferFormal; Node = NodeId 1005; Ordinal = 1; Group = NodeId 1100 } ]) }
    let importParams =
        [ NodeId 1004, BoundaryScalar.ReadOnlyBytes(NodeId 1100) ] @
        if isUncounted then [] else [ NodeId 1005, BoundaryScalar.Integer(64, false) ]
    let callArgs =
        [ { Actual = NodeId 3; Formal = NodeId 1004; Abi = BoundaryScalar.ReadOnlyBytes(NodeId 1100); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ] @
        if isUncounted then [] else [ { Actual = NodeId 4; Formal = NodeId 1005; Abi = BoundaryScalar.Integer(64, false); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
    let imported =
        { basis.Imports[NodeId 72] with
            Symbol = "readFn"; Parameters = importParams; Result = None
            DeclarationFacts = facts; Participants = facts.Keys |> Set.ofSeq
            SourceTypes = Map.ofList ([NodeId 1004, arrayType; NodeId 1, unitType] @ if isUncounted then [] else [NodeId 1005, countType]) }
    let call =
        { basis.Calls[NodeId 1] with
            Arguments = callArgs; Result = None; SourceTypes = imported.SourceTypes; Participants = facts.Keys |> Set.ofSeq }
    let countVal = if mode = "count-over-extent" then 10I else 4I
    let countCarrier =
        { held.Emission.Numeric.Values[NodeId 4] with
            Slot = SettledSlot.Integer(64, Some "uint64"); SourceType = countType
            Range = ValueRange.Bounded(countVal, countVal); Obligations = [] }
    let extentClaim =
        controlClaim "ro-extent" "foreign-readonly-buffer-extent"
            (ObligationBody.ZeroCopyBufferExtent
                { Call = NodeId 1; Declaration = NodeId 1100; Parameter = 0; CountParameter = 1
                  Buffer = NodeId 3; Count = NodeId 4; MinimumCount = 4I; MaximumCount = 4I
                  ExtentCapacity = 4I; ElementBytes = 1; CountCoverage = NodeId 951 })
    let retireOrders = if mode = "retention-after-retire" then [0] elif isRetained then [5] else []
    let retireNodes = if isRetained then [NodeId 955] else []
    let retentionClaim =
        controlClaim "ro-ret" "foreign-buffer-retention-domination"
            (ObligationBody.BufferRetentionDomination
                { Call = NodeId 1; Declaration = NodeId 1100; Buffer = NodeId 3; Residence = NodeId 11
                  Mode = (if isRetained then BufferRetentionMode.RetainedUntilOwner(1, 1) else BufferRetentionMode.DuringCall)
                  AcquireOrder = 1; RetirementOrders = retireOrders })
    let termClaim =
        let staging =
            if mode = "valid-static-nul" || mode = "interior-nul-static" then UncountedPathStagingMode.StaticImageZeroCopy 0
            else UncountedPathStagingMode.CallScopedStaged(NodeId 956, (if mode = "staged-too-small" then 4 else 5))
        controlClaim "ro-term" "foreign-uncounted-path-termination"
            (ObligationBody.UncountedPathTermination
                { Call = NodeId 1; Declaration = NodeId 1100; Parameter = 0; Source = NodeId 3
                  Mode = staging; ByteLength = 4I; RequiresNoInteriorNul = true; RequiresTrailingNul = true })
    let crossing =
        match mode with
        | "valid-static-nul" | "interior-nul-static" ->
            BoundaryReadOnlyBufferCrossing.StaticImageNulBorrowed(0, NodeId 3, 4I, NodeId 953)
        | "valid-staged-nul" ->
            BoundaryReadOnlyBufferCrossing.CallScopedNulStaged(NodeId 956, 5, 4I, NodeId 953)
        | "staged-too-small" ->
            BoundaryReadOnlyBufferCrossing.CallScopedNulStaged(NodeId 956, 4, 4I, NodeId 953)
        | _ ->
            BoundaryReadOnlyBufferCrossing.ExplicitZeroCopy(1, NodeId 4, 4I, NodeId 951)
    let roUse : BoundaryReadOnlyBufferUse =
        { Call = NodeId 1; Declaration = NodeId 1100; Parameter = 0; Buffer = NodeId 3
          Residence = NodeId 11; Retirements = retireNodes
          Copies = if mode = "nonzero-copy" then 1 else 0
          Crossing = crossing; RetentionProof = NodeId 952; AccessExclusivityProof = None
          Participants = ParticipantEvidence.Established
            ([ { Role = ParticipantRole.ReadOnlyBufferCall; Node = NodeId 1; Ordinal = 0; Group = NodeId 1 }
               { Role = ParticipantRole.ReadOnlyBufferDeclaration; Node = NodeId 1100; Ordinal = 0; Group = NodeId 1 }
               { Role = ParticipantRole.ReadOnlyBufferActual; Node = NodeId 3; Ordinal = 0; Group = NodeId 1 }
               { Role = ParticipantRole.ReadOnlyBufferResidence; Node = NodeId 11; Ordinal = 0; Group = NodeId 1 } ] @
             (retireNodes |> List.map (fun r -> { Role = ParticipantRole.ReadOnlyBufferRetirement; Node = r; Ordinal = 0; Group = NodeId 1 }))) }
    let claims = [NodeId 951, extentClaim; NodeId 952, retentionClaim; NodeId 953, termClaim]
    let useStaticPool = mode = "valid-static-nul" || mode = "interior-nul-static"
    let poolBytes =
        if mode = "interior-nul-static" then [byte 'a'; 0uy; byte 'c'; byte 'd'; 0uy]
        else [byte 'a'; byte 'b'; byte 'c'; byte 'd'; 0uy]
    let pool : StaticStringPool =
        { Symbol = ".rodata.str"; Bytes = poolBytes; Alignment = 1; Size = 5; UsedSize = 5
          Entries = [{ NodeIds = [NodeId 3]; Content = "abcd"; Offset = 0; Length = 4; StorageLength = 5 }]
          SpaceName = "rodata"; Capacity = 5L; SpaceAlignment = 1; Granularity = 1; DeclarationNode = NodeId 2 }
    let callNode =
        let args = if isUncounted then [NodeId 3] else [NodeId 3; NodeId 4]
        { held.Nodes[NodeId 1] with Kind = SemanticKind.Application(NodeId 2, args); Children = NodeId 2 :: args; Type = unitType }
    let revision =
        { held with
            StaticStringPool = (if useStaticPool then Some pool else held.StaticStringPool)
            LiteralStorage = (if useStaticPool then held.LiteralStorage.Add(NodeId 3, LiteralStorage.Materialized 0) else held.LiteralStorage)
            Nodes = held.Nodes.Add(NodeId 1, callNode)
            CurrentClaims = claims |> List.fold (fun m (k, v) -> Map.add k v m) held.CurrentClaims
            Obligations = held.Obligations @ List.map snd claims
            ObligationSources = claims |> List.fold (fun m (k, _) -> Map.add k [[NodeId 1; NodeId 3]] m) held.ObligationSources
            Emission =
                { held.Emission with
                    Boundary =
                        { basis with
                            Imports = Map.ofList [NodeId 72, imported]
                            Calls = Map.ofList [NodeId 1, call]
                            ReadOnlyBufferDeclarations = Map.ofList [NodeId 1100, roDecl]
                            ReadOnlyBufferUses = if mode = "missing-use" then Map.empty else Map.ofList [(NodeId 1, 0), roUse] }
                    Numeric =
                        { held.Emission.Numeric with
                            Operations = Map.empty; OperationRequired = Set.empty; ResultSites = Set.empty
                            Required = if isUncounted then Set.empty else Set.singleton(NodeId 4)
                            Values = if isUncounted then held.Emission.Numeric.Values.Remove(NodeId 1) else held.Emission.Numeric.Values.Remove(NodeId 1).Add(NodeId 4, countCarrier) } } }
        |> covered
    let revision =
        { revision with
            SourceReadings =
                { revision.SourceReadings with
                    ContextHeaders = revision.SourceReadings.ContextHeaders.Add(NodeId 50, header)
                    Contexts = revision.SourceReadings.Contexts.Add(NodeId 50, [[]])
                    Ports = revision.SourceReadings.Ports.Add((NodeId 50, OccurrencePort.ModuleDeclaration), header.Ports[OccurrencePort.ModuleDeclaration]) } }
    let violations = Integrity.check revision
    if expectedPart = "" then
        Assert.Empty violations
    else
        Assert.Contains(violations, fun v -> v.Part = expectedPart)


[<Theory>]
[<InlineData("valid", "")>]
[<InlineData("null-not-option", "Emission.Boundary.BorrowedResultViewUses.Account")>]
[<InlineData("read-after-invalidation", "Emission.Boundary.BorrowedResultViewUses.Frontier")>]
let ``borrowed result view checks null-to-none boundary and invalidation frontier`` defect expectedPart =
    let held = writableBufferControl false
    let basis = held.Emission.Boundary
    let header = held.SourceReadings.ContextHeaders[NodeId 50]
    let record fields ids parent = controlFact "record" fields [] ids (Some parent)
    let binding name child = controlFact "binding" [name] [0I;0I] [child] (Some 50)
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let number value parent = controlFact "integer" [] [value] [] (Some parent)
    let case name refs parent = controlFact "case" [name] [] refs (Some parent)
    let viewFacts =
        basis.WritableBufferDeclarations[NodeId 1100].DeclarationFacts
        |> Map.add (NodeId 1201) (binding "fillBorrowedViewDescriptor" 1200)
        |> Map.add (NodeId 1200) (controlFact "quotation" [] [] [1202] (Some 1201))
        |> Map.add (NodeId 1202) (record ["Binding"; "Content"; "Extent"; "Owner"; "InvalidatedBy"; "Hypothesis"] [1203; 1204; 1205; 1206; 1207; 1208] 1200)
        |> Map.add (NodeId 1203) (text (header.Name + ".fill") 1202)
        |> Map.add (NodeId 1204) (case "Utf8Text" [] 1202)
        |> Map.add (NodeId 1205) (case "NulTerminated" [] 1202)
        |> Map.add (NodeId 1206) (number 0I 1202)
        |> Map.add (NodeId 1207) (controlFact "array" [] [] [1212] (Some 1202))
        |> Map.add (NodeId 1212) (case "AnyOwnerCall" [] 1207)
        |> Map.add (NodeId 1208) (record ["Identity"; "Version"; "Source"] [1209; 1210; 1211] 1202)
        |> Map.add (NodeId 1209) (text "view-hyp" 1208)
        |> Map.add (NodeId 1210) (text "1" 1208)
        |> Map.add (NodeId 1211) (text "fixture" 1208)
    let viewDecl : BoundaryBorrowedResultViewDeclaration =
        { Identity = NodeId 1200; Declaration = NodeId 2; Body = NodeId 1006
          Formals = [NodeId 1004; NodeId 1005]; Descriptor = NodeId 72
          OwnerParameter = 0; OwnerFormal = NodeId 1004
          Contract =
            { Binding = header.Name + ".fill"; Content = BAREWire.Descriptors.BorrowedContent.Utf8Text
              Extent = BAREWire.Descriptors.BorrowedExtent.NulTerminated; Owner = 0
              InvalidatedBy = [| BAREWire.Descriptors.BorrowInvalidation.AnyOwnerCall |]
              Hypothesis = { Identity = "view-hyp"; Version = "1"; Source = "fixture" } }
          DeclarationFacts = viewFacts
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.BorrowedResultViewDeclaration; Node = NodeId 1200; Ordinal = 0; Group = NodeId 1200 }
              { Role = ParticipantRole.BorrowedResultViewOwner; Node = NodeId 1004; Ordinal = 0; Group = NodeId 1200 } ] }
    let readOrders = if defect = "read-after-invalidation" then [6] else [2]
    let scopeClaim =
        controlClaim "borrowed-view-scope" "foreign-borrowed-view-scope"
            (ObligationBody.BorrowedResultViewScope
                { Call = NodeId 1; Declaration = NodeId 1200; Owner = NodeId 3; View = NodeId 1
                  CallOrder = 1; InvalidationOrders = [5]; ReadOrders = readOrders
                  NullToNoneBoundary = defect <> "null-not-option" })
    let viewUse : BoundaryBorrowedResultViewUse =
        { Call = NodeId 1; Declaration = NodeId 1200; Owner = NodeId 3; View = NodeId 1
          CompanionCall = None; CompanionArguments = []; CallOrder = 1
          Invalidations = [NodeId 961]; InvalidationOrders = [5]
          Reads = [NodeId 962]; ReadOrders = readOrders
          NullToNoneBoundary = defect <> "null-not-option"
          ScopeProof = NodeId 960
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.BorrowedResultViewCall; Node = NodeId 1; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewDeclaration; Node = NodeId 1200; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewOwner; Node = NodeId 3; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewInvalidation; Node = NodeId 961; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewRead; Node = NodeId 962; Ordinal = 0; Group = NodeId 1 } ] }
    let revision =
        { held with
            CurrentClaims = held.CurrentClaims.Add(NodeId 960, scopeClaim)
            Obligations = held.Obligations @ [scopeClaim]
            ObligationSources = held.ObligationSources.Add(NodeId 960, [[NodeId 1; NodeId 3]])
            Emission =
                { held.Emission with
                    Boundary =
                        { basis with
                            BorrowedResultViewDeclarations = Map.ofList [NodeId 1200, viewDecl]
                            BorrowedResultViewUses = Map.ofList [NodeId 1, viewUse] } } }
    let violations = Integrity.check revision
    if expectedPart = "" then
        Assert.Empty violations
    else
        Assert.Contains(violations, fun v -> v.Part = expectedPart)


[<Fact>]
let ``ordinary scalar operand cannot acquire a buffer absence account`` () =
    let call = boundaryCalleeFacts.Emission.Boundary.Calls[NodeId 1]
    let sel : BoundaryBufferAbsenceSelection =
        { Construction = NodeId 3; CaseOrdinal = 0; Payload = None; Absence = NodeId 700
          Transport = [NodeId 3]; Obligation = NodeId 701 }
    let changed = { call with Arguments = { call.Arguments.Head with BufferAbsence = Some(BoundaryBufferAbsenceChoice.Direct sel) } :: call.Arguments.Tail }
    let boundary = { boundaryCalleeFacts.Emission.Boundary with Calls = Map.ofList [call.Site, changed] }
    let violations = Integrity.check { boundaryCalleeFacts with Emission = { boundaryCalleeFacts.Emission with Boundary = boundary } }
    let v = within "Emission.Boundary.Calls.BufferAbsence" violations
    Assert.Equal("A buffer-absence account requires its original ReadOnlyBytes or WritableBytes formal.", v.Reason)

[<Theory>]
[<InlineData("valid-return", "")>]
[<InlineData("bad-import-return", "Emission.Boundary.Imports.Result")>]
[<InlineData("arg-borrowed", "Emission.Boundary.Calls.BorrowedBytes")>]
let ``borrowed bytes scalar is admitted only as declared borrowed view return`` mode expectedPart =
    let held = writableBufferControl false
    let basis = held.Emission.Boundary
    let header = held.SourceReadings.ContextHeaders[NodeId 50]
    let record fields ids parent = controlFact "record" fields [] ids (Some parent)
    let binding name child = controlFact "binding" [name] [0I;0I] [child] (Some 50)
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let number value parent = controlFact "integer" [] [value] [] (Some parent)
    let case name refs parent = controlFact "case" [name] [] refs (Some parent)
    let viewFacts =
        basis.WritableBufferDeclarations[NodeId 1100].DeclarationFacts
        |> Map.add (NodeId 1201) (binding "fillBorrowedViewDescriptor" 1200)
        |> Map.add (NodeId 1200) (controlFact "quotation" [] [] [1202] (Some 1201))
        |> Map.add (NodeId 1202) (record ["Binding"; "Content"; "Extent"; "Owner"; "InvalidatedBy"; "Hypothesis"] [1203; 1204; 1205; 1206; 1207; 1208] 1200)
        |> Map.add (NodeId 1203) (text (header.Name + ".fill") 1202)
        |> Map.add (NodeId 1204) (case "Utf8Text" [] 1202)
        |> Map.add (NodeId 1205) (case "NulTerminated" [] 1202)
        |> Map.add (NodeId 1206) (number 0I 1202)
        |> Map.add (NodeId 1207) (controlFact "array" [] [] [1212] (Some 1202))
        |> Map.add (NodeId 1212) (case "AnyOwnerCall" [] 1207)
        |> Map.add (NodeId 1208) (record ["Identity"; "Version"; "Source"] [1209; 1210; 1211] 1202)
        |> Map.add (NodeId 1209) (text "view-hyp" 1208)
        |> Map.add (NodeId 1210) (text "1" 1208)
        |> Map.add (NodeId 1211) (text "fixture" 1208)
    let viewDecl : BoundaryBorrowedResultViewDeclaration =
        { Identity = NodeId 1200; Declaration = NodeId 2; Body = NodeId 1006
          Formals = [NodeId 1004; NodeId 1005]; Descriptor = NodeId 72
          OwnerParameter = 0; OwnerFormal = NodeId 1004
          Contract =
            { Binding = header.Name + ".fill"; Content = BAREWire.Descriptors.BorrowedContent.Utf8Text
              Extent = BAREWire.Descriptors.BorrowedExtent.NulTerminated; Owner = 0
              InvalidatedBy = [| BAREWire.Descriptors.BorrowInvalidation.AnyOwnerCall |]
              Hypothesis = { Identity = "view-hyp"; Version = "1"; Source = "fixture" } }
          DeclarationFacts = viewFacts
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.BorrowedResultViewDeclaration; Node = NodeId 1200; Ordinal = 0; Group = NodeId 1200 }
              { Role = ParticipantRole.BorrowedResultViewOwner; Node = NodeId 1004; Ordinal = 0; Group = NodeId 1200 } ] }
    let scopeClaim =
        controlClaim "borrowed-view-scope" "foreign-borrowed-view-scope"
            (ObligationBody.BorrowedResultViewScope
                { Call = NodeId 1; Declaration = NodeId 1200; Owner = NodeId 3; View = NodeId 1
                  CallOrder = 1; InvalidationOrders = [5]; ReadOrders = [2]
                  NullToNoneBoundary = true })
    let viewUse : BoundaryBorrowedResultViewUse =
        { Call = NodeId 1; Declaration = NodeId 1200; Owner = NodeId 3; View = NodeId 1
          CompanionCall = None; CompanionArguments = []; CallOrder = 1
          Invalidations = [NodeId 961]; InvalidationOrders = [5]
          Reads = [NodeId 962]; ReadOrders = [2]
          NullToNoneBoundary = true; ScopeProof = NodeId 960
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.BorrowedResultViewCall; Node = NodeId 1; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewDeclaration; Node = NodeId 1200; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewOwner; Node = NodeId 3; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewInvalidation; Node = NodeId 961; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewRead; Node = NodeId 962; Ordinal = 0; Group = NodeId 1 } ] }
    let imported0 = basis.Imports[NodeId 72]
    let call0 = basis.Calls[NodeId 1]
    let safeParams = (fst imported0.Parameters.Head, BoundaryScalar.Integer(64, false)) :: imported0.Parameters.Tail
    let safeArgs = { call0.Arguments.Head with Abi = BoundaryScalar.Integer(64, false) } :: call0.Arguments.Tail
    let imported, call =
        match mode with
        | "bad-import-return" ->
            { imported0 with Parameters = safeParams; Result = Some(BoundaryScalar.BorrowedBytes(NodeId 9999)) },
            { call0 with Arguments = safeArgs; Result = Some(BoundaryScalar.BorrowedBytes(NodeId 9999)) }
        | "arg-borrowed" ->
            { imported0 with Parameters = (fst imported0.Parameters.Head, BoundaryScalar.BorrowedBytes(NodeId 1200)) :: imported0.Parameters.Tail },
            { call0 with Arguments = { call0.Arguments.Head with Abi = BoundaryScalar.BorrowedBytes(NodeId 1200) } :: call0.Arguments.Tail }
        | _ ->
            { imported0 with Parameters = safeParams; Result = Some(BoundaryScalar.BorrowedBytes(NodeId 1200)) },
            { call0 with Arguments = safeArgs; Result = Some(BoundaryScalar.BorrowedBytes(NodeId 1200)) }
    let revision =
        { held with
            CurrentClaims = held.CurrentClaims.Add(NodeId 960, scopeClaim)
            Obligations = held.Obligations @ [scopeClaim]
            ObligationSources = held.ObligationSources.Add(NodeId 960, [[NodeId 1; NodeId 3]])
            Emission =
                { held.Emission with
                    Numeric = { held.Emission.Numeric with ForeignResultUses = [] }
                    Boundary =
                        { basis with
                            Imports = Map.ofList [NodeId 72, imported]
                            Calls = Map.ofList [NodeId 1, call]
                            WritableBufferDeclarations = Map.empty
                            WritableBufferUses = Map.empty
                            BorrowedResultViewDeclarations = Map.ofList [NodeId 1200, viewDecl]
                            BorrowedResultViewUses = Map.ofList [NodeId 1, viewUse] } } }
    let violations = Integrity.check revision
    if expectedPart = "" then
        Assert.Empty violations
    else
        Assert.Contains(violations, fun v -> v.Part = expectedPart)


[<Fact>]
let ``readonly declaration ignores trailing PassBy Fixed descriptor sentinel parameters`` () =
    let held = snapshotFacts
    let basis = boundaryCalleeFacts.Emission.Boundary
    let header = boundaryCalleeFacts.SourceReadings.ContextHeaders[NodeId 50]
    let integerType name kind =
        TypeIdentity.Application({Declaration = {Module = []; Name = name}; Parameters = []; NativeKind = Some kind}, [])
    let byteType = integerType "uint8" (NTUKind.NTUuint(NTUWidth.Fixed 8))
    let countType = integerType "uint64" (NTUKind.NTUuint(NTUWidth.Fixed 64))
    let arrayType = TypeIdentity.Application({Declaration = {Module = []; Name = "array"}; Parameters = [TypeParamKind.Type]; NativeKind = None}, [byteType])
    let unitType = held.Nodes[NodeId 1].Type
    let record fields ids parent = controlFact "record" fields [] ids (Some parent)
    let binding name child = controlFact "binding" [name] [0I;0I] [child] (Some 50)
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let number value parent = controlFact "integer" [] [value] [] (Some parent)
    let case name refs parent = controlFact "case" [name] [] refs (Some parent)
    let facts =
        [ 2, binding "readFn" 1003
          1003, controlFact "lambda" ["readFn"; "buf"; "count"] [2I; 0I; 0I] [1004; 1005; 1006] (Some 2)
          1004, {controlFact "formal" ["buf"] [] [] (Some 1003) with SourceType = arrayType}
          1005, {controlFact "formal" ["count"] [] [] (Some 1003) with SourceType = countType}
          1006, controlFact "unit" [] [] [] (Some 1003)
          1073, binding "readFnDescriptor" 1072
          1072, controlFact "quotation" [] [] [72] (Some 1073)
          72, record ["Parameters"; "CName"] [1010; 1020] 1072
          1010, controlFact "array" [] [] [1011; 1012; 1030] (Some 72)
          1011, record ["Type"; "PassBy"] [1013; 1016] 1010
          1013, case "Integer" [1014] 1011
          1014, controlFact "tuple" [] [] [1015; 1018] (Some 1013)
          1015, case "Unsigned" [] 1014
          1018, number 8I 1014
          1016, case "ReadOnlyReference" [] 1011
          1012, record ["Type"; "PassBy"] [1017; 1019] 1010
          1017, case "Integer" [1021] 1012
          1021, controlFact "tuple" [] [] [1022; 1023] (Some 1017)
          1022, case "Unsigned" [] 1021
          1023, number 64I 1021
          1019, case "Value" [] 1012
          1030, record ["Type"; "PassBy"] [1031; 1033] 1010
          1031, case "Pointer" [1032] 1030
          1032, number 64I 1031
          1033, case "Fixed" [1034] 1030
          1034, case "EntrySentinel" [1035; 1036] 1033
          1035, text "SQLITE_TRANSIENT" 1034
          1036, number (-1I) 1034
          1020, text "readFn" 72
          1101, binding "readFnReadOnlyDescriptor" 1100
          1100, controlFact "quotation" [] [] [1102] (Some 1101)
          1102, record ["Binding"; "Parameter"; "Extent"; "Content"; "Retention"; "Hypothesis"] [1103; 1104; 1105; 1115; 1111; 1106] 1100
          1103, text (header.Name + ".readFn") 1102
          1104, number 0I 1102
          1105, case "ExplicitCount" [1110] 1102
          1110, number 1I 1105
          1115, case "RawBytes" [] 1102
          1111, case "DuringCall" [] 1102
          1106, record ["Identity"; "Version"; "Source"] [1107; 1108; 1109] 1102
          1107, text "ro-fixed" 1106
          1108, text "1" 1106
          1109, text "fixture" 1106 ]
        |> List.map (fun (id, fact) -> NodeId id, fact) |> Map.ofList
    let roDecl : BoundaryReadOnlyBufferDeclaration =
        { Identity = NodeId 1100; Declaration = NodeId 2; Body = NodeId 1006
          Formals = [NodeId 1004; NodeId 1005]; Descriptor = NodeId 72
          Parameter = 0; CountParameter = Some 1
          BufferFormal = NodeId 1004; CountFormal = Some(NodeId 1005)
          Contract =
            { Binding = header.Name + ".readFn"; Parameter = 0
              Extent = BAREWire.Descriptors.ReadOnlyBufferExtent.ExplicitCount 1
              Content = BAREWire.Descriptors.BorrowedContent.RawBytes
              Retention = BAREWire.Descriptors.BufferRetention.DuringCall
              Hypothesis = { Identity = "ro-fixed"; Version = "1"; Source = "fixture" } }
          DeclarationFacts = facts
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.ReadOnlyBufferDeclaration; Node = NodeId 1100; Ordinal = 0; Group = NodeId 1100 }
              { Role = ParticipantRole.ReadOnlyBufferFormal; Node = NodeId 1004; Ordinal = 0; Group = NodeId 1100 }
              { Role = ParticipantRole.ReadOnlyBufferFormal; Node = NodeId 1005; Ordinal = 1; Group = NodeId 1100 } ] }
    let imported =
        { basis.Imports[NodeId 72] with
            Symbol = "readFn"
            Parameters = [NodeId 1004, BoundaryScalar.ReadOnlyBytes(NodeId 1100); NodeId 1005, BoundaryScalar.Integer(64, false)]
            Result = None; DeclarationFacts = facts; Participants = facts.Keys |> Set.ofSeq
            SourceTypes = Map.ofList [NodeId 1004, arrayType; NodeId 1005, countType; NodeId 1, unitType] }
    let call =
        { basis.Calls[NodeId 1] with
            Arguments =
                [ { Actual = NodeId 3; Formal = NodeId 1004; Abi = BoundaryScalar.ReadOnlyBytes(NodeId 1100); Adaptation = None; OptionalEntry = None; BufferAbsence = None }
                  { Actual = NodeId 4; Formal = NodeId 1005; Abi = BoundaryScalar.Integer(64, false); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
            Result = None; SourceTypes = imported.SourceTypes; Participants = facts.Keys |> Set.ofSeq }
    let countCarrier =
        { held.Emission.Numeric.Values[NodeId 4] with
            Slot = SettledSlot.Integer(64, Some "uint64"); SourceType = countType
            Range = ValueRange.Bounded(4I, 4I); Obligations = [] }
    let extentClaim =
        controlClaim "ro-extent" "foreign-readonly-buffer-extent"
            (ObligationBody.ZeroCopyBufferExtent
                { Call = NodeId 1; Declaration = NodeId 1100; Parameter = 0; CountParameter = 1
                  Buffer = NodeId 3; Count = NodeId 4; MinimumCount = 4I; MaximumCount = 4I
                  ExtentCapacity = 4I; ElementBytes = 1; CountCoverage = NodeId 951 })
    let retentionClaim =
        controlClaim "ro-ret" "foreign-buffer-retention-domination"
            (ObligationBody.BufferRetentionDomination
                { Call = NodeId 1; Declaration = NodeId 1100; Buffer = NodeId 3; Residence = NodeId 11
                  Mode = BufferRetentionMode.DuringCall; AcquireOrder = 1; RetirementOrders = [] })
    let roUse : BoundaryReadOnlyBufferUse =
        { Call = NodeId 1; Declaration = NodeId 1100; Parameter = 0; Buffer = NodeId 3
          Residence = NodeId 11; Retirements = []; Copies = 0
          Crossing = BoundaryReadOnlyBufferCrossing.ExplicitZeroCopy(1, NodeId 4, 4I, NodeId 951)
          RetentionProof = NodeId 952; AccessExclusivityProof = None
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.ReadOnlyBufferCall; Node = NodeId 1; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.ReadOnlyBufferDeclaration; Node = NodeId 1100; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.ReadOnlyBufferActual; Node = NodeId 3; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.ReadOnlyBufferResidence; Node = NodeId 11; Ordinal = 0; Group = NodeId 1 } ] }
    let callNode = { held.Nodes[NodeId 1] with Kind = SemanticKind.Application(NodeId 2, [NodeId 3; NodeId 4]); Children = [NodeId 2; NodeId 3; NodeId 4]; Type = unitType }
    let revision =
        { held with
            Nodes = held.Nodes.Add(NodeId 1, callNode)
            CurrentClaims = held.CurrentClaims.Add(NodeId 951, extentClaim).Add(NodeId 952, retentionClaim)
            Obligations = held.Obligations @ [extentClaim; retentionClaim]
            ObligationSources = held.ObligationSources.Add(NodeId 951, [[NodeId 1; NodeId 3]]).Add(NodeId 952, [[NodeId 1; NodeId 3]])
            Emission =
                { held.Emission with
                    Boundary =
                        { basis with
                            Imports = Map.ofList [NodeId 72, imported]
                            Calls = Map.ofList [NodeId 1, call]
                            ReadOnlyBufferDeclarations = Map.ofList [NodeId 1100, roDecl]
                            ReadOnlyBufferUses = Map.ofList [(NodeId 1, 0), roUse] }
                    Numeric =
                        { held.Emission.Numeric with
                            Operations = Map.empty; OperationRequired = Set.empty; ResultSites = Set.empty
                            Required = Set.singleton(NodeId 4)
                            Values = held.Emission.Numeric.Values.Remove(NodeId 1).Add(NodeId 4, countCarrier) } } }
        |> covered
    let revision =
        { revision with
            SourceReadings =
                { revision.SourceReadings with
                    ContextHeaders = revision.SourceReadings.ContextHeaders.Add(NodeId 50, header)
                    Contexts = revision.SourceReadings.Contexts.Add(NodeId 50, [[]])
                    Ports = revision.SourceReadings.Ports.Add((NodeId 50, OccurrencePort.ModuleDeclaration), header.Ports[OccurrencePort.ModuleDeclaration]) } }
    Assert.Empty(Integrity.check revision)

[<Theory>]
[<InlineData("borrowed-declared-resource", "")>]
[<InlineData("borrowed-chandle-formal", "")>]
[<InlineData("borrowed-nullable-chandle-formal", "")>]
[<InlineData("unwitnessed-arbitrary-node", "Emission.Boundary.Calls.Resource")>]
[<InlineData("non-chandle-formal", "Emission.Boundary.Calls.Resource")>]
[<InlineData("unwitnessed-result", "Emission.Boundary.Calls.Resource")>]
let ``non-acquiring call admits borrowed ResourceHandle arguments and forbids ResourceHandle return`` mode expectedPart =
    let held = resourceReleaseSignatureControl "void"
    let basis = boundaryCalleeFacts.Emission.Boundary
    let imported0 = basis.Imports |> Map.values |> Seq.head
    let call0 = basis.Calls[NodeId 1]
    let sqliteMarker = TypeIdentity.Application({ Declaration = { Module = []; Name = "sqlite3_context" }; Parameters = []; NativeKind = None }, [])
    let cHandleType = TypeIdentity.Application({ Declaration = { Module = []; Name = "CHandle" }; Parameters = [TypeParamKind.Type]; NativeKind = Some NTUKind.NTUptr }, [sqliteMarker])
    let optionCHandleType = TypeIdentity.Application({ Declaration = { Module = []; Name = "option" }; Parameters = [TypeParamKind.Type]; NativeKind = None }, [cHandleType])
    let formalId = fst imported0.Parameters.Head
    let targetId, isNullable =
        match mode with
        | "borrowed-declared-resource" -> NodeId 7000, false
        | "borrowed-nullable-chandle-formal" -> formalId, true
        | "borrowed-chandle-formal" | "non-chandle-formal" -> formalId, false
        | _ -> NodeId 2, false
    let handleAbi = BoundaryScalar.ResourceHandle(targetId, isNullable)
    let formalType =
        match mode with
        | "borrowed-chandle-formal" -> Some cHandleType
        | "borrowed-nullable-chandle-formal" -> Some optionCHandleType
        | _ -> None
    let updatedFacts =
        match mode with
        | "borrowed-chandle-formal" | "borrowed-nullable-chandle-formal" | "non-chandle-formal" ->
            imported0.DeclarationFacts.Add(formalId, controlFact "formal" ["ctx"] [] [] (Some 2))
        | _ -> imported0.DeclarationFacts
    let updatedSourceTypes =
        match formalType with
        | Some ty -> imported0.SourceTypes.Add(formalId, ty)
        | None -> imported0.SourceTypes
    let imported, call =
        if mode = "unwitnessed-result" then
            { imported0 with Result = Some(BoundaryScalar.ResourceHandle(NodeId 7000, true)) },
            { call0 with Resource = None; Result = Some(BoundaryScalar.ResourceHandle(NodeId 7000, true)) }
        else
            { imported0 with
                Parameters = (formalId, handleAbi) :: imported0.Parameters.Tail
                Result = None
                DeclarationFacts = updatedFacts
                SourceTypes = updatedSourceTypes },
            { call0 with
                Resource = None; Result = None
                Arguments = { call0.Arguments.Head with Abi = handleAbi } :: call0.Arguments.Tail
                SourceTypes = updatedSourceTypes }
    let boundary =
        { basis with
            ResourceDeclarations =
                if mode = "borrowed-declared-resource" then held.Emission.Boundary.ResourceDeclarations
                else basis.ResourceDeclarations
            Imports = Map.add imported.Identity imported basis.Imports
            Calls = Map.add call.Site call basis.Calls }
    let violations = Integrity.check { boundaryCalleeFacts with Emission = { boundaryCalleeFacts.Emission with Boundary = boundary } }
    if expectedPart = "" then
        Assert.Empty violations
    else
        Assert.Contains(violations, fun v -> v.Part = expectedPart)

[<Theory>]
[<InlineData("contracted-chandle-formal", "")>]
[<InlineData("contracted-context", "")>]
[<InlineData("bogus-node-handle", "Emission.Boundary.CallbackInvocations.Signature")>]
[<InlineData("non-chandle-formal-handle", "Emission.Boundary.CallbackInvocations.Signature")>]
[<InlineData("forged-context-record", "Emission.Boundary.CallbackInvocations.Signature")>]
[<InlineData("raw-pointer", "Emission.Boundary.CallbackInvocations.Signature")>]
[<InlineData("missing-platform-pointer", "Emission.Boundary.CallbackInvocations.Signature")>]
let ``callback signature admits contracted pointer parameters while rejecting raw pointers`` mode expectedPart =
    let held = optionalBoundaryControl true
    let basis = held.Emission.Boundary
    let receiver0 = basis.CallbackInvocations[NodeId 220]
    let imported0 = basis.Imports[receiver0.Import]
    let sqliteMarker = TypeIdentity.Application({ Declaration = { Module = []; Name = "sqlite3_context" }; Parameters = []; NativeKind = None }, [])
    let cHandleType = TypeIdentity.Application({ Declaration = { Module = []; Name = "CHandle" }; Parameters = [TypeParamKind.Type]; NativeKind = Some NTUKind.NTUptr }, [sqliteMarker])
    let int32Type = TypeIdentity.Application({ Declaration = { Module = []; Name = "int32" }; Parameters = []; NativeKind = Some(NTUKind.NTUint(NTUWidth.Fixed 32)) }, [])
    let fnPtrCHandleType =
        TypeIdentity.Application(
            { Declaration = { Module = []; Name = "entry" }; Parameters = [TypeParamKind.Type]; NativeKind = Some NTUKind.NTUfnptr },
            [ TypeIdentity.Function(cHandleType, int32Type) ])
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let number value parent = controlFact "integer" [] [value] [] (Some parent)
    let record fields refs parent = controlFact "record" fields [] refs (Some parent)
    let ctxType = TypeIdentity.Application({ Declaration = { Module = ["BAREWire"; "Descriptors"]; Name = "CallbackContextDescriptor" }; Parameters = []; NativeKind = None }, [])
    let contextQuotationFacts =
        [ 801, { controlFact "binding" ["cbCtx"] [0I; 0I] [800] (Some 400) with SourceType = ctxType }
          800, { controlFact "quotation" [] [1I] [802] (Some 801) with SourceType = ctxType }
          802, { record ["Binding"; "Parameter"; "Argument"; "ContextParameter"] [803; 804; 805; 806] 800 with SourceType = ctxType }
          803, text receiver0.Contract.Binding 802
          804, number 0I 802
          805, number 0I 802
          806, number 1I 802 ]
        |> List.map (fun (id, fact) -> NodeId id, fact)
    let forgedRecordFacts =
        [ 802, record ["Binding"; "Parameter"; "Argument"; "ContextParameter"] [803; 804; 805; 806] 210
          803, text receiver0.Contract.Binding 802
          804, number 0I 802
          805, number 0I 802
          806, number 1I 802 ]
        |> List.map (fun (id, fact) -> NodeId id, fact)
    let pointerSignature : BAREWire.Descriptors.EntrySignature =
        { Parameters =
            [| { Name = "ctx"; Type = BAREWire.Descriptors.TypeRef.Pointer 64; PassBy = BAREWire.Descriptors.PassBy.Value } |]
          ReturnType = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 32)
          CallingConvention = BAREWire.Descriptors.CallConv.CDecl }
    let boundary, rev =
        match mode with
        | "contracted-chandle-formal" | "missing-platform-pointer" ->
            let desc215 = NodeId 2150
            let formal216 = NodeId 216
            let inv225 = NodeId 225
            let imp215 =
                { imported0 with
                    Identity = desc215
                    Parameters = [formal216, BoundaryScalar.Entry inv225]
                    DeclarationFacts =
                        imported0.DeclarationFacts
                            .Add(desc215, imported0.DeclarationFacts[NodeId 210])
                            .Add(formal216, { controlFact "formal" ["ctxCb"] [] [] (Some 215) with SourceType = fnPtrCHandleType })
                            .Add(inv225, imported0.DeclarationFacts[NodeId 220])
                    SourceTypes = Map.ofList [formal216, fnPtrCHandleType]
                    Participants = imported0.Participants.Add(desc215).Add(formal216).Add(inv225) }
            let receiver225 =
                { receiver0 with
                    Identity = inv225; Import = imp215.Identity; Formal = formal216
                    Contract = { receiver0.Contract with Signature = pointerSignature }
                    Signature = { receiver0.Signature with Parameters = [BoundaryScalar.ResourceHandle(formal216, false)] }
                    Participants = receiver0.Participants.Add(inv225).Add(imp215.Identity).Add(formal216) }
            let b =
                { basis with
                    Imports = basis.Imports.Add(imp215.Identity, imp215)
                    CallbackInvocations = basis.CallbackInvocations.Add(receiver225.Identity, receiver225) }
            b,
            { held with
                Platform = if mode = "missing-platform-pointer" then { held.Platform with Pointer = Error "missing" } else held.Platform
                Emission = { held.Emission with Boundary = b } }
        | _ ->
            let paramAbi, extraFacts =
                match mode with
                | "contracted-context" -> BoundaryScalar.Integer(64, false), contextQuotationFacts
                | "forged-context-record" -> BoundaryScalar.Integer(64, false), forgedRecordFacts
                | "non-chandle-formal-handle" -> BoundaryScalar.ResourceHandle(receiver0.Formal, false), []
                | "bogus-node-handle" -> BoundaryScalar.ResourceHandle(NodeId 1, false), []
                | _ -> BoundaryScalar.Integer(64, false), []
            let mergedImport =
                { imported0 with
                    DeclarationFacts = (imported0.DeclarationFacts, extraFacts) ||> List.fold (fun m (k, v) -> Map.add k v m) }
            let receiver =
                { receiver0 with
                    Contract = { receiver0.Contract with Signature = pointerSignature }
                    Signature = { receiver0.Signature with Parameters = [paramAbi] } }
            let b =
                { basis with
                    Imports = basis.Imports.Add(mergedImport.Identity, mergedImport)
                    CallbackInvocations = basis.CallbackInvocations.Add(receiver.Identity, receiver) }
            b, { held with Emission = { held.Emission with Boundary = b } }
    ignore boundary
    let violations = Integrity.check rev
    if expectedPart = "" then
        Assert.Empty violations
    else
        Assert.Contains(violations, fun v -> v.Part = expectedPart)

[<Fact>]
let ``retained callback invocation is admitted alongside callback absence`` () =
    let held = optionalBoundaryControl true
    let basis = held.Emission.Boundary
    let receiver0 = basis.CallbackInvocations[NodeId 220]
    let imported0 = basis.Imports[receiver0.Import]
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let number value parent = controlFact "integer" [] [value] [] (Some parent)
    let case name refs parent = controlFact "case" [name] [] refs (Some parent)
    let record fields refs parent = controlFact "record" fields [] refs (Some parent)
    let retainedFacts =
        imported0.DeclarationFacts
        |> Map.add (NodeId 212) (controlFact "array" [] [] [218; 245] (Some 210))
        |> Map.add (NodeId 245) (record ["Type"; "PassBy"] [246; 249] 212)
        |> Map.add (NodeId 246) (case "Integer" [247] 245)
        |> Map.add (NodeId 247) (controlFact "tuple" [] [] [248; 250] (Some 246))
        |> Map.add (NodeId 248) (case "Signed" [] 247)
        |> Map.add (NodeId 250) (number 32I 247)
        |> Map.add (NodeId 249) (case "Value" [] 245)
        |> Map.add (NodeId 602) { record ["Binding"; "Parameter"; "Owner"; "Releases"] [603; 604; 605; 606] 600 with SourceType = TypeIdentity.Application({ Declaration = { Module = ["BAREWire"; "Descriptors"]; Name = "RetainedCallbackDescriptor" }; Parameters = []; NativeKind = None }, []) }
        |> Map.add (NodeId 605) (number 1I 602)
        |> Map.add (NodeId 606) (controlFact "array" [] [] [607] (Some 602))
        |> Map.add (NodeId 607) (case "OwnerRelease" [608] 606)
        |> Map.add (NodeId 608) (record ["Binding"; "Parameter"] [609; 610] 607)
        |> Map.add (NodeId 609) (text "OptionalControl.close" 608)
        |> Map.add (NodeId 610) (number 0I 608)
    let ownerDecl =
        { imported0 with
            Parameters = imported0.Parameters @ [NodeId 211, BoundaryScalar.Integer(32, true)]
            DeclarationFacts = retainedFacts }
    let receiver =
        { receiver0 with
            Extent = BoundaryCallbackExtent.Retained(1, [| BAREWire.Descriptors.RetentionRelease.OwnerRelease { Binding = "OptionalControl.close"; Parameter = 0 } |]) }
    let boundary =
        { basis with
            Imports = basis.Imports.Add(ownerDecl.Identity, ownerDecl)
            CallbackInvocations = basis.CallbackInvocations.Add(receiver.Identity, receiver) }
    let violations = Integrity.check { held with Emission = { held.Emission with Boundary = boundary } }
    Assert.DoesNotContain(violations, fun v -> v.Part.StartsWith("Emission.Boundary.Callback", System.StringComparison.Ordinal) || v.Part.Contains "OptionalEntry")

[<Theory>]
[<InlineData("wrong-owner", "Emission.Boundary.CallbackInvocations.RetainedExtent")>]
[<InlineData("wrong-releases", "Emission.Boundary.CallbackInvocations.RetainedExtent")>]
[<InlineData("wrong-parameter", "Emission.Boundary.CallbackInvocations.RetainedExtent")>]
let ``retained callback invocation rejects owner release or parameter quotation mismatch`` mode expectedPart =
    let held = optionalBoundaryControl false
    let basis = held.Emission.Boundary
    let receiver0 = basis.CallbackInvocations[NodeId 220]
    let imported0 = basis.Imports[receiver0.Import]
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let number value parent = controlFact "integer" [] [value] [] (Some parent)
    let case name refs parent = controlFact "case" [name] [] refs (Some parent)
    let record fields refs parent = controlFact "record" fields [] refs (Some parent)
    let quotedOwner = if mode = "wrong-owner" then 0I else 1I
    let quotedRelease = if mode = "wrong-releases" then "OptionalControl.wrong" else "OptionalControl.close"
    let quotedParam = if mode = "wrong-parameter" then "wrongParam" else "callback"
    let retainedFacts =
        imported0.DeclarationFacts
        |> Map.add (NodeId 212) (controlFact "array" [] [] [218; 245] (Some 210))
        |> Map.add (NodeId 245) (record ["Type"; "PassBy"] [246; 249] 212)
        |> Map.add (NodeId 246) (case "Integer" [247] 245)
        |> Map.add (NodeId 247) (controlFact "tuple" [] [] [248; 250] (Some 246))
        |> Map.add (NodeId 248) (case "Signed" [] 247)
        |> Map.add (NodeId 250) (number 32I 247)
        |> Map.add (NodeId 249) (case "Value" [] 245)
        |> Map.add (NodeId 604) (text quotedParam 602)
        |> Map.add (NodeId 602) { record ["Binding"; "Parameter"; "Owner"; "Releases"] [603; 604; 605; 606] 600 with SourceType = TypeIdentity.Application({ Declaration = { Module = ["BAREWire"; "Descriptors"]; Name = "RetainedCallbackDescriptor" }; Parameters = []; NativeKind = None }, []) }
        |> Map.add (NodeId 605) (number quotedOwner 602)
        |> Map.add (NodeId 606) (controlFact "array" [] [] [607] (Some 602))
        |> Map.add (NodeId 607) (case "OwnerRelease" [608] 606)
        |> Map.add (NodeId 608) (record ["Binding"; "Parameter"] [609; 610] 607)
        |> Map.add (NodeId 609) (text quotedRelease 608)
        |> Map.add (NodeId 610) (number 0I 608)
    let ownerDecl =
        { imported0 with
            Parameters = imported0.Parameters @ [NodeId 211, BoundaryScalar.Integer(32, true)]
            DeclarationFacts = retainedFacts }
    let receiver =
        { receiver0 with
            Extent = BoundaryCallbackExtent.Retained(1, [| BAREWire.Descriptors.RetentionRelease.OwnerRelease { Binding = "OptionalControl.close"; Parameter = 0 } |]) }
    let boundary =
        { basis with
            Imports = basis.Imports.Add(ownerDecl.Identity, ownerDecl)
            CallbackInvocations = basis.CallbackInvocations.Add(receiver.Identity, receiver) }
    let violations = Integrity.check { held with Emission = { held.Emission with Boundary = boundary } }
    Assert.Contains(violations, fun v -> v.Part = expectedPart)

[<Theory>]
[<InlineData("valid-pointer-value", "")>]
[<InlineData("reject-mutable-reference", "Emission.Boundary.ReadOnlyBufferDeclarations.Ordinals")>]
let ``readonly buffer declaration admits Pointer Value ABI while rejecting mutable Reference`` mode expectedPart =
    let held = snapshotFacts
    let basis = boundaryCalleeFacts.Emission.Boundary
    let header = boundaryCalleeFacts.SourceReadings.ContextHeaders[NodeId 50]
    let integerType name kind =
        TypeIdentity.Application({Declaration = {Module = []; Name = name}; Parameters = []; NativeKind = Some kind}, [])
    let byteType = integerType "uint8" (NTUKind.NTUuint(NTUWidth.Fixed 8))
    let countType = integerType "uint64" (NTUKind.NTUuint(NTUWidth.Fixed 64))
    let arrayType = TypeIdentity.Application({Declaration = {Module = []; Name = "array"}; Parameters = [TypeParamKind.Type]; NativeKind = None}, [byteType])
    let unitType = held.Nodes[NodeId 1].Type
    let record fields ids parent = controlFact "record" fields [] ids (Some parent)
    let binding name child = controlFact "binding" [name] [0I;0I] [child] (Some 50)
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let number value parent = controlFact "integer" [] [value] [] (Some parent)
    let case name refs parent = controlFact "case" [name] [] refs (Some parent)
    let paramTypeFacts =
        if mode = "valid-pointer-value" then
            [ 1013, case "Pointer" [1014] 1011
              1014, number 64I 1013
              1016, case "Value" [] 1011 ]
        else
            [ 1013, case "Integer" [1014] 1011
              1014, controlFact "tuple" [] [] [1015; 1018] (Some 1013)
              1015, case "Unsigned" [] 1014
              1018, number 8I 1014
              1016, case "Reference" [] 1011 ]
    let facts =
        ([ 2, binding "readFn" 1003
           1003, controlFact "lambda" ["readFn"; "buf"; "count"] [2I; 0I; 0I] [1004; 1005; 1006] (Some 2)
           1004, {controlFact "formal" ["buf"] [] [] (Some 1003) with SourceType = arrayType}
           1005, {controlFact "formal" ["count"] [] [] (Some 1003) with SourceType = countType}
           1006, controlFact "unit" [] [] [] (Some 1003)
           1073, binding "readFnDescriptor" 1072
           1072, controlFact "quotation" [] [] [72] (Some 1073)
           72, record ["Parameters"; "CName"] [1010; 1020] 1072
           1010, controlFact "array" [] [] [1011; 1012] (Some 72)
           1011, record ["Type"; "PassBy"] [1013; 1016] 1010
           1012, record ["Type"; "PassBy"] [1017; 1019] 1010
           1017, case "Integer" [1021] 1012
           1021, controlFact "tuple" [] [] [1022; 1023] (Some 1017)
           1022, case "Unsigned" [] 1021
           1023, number 64I 1021
           1019, case "Value" [] 1012
           1020, text "readFn" 72
           1101, binding "readFnReadOnlyDescriptor" 1100
           1100, controlFact "quotation" [] [] [1102] (Some 1101)
           1102, record ["Binding"; "Parameter"; "Extent"; "Content"; "Retention"; "Hypothesis"] [1103; 1104; 1105; 1115; 1111; 1106] 1100
           1103, text (header.Name + ".readFn") 1102
           1104, number 0I 1102
           1105, case "ExplicitCount" [1110] 1102
           1110, number 1I 1105
           1115, case "RawBytes" [] 1102
           1111, case "DuringCall" [] 1102
           1106, record ["Identity"; "Version"; "Source"] [1107; 1108; 1109] 1102
           1107, text "ro-abi" 1106
           1108, text "1" 1106
           1109, text "fixture" 1106 ] @ paramTypeFacts)
        |> List.map (fun (id, fact) -> NodeId id, fact) |> Map.ofList
    let roDecl : BoundaryReadOnlyBufferDeclaration =
        { Identity = NodeId 1100; Declaration = NodeId 2; Body = NodeId 1006
          Formals = [NodeId 1004; NodeId 1005]; Descriptor = NodeId 72
          Parameter = 0; CountParameter = Some 1
          BufferFormal = NodeId 1004; CountFormal = Some(NodeId 1005)
          Contract =
            { Binding = header.Name + ".readFn"; Parameter = 0
              Extent = BAREWire.Descriptors.ReadOnlyBufferExtent.ExplicitCount 1
              Content = BAREWire.Descriptors.BorrowedContent.RawBytes
              Retention = BAREWire.Descriptors.BufferRetention.DuringCall
              Hypothesis = { Identity = "ro-abi"; Version = "1"; Source = "fixture" } }
          DeclarationFacts = facts
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.ReadOnlyBufferDeclaration; Node = NodeId 1100; Ordinal = 0; Group = NodeId 1100 }
              { Role = ParticipantRole.ReadOnlyBufferFormal; Node = NodeId 1004; Ordinal = 0; Group = NodeId 1100 }
              { Role = ParticipantRole.ReadOnlyBufferFormal; Node = NodeId 1005; Ordinal = 1; Group = NodeId 1100 } ] }
    let imported =
        { basis.Imports[NodeId 72] with
            Symbol = "readFn"
            Parameters = [NodeId 1004, BoundaryScalar.ReadOnlyBytes(NodeId 1100); NodeId 1005, BoundaryScalar.Integer(64, false)]
            Result = None; DeclarationFacts = facts; Participants = facts.Keys |> Set.ofSeq
            SourceTypes = Map.ofList [NodeId 1004, arrayType; NodeId 1005, countType; NodeId 1, unitType] }
    let call =
        { basis.Calls[NodeId 1] with
            Arguments =
                [ { Actual = NodeId 3; Formal = NodeId 1004; Abi = BoundaryScalar.ReadOnlyBytes(NodeId 1100); Adaptation = None; OptionalEntry = None; BufferAbsence = None }
                  { Actual = NodeId 4; Formal = NodeId 1005; Abi = BoundaryScalar.Integer(64, false); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
            Result = None; SourceTypes = imported.SourceTypes; Participants = facts.Keys |> Set.ofSeq }
    let countCarrier =
        { held.Emission.Numeric.Values[NodeId 4] with
            Slot = SettledSlot.Integer(64, Some "uint64"); SourceType = countType
            Range = ValueRange.Bounded(4I, 4I); Obligations = [] }
    let extentClaim =
        controlClaim "ro-extent" "foreign-readonly-buffer-extent"
            (ObligationBody.ZeroCopyBufferExtent
                { Call = NodeId 1; Declaration = NodeId 1100; Parameter = 0; CountParameter = 1
                  Buffer = NodeId 3; Count = NodeId 4; MinimumCount = 4I; MaximumCount = 4I
                  ExtentCapacity = 4I; ElementBytes = 1; CountCoverage = NodeId 951 })
    let retentionClaim =
        controlClaim "ro-ret" "foreign-buffer-retention-domination"
            (ObligationBody.BufferRetentionDomination
                { Call = NodeId 1; Declaration = NodeId 1100; Buffer = NodeId 3; Residence = NodeId 11
                  Mode = BufferRetentionMode.DuringCall; AcquireOrder = 1; RetirementOrders = [] })
    let roUse : BoundaryReadOnlyBufferUse =
        { Call = NodeId 1; Declaration = NodeId 1100; Parameter = 0; Buffer = NodeId 3
          Residence = NodeId 11; Retirements = []; Copies = 0
          Crossing = BoundaryReadOnlyBufferCrossing.ExplicitZeroCopy(1, NodeId 4, 4I, NodeId 951)
          RetentionProof = NodeId 952; AccessExclusivityProof = None
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.ReadOnlyBufferCall; Node = NodeId 1; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.ReadOnlyBufferDeclaration; Node = NodeId 1100; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.ReadOnlyBufferActual; Node = NodeId 3; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.ReadOnlyBufferResidence; Node = NodeId 11; Ordinal = 0; Group = NodeId 1 } ] }
    let callNode = { held.Nodes[NodeId 1] with Kind = SemanticKind.Application(NodeId 2, [NodeId 3; NodeId 4]); Children = [NodeId 2; NodeId 3; NodeId 4]; Type = unitType }
    let revision =
        { held with
            Nodes = held.Nodes.Add(NodeId 1, callNode)
            CurrentClaims = held.CurrentClaims.Add(NodeId 951, extentClaim).Add(NodeId 952, retentionClaim)
            Obligations = held.Obligations @ [extentClaim; retentionClaim]
            ObligationSources = held.ObligationSources.Add(NodeId 951, [[NodeId 1; NodeId 3]]).Add(NodeId 952, [[NodeId 1; NodeId 3]])
            Emission =
                { held.Emission with
                    Boundary =
                        { basis with
                            Imports = Map.ofList [NodeId 72, imported]
                            Calls = Map.ofList [NodeId 1, call]
                            ReadOnlyBufferDeclarations = Map.ofList [NodeId 1100, roDecl]
                            ReadOnlyBufferUses = Map.ofList [(NodeId 1, 0), roUse] }
                    Numeric =
                        { held.Emission.Numeric with
                            Operations = Map.empty; OperationRequired = Set.empty; ResultSites = Set.empty
                            Required = Set.singleton(NodeId 4)
                            Values = held.Emission.Numeric.Values.Remove(NodeId 1).Add(NodeId 4, countCarrier) } } }
        |> covered
    let revision =
        { revision with
            SourceReadings =
                { revision.SourceReadings with
                    ContextHeaders = revision.SourceReadings.ContextHeaders.Add(NodeId 50, header)
                    Contexts = revision.SourceReadings.Contexts.Add(NodeId 50, [[]])
                    Ports = revision.SourceReadings.Ports.Add((NodeId 50, OccurrencePort.ModuleDeclaration), header.Ports[OccurrencePort.ModuleDeclaration]) } }
    let violations = Integrity.check revision
    if expectedPart = "" then Assert.Empty violations
    else Assert.Contains(violations, fun v -> v.Part = expectedPart)

[<Fact>]
let ``positive buffer absence account passes with None-to-null choice and current plan claim`` () =
    let held = snapshotFacts
    let basis = boundaryCalleeFacts.Emission.Boundary
    let header = boundaryCalleeFacts.SourceReadings.ContextHeaders[NodeId 50]
    let byteType = TypeIdentity.Application({Declaration = {Module = []; Name = "uint8"}; Parameters = []; NativeKind = Some(NTUKind.NTUuint(NTUWidth.Fixed 8))}, [])
    let arrayType = TypeIdentity.Application({Declaration = {Module = []; Name = "array"}; Parameters = [TypeParamKind.Type]; NativeKind = None}, [byteType])
    let optionArrayType = TypeIdentity.Application({Declaration = {Module = []; Name = "option"}; Parameters = [TypeParamKind.Type]; NativeKind = None}, [arrayType])
    let unitType = held.Nodes[NodeId 1].Type
    let record fields ids parent = controlFact "record" fields [] ids (Some parent)
    let binding name child = controlFact "binding" [name] [0I;0I] [child] (Some 50)
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let number value parent = controlFact "integer" [] [value] [] (Some parent)
    let case name refs parent = controlFact "case" [name] [] refs (Some parent)
    let facts =
        [ 2, binding "openVfs" 1003
          1003, controlFact "lambda" ["openVfs"; "vfs"] [1I; 0I; 0I] [1004; 1006] (Some 2)
          1004, {controlFact "formal" ["vfs"] [] [] (Some 1003) with SourceType = optionArrayType}
          1006, controlFact "unit" [] [] [] (Some 1003)
          1073, binding "openVfsDescriptor" 1072
          1072, controlFact "quotation" [] [] [72] (Some 1073)
          72, record ["Parameters"; "CName"] [1010; 1020] 1072
          1010, controlFact "array" [] [] [1011] (Some 72)
          1011, record ["Type"; "PassBy"] [1013; 1016] 1010
          1013, case "Pointer" [1014] 1011
          1014, number 64I 1013
          1016, case "Value" [] 1011
          1020, text "openVfs" 72
          1101, binding "openVfsReadOnlyDescriptor" 1100
          1100, controlFact "quotation" [] [] [1102] (Some 1101)
          1102, record ["Binding"; "Parameter"; "Extent"; "Content"; "Retention"; "Hypothesis"] [1103; 1104; 1105; 1115; 1111; 1106] 1100
          1103, text (header.Name + ".openVfs") 1102
          1104, number 0I 1102
          1105, case "UncountedNulTerminated" [] 1102
          1115, case "Utf8Text" [] 1102
          1111, case "DuringCall" [] 1102
          1106, record ["Identity"; "Version"; "Source"] [1107; 1108; 1109] 1102
          1107, text "ro-abs" 1106
          1108, text "1" 1106
          1109, text "fixture" 1106
          701, binding "openVfsBufferAbsence" 700
          700, controlFact "quotation" [] [] [702] (Some 701)
          702, { record ["Binding"; "Parameter"; "Hypothesis"] [703; 704; 705] 700 with
                    SourceType = TypeIdentity.Application({ Declaration = { Module = ["BAREWire"; "Descriptors"]; Name = "BufferAbsenceContract" }; Parameters = []; NativeKind = None }, []) }
          703, text (header.Name + ".openVfs") 702
          704, number 0I 702
          705, record ["Identity"; "Version"; "Source"] [706; 707; 708] 702
          706, text "abs-hyp" 705
          707, text "1" 705
          708, text "fixture" 705 ]
        |> List.map (fun (id, fact) -> NodeId id, fact) |> Map.ofList
    let roDecl : BoundaryReadOnlyBufferDeclaration =
        { Identity = NodeId 1100; Declaration = NodeId 2; Body = NodeId 1006
          Formals = [NodeId 1004]; Descriptor = NodeId 72
          Parameter = 0; CountParameter = None
          BufferFormal = NodeId 1004; CountFormal = None
          Contract =
            { Binding = header.Name + ".openVfs"; Parameter = 0
              Extent = BAREWire.Descriptors.ReadOnlyBufferExtent.UncountedNulTerminated
              Content = BAREWire.Descriptors.BorrowedContent.Utf8Text
              Retention = BAREWire.Descriptors.BufferRetention.DuringCall
              Hypothesis = { Identity = "ro-abs"; Version = "1"; Source = "fixture" } }
          DeclarationFacts = facts
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.ReadOnlyBufferDeclaration; Node = NodeId 1100; Ordinal = 0; Group = NodeId 1100 }
              { Role = ParticipantRole.ReadOnlyBufferFormal; Node = NodeId 1004; Ordinal = 0; Group = NodeId 1100 } ] }
    let absence : BoundaryBufferAbsence =
        { Quote = NodeId 700; DescriptorBinding = NodeId 701; Record = NodeId 702
          Import = NodeId 72; Parameter = 0; Formal = NodeId 1004; BufferDeclaration = NodeId 1100
          Contract = { Binding = header.Name + ".openVfs"; Parameter = 0; Hypothesis = { Identity = "abs-hyp"; Version = "1"; Source = "fixture" } }
          SourcePath = [NodeId 700; NodeId 702]
          Inputs =
            [ BufferAbsenceInputRole.Binding, [NodeId 703]
              BufferAbsenceInputRole.Parameter, [NodeId 704]
              BufferAbsenceInputRole.Hypothesis, [NodeId 705]
              BufferAbsenceInputRole.HypothesisIdentity, [NodeId 706]
              BufferAbsenceInputRole.HypothesisVersion, [NodeId 707]
              BufferAbsenceInputRole.HypothesisSource, [NodeId 708] ]
          DeclarationFacts = [700..708] |> List.map (fun id -> NodeId id, facts[NodeId id]) |> Map.ofList }
    let sel : BoundaryBufferAbsenceSelection =
        { Construction = NodeId 3; CaseOrdinal = 0; Payload = None; Absence = NodeId 700
          Transport = [NodeId 3]; Obligation = NodeId 958 }
    let absClaim =
        controlClaim "abs-none" "foreign-buffer-absence-conversion-0"
            (ObligationBody.BufferAbsenceArgumentConversion
                { Call = NodeId 1; Parameter = 0; Actual = NodeId 3; Construction = NodeId 3; SourceCase = 0
                  Absence = NodeId 700
                  Arms = [ { CaseOrdinal = 0; Choice = BufferAbsencePlanChoice.AbsentNull }
                           { CaseOrdinal = 1; Choice = BufferAbsencePlanChoice.RequiresNonNullBuffer } ] })
    let imported =
        { basis.Imports[NodeId 72] with
            Symbol = "openVfs"; Parameters = [NodeId 1004, BoundaryScalar.ReadOnlyBytes(NodeId 1100)]; Result = None
            DeclarationFacts = facts; Participants = facts.Keys |> Set.ofSeq
            SourceTypes = Map.ofList [NodeId 1004, optionArrayType; NodeId 1, unitType] }
    let call =
        { basis.Calls[NodeId 1] with
            Arguments = [ { Actual = NodeId 3; Formal = NodeId 1004; Abi = BoundaryScalar.ReadOnlyBytes(NodeId 1100); Adaptation = None; OptionalEntry = None; BufferAbsence = Some(BoundaryBufferAbsenceChoice.Direct sel) } ]
            Result = None; SourceTypes = imported.SourceTypes; Participants = facts.Keys |> Set.ofSeq }
    let callNode = { held.Nodes[NodeId 1] with Kind = SemanticKind.Application(NodeId 2, [NodeId 3]); Children = [NodeId 2; NodeId 3]; Type = unitType }
    let revision =
        { held with
            Nodes = held.Nodes.Add(NodeId 1, callNode)
            CurrentClaims = held.CurrentClaims.Add(NodeId 958, absClaim)
            Obligations = held.Obligations @ [absClaim]
            ObligationSources = held.ObligationSources.Add(NodeId 958, [[NodeId 1; NodeId 3]])
            Emission =
                { held.Emission with
                    Boundary =
                        { basis with
                            Imports = Map.ofList [NodeId 72, imported]
                            Calls = Map.ofList [NodeId 1, call]
                            ReadOnlyBufferDeclarations = Map.ofList [NodeId 1100, roDecl]
                            BufferAbsences = Map.ofList [NodeId 700, absence] }
                    Numeric =
                        { held.Emission.Numeric with
                            Operations = Map.empty; OperationRequired = Set.empty; ResultSites = Set.empty
                            Required = Set.empty; Values = held.Emission.Numeric.Values.Remove(NodeId 1) } } }
        |> covered
    let revision =
        { revision with
            SourceReadings =
                { revision.SourceReadings with
                    ContextHeaders = revision.SourceReadings.ContextHeaders.Add(NodeId 50, header)
                    Contexts = revision.SourceReadings.Contexts.Add(NodeId 50, [[]])
                    Ports = revision.SourceReadings.Ports.Add((NodeId 50, OccurrencePort.ModuleDeclaration), header.Ports[OccurrencePort.ModuleDeclaration]) } }
    Assert.Empty(Integrity.check revision)

[<Theory>]
[<InlineData("valid", "")>]
[<InlineData("scoped-context", "")>]
[<InlineData("unscoped-parent", "Emission.Boundary.CountedEntryArrays.Participants")>]
[<InlineData("mismatched-count-arg", "Emission.Boundary.CountedEntryArrays.Contract")>]
[<InlineData("mismatched-element", "Emission.Boundary.CountedEntryArrays.Contract")>]
let ``counted entry array validates quotation fields and Pointer callback argument`` mode expectedPart =
    let held = optionalBoundaryControl true
    let basis = held.Emission.Boundary
    let receiver0 = basis.CallbackInvocations[NodeId 220]
    let imported0 = basis.Imports[receiver0.Import]
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let number value parent = controlFact "integer" [] [value] [] (Some parent)
    let case name refs parent = controlFact "case" [name] [] refs (Some parent)
    let record fields refs parent = controlFact "record" fields [] refs (Some parent)
    let bindingParent =
        match mode with
        | "scoped-context" -> Some 400
        | "unscoped-parent" -> Some 999
        | _ -> None
    let countedFacts =
        [ 751, controlFact "binding" ["countedArg"] [0I; 0I] [750] bindingParent
          750, controlFact "quotation" [] [] [752] (Some 751)
          752, record ["Binding"; "Parameter"; "Argument"; "CountArgument"; "Element"] [753; 754; 755; 756; 757] 750
          753, text "OptionalControl.receive" 752
          754, number 0I 752
          755, number 1I 752
          756, number 0I 752
          757, (if mode = "mismatched-element" then case "NullableText" [] 752 else case "Handle" [758] 752)
          758, text "sqlite3_value" 757 ]
        |> List.map (fun (id, fact) -> NodeId id, fact) |> Map.ofList
    let counted : BoundaryCountedEntryArray =
        { Identity = NodeId 750; Import = receiver0.Import; Parameter = 0; Invocation = NodeId 220
          Contract =
            { Binding = "OptionalControl.receive"; Parameter = 0; Argument = 1
              CountArgument = (if mode = "mismatched-count-arg" then 2 else 0)
              Element = BAREWire.Descriptors.CountedElement.Handle "sqlite3_value" }
          DeclarationFacts = countedFacts
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.CountedEntryArrayDeclaration; Node = NodeId 750; Ordinal = 0; Group = NodeId 750 }
              { Role = ParticipantRole.CountedEntryArrayInvocation; Node = NodeId 220; Ordinal = 0; Group = NodeId 750 } ] }
    let sigWithArray : BAREWire.Descriptors.EntrySignature =
        { Parameters =
            [| { Name = "argc"; Type = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 32); PassBy = BAREWire.Descriptors.PassBy.Value }
               { Name = "argv"; Type = BAREWire.Descriptors.TypeRef.Pointer 64; PassBy = BAREWire.Descriptors.PassBy.Value } |]
          ReturnType = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 32)
          CallingConvention = BAREWire.Descriptors.CallConv.CDecl }
    let receiver =
        { receiver0 with
            Contract = { receiver0.Contract with Signature = sigWithArray }
            Signature = { receiver0.Signature with Parameters = [BoundaryScalar.Integer(32, true); BoundaryScalar.ReadOnlyBytes(NodeId 750)] } }
    let boundary =
        { basis with
            CallbackInvocations = basis.CallbackInvocations.Add(receiver.Identity, receiver)
            CountedEntryArrays = Map.ofList [NodeId 750, counted] }
    let rev = { held with Emission = { held.Emission with Boundary = boundary } }
    let violations = Integrity.check rev
    if expectedPart = "" then
        Assert.Empty violations
        if mode = "scoped-context" then
            Assert.Contains(Integrity.named rev, fun (part, ids) ->
                part = "Emission.Boundary.CountedEntryArrays.DeclarationFacts" && List.contains (NodeId 400) ids)
    else
        Assert.Contains(violations, fun v -> v.Part = expectedPart)

[<Theory>]
[<InlineData("valid-companion", "")>]
[<InlineData("shared-origin-varref", "")>]
[<InlineData("pattern-formal-varref", "")>]
[<InlineData("wrong-companion-binding", "Emission.Boundary.BorrowedResultViewUses.Account")>]
[<InlineData("wrong-shared-origin", "Emission.Boundary.BorrowedResultViewUses.Account")>]
[<InlineData("mutable-binding-varref", "Emission.Boundary.BorrowedResultViewUses.Account")>]
let ``borrowed result view CompanionCall verifies companion import binding and shared arguments`` mode expectedPart =
    let held = snapshotFacts
    let basis = boundaryCalleeFacts.Emission.Boundary
    let header = boundaryCalleeFacts.SourceReadings.ContextHeaders[NodeId 50]
    let record fields ids parent = controlFact "record" fields [] ids (Some parent)
    let binding name child = controlFact "binding" [name] [0I;0I] [child] (Some 50)
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let number value parent = controlFact "integer" [] [value] [] (Some parent)
    let case name refs parent = controlFact "case" [name] [] refs (Some parent)
    let intType = held.Nodes[NodeId 3].Type
    let viewFacts =
        [ 2, binding "colText" 1003
          1003, controlFact "lambda" ["colText"; "stmt"; "col"] [2I; 0I; 0I] [1004; 1005; 1006] (Some 2)
          1004, {controlFact "formal" ["stmt"] [] [] (Some 1003) with SourceType = intType}
          1005, {controlFact "formal" ["col"] [] [] (Some 1003) with SourceType = intType}
          1006, controlFact "unit" [] [] [] (Some 1003)
          1073, binding "colTextDescriptor" 1072
          1072, controlFact "quotation" [] [] [72] (Some 1073)
          72, record ["Parameters"; "CName"] [1010; 1020] 1072
          1010, controlFact "array" [] [] [1011; 1012] (Some 72)
          1011, record ["Type"; "PassBy"] [1013; 1016] 1010
          1013, case "Pointer" [1014] 1011
          1014, number 64I 1013
          1016, case "Value" [] 1011
          1012, record ["Type"; "PassBy"] [1017; 1019] 1010
          1017, case "Integer" [1021] 1012
          1021, controlFact "tuple" [] [] [1022; 1023] (Some 1017)
          1022, case "Signed" [] 1021
          1023, number 32I 1021
          1019, case "Value" [] 1012
          1020, text "colText" 72
          1201, binding "colTextBorrowedViewDescriptor" 1200
          1200, controlFact "quotation" [] [] [1202] (Some 1201)
          1202, record ["Binding"; "Content"; "Extent"; "Owner"; "InvalidatedBy"; "Hypothesis"] [1203; 1204; 1205; 1206; 1207; 1208] 1200
          1203, text (header.Name + ".colText") 1202
          1204, case "Utf8Text" [] 1202
          1205, case "CompanionCall" [1217] 1202
          1217, controlFact "tuple" [] [] [1213; 1214] (Some 1205)
          1213, text (header.Name + ".colBytes") 1217
          1214, controlFact "array" [] [] [1215; 1216] (Some 1217)
          1215, number 0I 1214
          1216, number 1I 1214
          1206, number 0I 1202
          1207, controlFact "array" [] [] [1212] (Some 1202)
          1212, case "AnyOwnerCall" [] 1207
          1208, record ["Identity"; "Version"; "Source"] [1209; 1210; 1211] 1202
          1209, text "view-comp" 1208
          1210, text "1" 1208
          1211, text "fixture" 1208 ]
        |> List.map (fun (id, fact) -> NodeId id, fact) |> Map.ofList
    let compBindingName = if mode = "wrong-companion-binding" then "wrongComp" else "colBytes"
    let compFacts =
        [ 20, binding compBindingName 1083
          1083, controlFact "lambda" [compBindingName; "stmt"; "col"] [2I; 0I; 0I] [1084; 1085; 1086] (Some 20)
          1084, {controlFact "formal" ["stmt"] [] [] (Some 1083) with SourceType = intType}
          1085, {controlFact "formal" ["col"] [] [] (Some 1083) with SourceType = intType}
          1086, controlFact "unit" [] [] [] (Some 1083) ]
        |> List.map (fun (id, fact) -> NodeId id, fact) |> Map.ofList
    let viewDecl : BoundaryBorrowedResultViewDeclaration =
        { Identity = NodeId 1200; Declaration = NodeId 2; Body = NodeId 1006
          Formals = [NodeId 1004; NodeId 1005]; Descriptor = NodeId 72
          OwnerParameter = 0; OwnerFormal = NodeId 1004
          Contract =
            { Binding = header.Name + ".colText"; Content = BAREWire.Descriptors.BorrowedContent.Utf8Text
              Extent = BAREWire.Descriptors.BorrowedExtent.CompanionCall(header.Name + ".colBytes", [| 0; 1 |]); Owner = 0
              InvalidatedBy = [| BAREWire.Descriptors.BorrowInvalidation.AnyOwnerCall |]
              Hypothesis = { Identity = "view-comp"; Version = "1"; Source = "fixture" } }
          DeclarationFacts = viewFacts
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.BorrowedResultViewDeclaration; Node = NodeId 1200; Ordinal = 0; Group = NodeId 1200 }
              { Role = ParticipantRole.BorrowedResultViewOwner; Node = NodeId 1004; Ordinal = 0; Group = NodeId 1200 } ] }
    let useSharedVarRefs =
        mode = "shared-origin-varref" || mode = "wrong-shared-origin" ||
        mode = "mutable-binding-varref" || mode = "pattern-formal-varref"
    let borrowOwner = if useSharedVarRefs then NodeId 2003 else NodeId 3
    let borrowCol =
        if mode = "mutable-binding-varref" then NodeId 2016
        elif mode = "pattern-formal-varref" then NodeId 2013
        elif useSharedVarRefs then NodeId 2007
        else NodeId 4
    let compOwner = if useSharedVarRefs then NodeId 2004 else NodeId 3
    let compCol =
        if mode = "shared-origin-varref" then NodeId 2008
        elif mode = "pattern-formal-varref" then NodeId 2014
        elif mode = "wrong-shared-origin" then NodeId 2011
        elif mode = "mutable-binding-varref" then NodeId 2017
        else NodeId 4
    let scopeClaim =
        controlClaim "borrowed-view-scope" "foreign-borrowed-view-scope"
            (ObligationBody.BorrowedResultViewScope
                { Call = NodeId 1; Declaration = NodeId 1200; Owner = borrowOwner; View = NodeId 1
                  CallOrder = 1; InvalidationOrders = [5]; ReadOrders = [2]; NullToNoneBoundary = true })
    let viewUse : BoundaryBorrowedResultViewUse =
        { Call = NodeId 1; Declaration = NodeId 1200; Owner = borrowOwner; View = NodeId 1
          CompanionCall = Some(NodeId 21); CompanionArguments = [compOwner; compCol]; CallOrder = 1
          Invalidations = [NodeId 961]; InvalidationOrders = [5]; Reads = [NodeId 962]; ReadOrders = [2]
          NullToNoneBoundary = true; ScopeProof = NodeId 960
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.BorrowedResultViewCall; Node = NodeId 1; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewDeclaration; Node = NodeId 1200; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewOwner; Node = borrowOwner; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewInvalidation; Node = NodeId 961; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewRead; Node = NodeId 962; Ordinal = 0; Group = NodeId 1 } ] }
    let borrowImport =
        { basis.Imports[NodeId 72] with
            Binding = NodeId 2; Symbol = "colText"
            Parameters = [NodeId 1004, BoundaryScalar.Integer(64, false); NodeId 1005, BoundaryScalar.Integer(32, true)]
            Result = Some(BoundaryScalar.BorrowedBytes(NodeId 1200))
            DeclarationFacts = viewFacts; Participants = viewFacts.Keys |> Set.ofSeq
            SourceTypes = Map.ofList [NodeId 1004, intType; NodeId 1005, intType; NodeId 1, held.Nodes[NodeId 1].Type] }
    let compImport =
        { basis.Imports[NodeId 72] with
            Identity = NodeId 73; Binding = NodeId 20; Symbol = compBindingName
            Parameters = [NodeId 1084, BoundaryScalar.Integer(64, false); NodeId 1085, BoundaryScalar.Integer(32, true)]
            Result = Some(BoundaryScalar.Integer(32, true))
            DeclarationFacts = compFacts; Participants = compFacts.Keys |> Set.ofSeq
            SourceTypes = Map.ofList [NodeId 1084, intType; NodeId 1085, intType; NodeId 21, held.Nodes[NodeId 1].Type] }
    let borrowCall =
        { basis.Calls[NodeId 1] with
            Callee = NodeId 2
            Arguments =
                [ { Actual = borrowOwner; Formal = NodeId 1004; Abi = BoundaryScalar.Integer(64, false); Adaptation = None; OptionalEntry = None; BufferAbsence = None }
                  { Actual = borrowCol; Formal = NodeId 1005; Abi = BoundaryScalar.Integer(32, true); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
            Result = Some(BoundaryScalar.BorrowedBytes(NodeId 1200))
            SourceTypes = borrowImport.SourceTypes; Participants = viewFacts.Keys |> Set.ofSeq }
    let compCall =
        { basis.Calls[NodeId 1] with
            Site = NodeId 21; Import = NodeId 73; Callee = NodeId 20
            Arguments =
                [ { Actual = compOwner; Formal = NodeId 1084; Abi = BoundaryScalar.Integer(64, false); Adaptation = None; OptionalEntry = None; BufferAbsence = None }
                  { Actual = compCol; Formal = NodeId 1085; Abi = BoundaryScalar.Integer(32, true); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
            Result = Some(BoundaryScalar.Integer(32, true))
            SourceTypes = compImport.SourceTypes; Participants = compFacts.Keys |> Set.ofSeq }
    let compSiteNode = { held.Nodes[NodeId 1] with Id = NodeId 21; Kind = SemanticKind.Application(NodeId 20, [compOwner; compCol]); Children = [NodeId 20; compOwner; compCol] }
    let compCalleeNode = { held.Nodes[NodeId 2] with Id = NodeId 20 }
    let nodesWithSharedOrigins =
        let baseNodes = held.Nodes.Add(NodeId 20, compCalleeNode).Add(NodeId 21, compSiteNode)
        if not useSharedVarRefs then baseNodes else
        let nodeTpl = held.Nodes[NodeId 3]
        let colTpl = held.Nodes[NodeId 4]
        baseNodes
            .Add(NodeId 1, { held.Nodes[NodeId 1] with Kind = SemanticKind.Application(NodeId 2, [borrowOwner; borrowCol]); Children = [NodeId 2; borrowOwner; borrowCol] })
            .Add(NodeId 2001, { nodeTpl with Id = NodeId 2001; Kind = SemanticKind.Binding("stmt", false, false, None); Children = [NodeId 2002] })
            .Add(NodeId 2002, { nodeTpl with Id = NodeId 2002; Kind = SemanticKind.PlatformBinding "stmtVal"; Children = [] })
            .Add(NodeId 2003, { nodeTpl with Id = NodeId 2003; Kind = SemanticKind.VarRef("stmt", Some(NodeId 2001)); Children = [] })
            .Add(NodeId 2004, { nodeTpl with Id = NodeId 2004; Kind = SemanticKind.VarRef("stmt", Some(NodeId 2001)); Children = [] })
            .Add(NodeId 2005, { colTpl with Id = NodeId 2005; Kind = SemanticKind.Binding("col", false, false, None); Children = [NodeId 2006] })
            .Add(NodeId 2006, { colTpl with Id = NodeId 2006; Kind = SemanticKind.PlatformBinding "colVal"; Children = [] })
            .Add(NodeId 2007, { colTpl with Id = NodeId 2007; Kind = SemanticKind.VarRef("col", Some(NodeId 2005)); Children = [] })
            .Add(NodeId 2008, { colTpl with Id = NodeId 2008; Kind = SemanticKind.VarRef("col", Some(NodeId 2005)); Children = [] })
            .Add(NodeId 2009, { colTpl with Id = NodeId 2009; Kind = SemanticKind.Binding("otherCol", false, false, None); Children = [NodeId 2010] })
            .Add(NodeId 2010, { colTpl with Id = NodeId 2010; Kind = SemanticKind.PlatformBinding "otherColVal"; Children = [] })
            .Add(NodeId 2011, { colTpl with Id = NodeId 2011; Kind = SemanticKind.VarRef("otherCol", Some(NodeId 2009)); Children = [] })
            .Add(NodeId 2012, { colTpl with Id = NodeId 2012; Kind = SemanticKind.PatternBinding "colFormal"; Children = [] })
            .Add(NodeId 2013, { colTpl with Id = NodeId 2013; Kind = SemanticKind.VarRef("colFormal", Some(NodeId 2012)); Children = [] })
            .Add(NodeId 2014, { colTpl with Id = NodeId 2014; Kind = SemanticKind.VarRef("colFormal", Some(NodeId 2012)); Children = [] })
            .Add(NodeId 2015, { colTpl with Id = NodeId 2015; Kind = SemanticKind.Binding("mutCol", true, false, None); Children = [NodeId 2006] })
            .Add(NodeId 2016, { colTpl with Id = NodeId 2016; Kind = SemanticKind.VarRef("mutCol", Some(NodeId 2015)); Children = [] })
            .Add(NodeId 2017, { colTpl with Id = NodeId 2017; Kind = SemanticKind.VarRef("mutCol", Some(NodeId 2015)); Children = [] })
    let revision =
        { held with
            Nodes = nodesWithSharedOrigins
            CurrentClaims = held.CurrentClaims.Add(NodeId 960, scopeClaim)
            Obligations = held.Obligations @ [scopeClaim]
            ObligationSources = held.ObligationSources.Add(NodeId 960, [[NodeId 1; borrowOwner]])
            Emission =
                { held.Emission with
                    Boundary =
                        { basis with
                            Imports = Map.ofList [NodeId 72, borrowImport; NodeId 73, compImport]
                            Calls = Map.ofList [NodeId 1, borrowCall; NodeId 21, compCall]
                            BorrowedResultViewDeclarations = Map.ofList [NodeId 1200, viewDecl]
                            BorrowedResultViewUses = Map.ofList [NodeId 1, viewUse] }
                    Numeric =
                        { held.Emission.Numeric with
                            Operations = Map.empty; OperationRequired = Set.empty; ResultSites = Set.empty
                            Required = Set.empty; Values = held.Emission.Numeric.Values.Remove(NodeId 1) } } }
        |> covered
    let revision =
        { revision with
            SourceReadings =
                { revision.SourceReadings with
                    ContextHeaders = revision.SourceReadings.ContextHeaders.Add(NodeId 50, header)
                    Contexts = revision.SourceReadings.Contexts.Add(NodeId 50, [[]])
                    Ports = revision.SourceReadings.Ports.Add((NodeId 50, OccurrencePort.ModuleDeclaration), header.Ports[OccurrencePort.ModuleDeclaration]) } }
    let violations = Integrity.check revision
    if expectedPart = "" then
        Assert.Empty violations
    else
        Assert.Contains(violations, fun v -> v.Part = expectedPart)

[<Fact>]
let ``integrity-valid Schema 53 revision round-trips through Binary encode decode and Json Inspection render`` () =
    let held = snapshotFacts
    let basis = boundaryCalleeFacts.Emission.Boundary
    let header = boundaryCalleeFacts.SourceReadings.ContextHeaders[NodeId 50]
    let byteType = TypeIdentity.Application({Declaration = {Module = []; Name = "uint8"}; Parameters = []; NativeKind = Some(NTUKind.NTUuint(NTUWidth.Fixed 8))}, [])
    let arrayType = TypeIdentity.Application({Declaration = {Module = []; Name = "array"}; Parameters = [TypeParamKind.Type]; NativeKind = None}, [byteType])
    let optionArrayType = TypeIdentity.Application({Declaration = {Module = []; Name = "option"}; Parameters = [TypeParamKind.Type]; NativeKind = None}, [arrayType])
    let unitType = held.Nodes[NodeId 1].Type
    let record fields ids parent = controlFact "record" fields [] ids (Some parent)
    let binding name child = controlFact "binding" [name] [0I;0I] [child] (Some 50)
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let number value parent = controlFact "integer" [] [value] [] (Some parent)
    let case name refs parent = controlFact "case" [name] [] refs (Some parent)
    let facts =
        [ 2, binding "openVfs" 1003
          1003, controlFact "lambda" ["openVfs"; "vfs"] [1I; 0I; 0I] [1004; 1006] (Some 2)
          1004, {controlFact "formal" ["vfs"] [] [] (Some 1003) with SourceType = optionArrayType}
          1006, controlFact "unit" [] [] [] (Some 1003)
          1073, binding "openVfsDescriptor" 1072
          1072, controlFact "quotation" [] [] [72] (Some 1073)
          72, record ["Parameters"; "CName"] [1010; 1020] 1072
          1010, controlFact "array" [] [] [1011] (Some 72)
          1011, record ["Type"; "PassBy"] [1013; 1016] 1010
          1013, case "Pointer" [1014] 1011
          1014, number 64I 1013
          1016, case "Value" [] 1011
          1020, text "openVfs" 72
          1101, binding "openVfsReadOnlyDescriptor" 1100
          1100, controlFact "quotation" [] [] [1102] (Some 1101)
          1102, record ["Binding"; "Parameter"; "Extent"; "Content"; "Retention"; "Hypothesis"] [1103; 1104; 1105; 1115; 1111; 1106] 1100
          1103, text (header.Name + ".openVfs") 1102
          1104, number 0I 1102
          1105, case "UncountedNulTerminated" [] 1102
          1115, case "Utf8Text" [] 1102
          1111, case "DuringCall" [] 1102
          1106, record ["Identity"; "Version"; "Source"] [1107; 1108; 1109] 1102
          1107, text "ro-rt" 1106
          1108, text "1" 1106
          1109, text "fixture" 1106
          701, binding "openVfsBufferAbsence" 700
          700, controlFact "quotation" [] [] [702] (Some 701)
          702, { record ["Binding"; "Parameter"; "Hypothesis"] [703; 704; 705] 700 with
                    SourceType = TypeIdentity.Application({ Declaration = { Module = ["BAREWire"; "Descriptors"]; Name = "BufferAbsenceContract" }; Parameters = []; NativeKind = None }, []) }
          703, text (header.Name + ".openVfs") 702
          704, number 0I 702
          705, record ["Identity"; "Version"; "Source"] [706; 707; 708] 702
          706, text "abs-rt" 705
          707, text "1" 705
          708, text "fixture" 705 ]
        |> List.map (fun (id, fact) -> NodeId id, fact) |> Map.ofList
    let viewFacts =
        [ 1201, binding "openVfsBorrowedViewDescriptor" 1200
          1200, controlFact "quotation" [] [] [1202] (Some 1201)
          1202, record ["Binding"; "Content"; "Extent"; "Owner"; "InvalidatedBy"; "Hypothesis"] [1203; 1204; 1205; 1206; 1207; 1208] 1200
          1203, text (header.Name + ".openVfs") 1202
          1204, case "Utf8Text" [] 1202
          1205, case "NulTerminated" [] 1202
          1206, number 0I 1202
          1207, controlFact "array" [] [] [1212] (Some 1202)
          1212, case "AnyOwnerCall" [] 1207
          1208, record ["Identity"; "Version"; "Source"] [1209; 1210; 1211] 1202
          1209, text "view-rt" 1208
          1210, text "1" 1208
          1211, text "fixture" 1208 ]
        |> List.map (fun (id, fact) -> NodeId id, fact)
    let allOpenVfsFacts = (facts, viewFacts) ||> List.fold (fun m (k, v) -> Map.add k v m)
    let roDecl : BoundaryReadOnlyBufferDeclaration =
        { Identity = NodeId 1100; Declaration = NodeId 2; Body = NodeId 1006
          Formals = [NodeId 1004]; Descriptor = NodeId 72; Parameter = 0; CountParameter = None
          BufferFormal = NodeId 1004; CountFormal = None
          Contract =
            { Binding = header.Name + ".openVfs"; Parameter = 0
              Extent = BAREWire.Descriptors.ReadOnlyBufferExtent.UncountedNulTerminated
              Content = BAREWire.Descriptors.BorrowedContent.Utf8Text
              Retention = BAREWire.Descriptors.BufferRetention.DuringCall
              Hypothesis = { Identity = "ro-rt"; Version = "1"; Source = "fixture" } }
          DeclarationFacts = allOpenVfsFacts
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.ReadOnlyBufferDeclaration; Node = NodeId 1100; Ordinal = 0; Group = NodeId 1100 }
              { Role = ParticipantRole.ReadOnlyBufferFormal; Node = NodeId 1004; Ordinal = 0; Group = NodeId 1100 } ] }
    let viewDecl : BoundaryBorrowedResultViewDeclaration =
        { Identity = NodeId 1200; Declaration = NodeId 2; Body = NodeId 1006
          Formals = [NodeId 1004]; Descriptor = NodeId 72
          OwnerParameter = 0; OwnerFormal = NodeId 1004
          Contract =
            { Binding = header.Name + ".openVfs"; Content = BAREWire.Descriptors.BorrowedContent.Utf8Text
              Extent = BAREWire.Descriptors.BorrowedExtent.NulTerminated; Owner = 0
              InvalidatedBy = [| BAREWire.Descriptors.BorrowInvalidation.AnyOwnerCall |]
              Hypothesis = { Identity = "view-rt"; Version = "1"; Source = "fixture" } }
          DeclarationFacts = allOpenVfsFacts
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.BorrowedResultViewDeclaration; Node = NodeId 1200; Ordinal = 0; Group = NodeId 1200 }
              { Role = ParticipantRole.BorrowedResultViewOwner; Node = NodeId 1004; Ordinal = 0; Group = NodeId 1200 } ] }
    let terminationClaim =
        controlClaim "ro-term" "foreign-uncounted-path-termination"
            (ObligationBody.UncountedPathTermination
                { Call = NodeId 1; Declaration = NodeId 1100; Parameter = 0; Source = NodeId 3
                  Mode = UncountedPathStagingMode.CallScopedStaged(NodeId 12, 5); ByteLength = 4I
                  RequiresNoInteriorNul = true; RequiresTrailingNul = true })
    let retentionClaim =
        controlClaim "ro-ret" "foreign-buffer-retention-domination"
            (ObligationBody.BufferRetentionDomination
                { Call = NodeId 1; Declaration = NodeId 1100; Buffer = NodeId 3; Residence = NodeId 11
                  Mode = BufferRetentionMode.DuringCall; AcquireOrder = 1; RetirementOrders = [] })
    let roUse : BoundaryReadOnlyBufferUse =
        { Call = NodeId 1; Declaration = NodeId 1100; Parameter = 0; Buffer = NodeId 3
          Residence = NodeId 11; Retirements = []; Copies = 0
          Crossing = BoundaryReadOnlyBufferCrossing.CallScopedNulStaged(NodeId 12, 5, 4I, NodeId 959)
          RetentionProof = NodeId 952; AccessExclusivityProof = None
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.ReadOnlyBufferCall; Node = NodeId 1; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.ReadOnlyBufferDeclaration; Node = NodeId 1100; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.ReadOnlyBufferActual; Node = NodeId 3; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.ReadOnlyBufferResidence; Node = NodeId 11; Ordinal = 0; Group = NodeId 1 } ] }
    let viewClaim =
        controlClaim "borrowed-view-scope" "foreign-borrowed-view-scope"
            (ObligationBody.BorrowedResultViewScope
                { Call = NodeId 1; Declaration = NodeId 1200; Owner = NodeId 3; View = NodeId 1
                  CallOrder = 1; InvalidationOrders = [5]; ReadOrders = [2]; NullToNoneBoundary = true })
    let viewUse : BoundaryBorrowedResultViewUse =
        { Call = NodeId 1; Declaration = NodeId 1200; Owner = NodeId 3; View = NodeId 1
          CompanionCall = None; CompanionArguments = []; CallOrder = 1
          Invalidations = [NodeId 961]; InvalidationOrders = [5]; Reads = [NodeId 962]; ReadOrders = [2]
          NullToNoneBoundary = true; ScopeProof = NodeId 960
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.BorrowedResultViewCall; Node = NodeId 1; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewDeclaration; Node = NodeId 1200; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewOwner; Node = NodeId 3; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewInvalidation; Node = NodeId 961; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewRead; Node = NodeId 962; Ordinal = 0; Group = NodeId 1 } ] }
    let absence : BoundaryBufferAbsence =
        { Quote = NodeId 700; DescriptorBinding = NodeId 701; Record = NodeId 702
          Import = NodeId 72; Parameter = 0; Formal = NodeId 1004; BufferDeclaration = NodeId 1100
          Contract = { Binding = header.Name + ".openVfs"; Parameter = 0; Hypothesis = { Identity = "abs-rt"; Version = "1"; Source = "fixture" } }
          SourcePath = [NodeId 700; NodeId 702]
          Inputs =
            [ BufferAbsenceInputRole.Binding, [NodeId 703]; BufferAbsenceInputRole.Parameter, [NodeId 704]
              BufferAbsenceInputRole.Hypothesis, [NodeId 705]; BufferAbsenceInputRole.HypothesisIdentity, [NodeId 706]
              BufferAbsenceInputRole.HypothesisVersion, [NodeId 707]; BufferAbsenceInputRole.HypothesisSource, [NodeId 708] ]
          DeclarationFacts = [700..708] |> List.map (fun id -> NodeId id, facts[NodeId id]) |> Map.ofList }
    let sel : BoundaryBufferAbsenceSelection =
        { Construction = NodeId 3; CaseOrdinal = 0; Payload = None; Absence = NodeId 700
          Transport = [NodeId 3]; Obligation = NodeId 958 }
    let absClaim =
        controlClaim "abs-none" "foreign-buffer-absence-conversion-0"
            (ObligationBody.BufferAbsenceArgumentConversion
                { Call = NodeId 1; Parameter = 0; Actual = NodeId 3; Construction = NodeId 3; SourceCase = 0
                  Absence = NodeId 700
                  Arms = [ { CaseOrdinal = 0; Choice = BufferAbsencePlanChoice.AbsentNull }
                           { CaseOrdinal = 1; Choice = BufferAbsencePlanChoice.RequiresNonNullBuffer } ] })
    let imported =
        { basis.Imports[NodeId 72] with
            Symbol = "openVfs"; Parameters = [NodeId 1004, BoundaryScalar.ReadOnlyBytes(NodeId 1100)]
            Result = Some(BoundaryScalar.BorrowedBytes(NodeId 1200))
            DeclarationFacts = allOpenVfsFacts; Participants = allOpenVfsFacts.Keys |> Set.ofSeq
            SourceTypes = Map.ofList [NodeId 1004, optionArrayType; NodeId 1, held.Nodes[NodeId 1].Type] }
    let call =
        { basis.Calls[NodeId 1] with
            Arguments = [ { Actual = NodeId 3; Formal = NodeId 1004; Abi = BoundaryScalar.ReadOnlyBytes(NodeId 1100); Adaptation = None; OptionalEntry = None; BufferAbsence = Some(BoundaryBufferAbsenceChoice.Direct sel) } ]
            Result = Some(BoundaryScalar.BorrowedBytes(NodeId 1200))
            SourceTypes = imported.SourceTypes; Participants = allOpenVfsFacts.Keys |> Set.ofSeq }
    let callNode = { held.Nodes[NodeId 1] with Kind = SemanticKind.Application(NodeId 2, [NodeId 3]); Children = [NodeId 2; NodeId 3]; Type = held.Nodes[NodeId 1].Type }
    let optRev = optionalBoundaryControl true
    let optBasis = optRev.Emission.Boundary
    let optCb0 = optBasis.CallbackInvocations[NodeId 220]
    let optImp0 = optBasis.Imports[optCb0.Import]
    let retType = TypeIdentity.Application({ Declaration = { Module = ["BAREWire"; "Descriptors"]; Name = "RetainedCallbackDescriptor" }; Parameters = []; NativeKind = None }, [])
    let optCbFacts =
        optImp0.DeclarationFacts
        |> Map.add (NodeId 212) (controlFact "array" [] [] [218; 245] (Some 210))
        |> Map.add (NodeId 245) (controlFact "record" ["Type"; "PassBy"] [] [246; 249] (Some 212))
        |> Map.add (NodeId 246) (controlFact "case" ["Integer"] [] [247] (Some 245))
        |> Map.add (NodeId 247) (controlFact "tuple" [] [] [248; 250] (Some 246))
        |> Map.add (NodeId 248) (controlFact "case" ["Signed"] [] [] (Some 247))
        |> Map.add (NodeId 250) (number 32I 247)
        |> Map.add (NodeId 249) (controlFact "case" ["Value"] [] [] (Some 245))
        |> Map.add (NodeId 602) { controlFact "record" ["Binding"; "Parameter"; "Owner"; "Releases"] [] [603; 604; 605; 606] (Some 600) with SourceType = retType }
        |> Map.add (NodeId 605) (number 1I 602)
        |> Map.add (NodeId 606) (controlFact "array" [] [] [607] (Some 602))
        |> Map.add (NodeId 607) (controlFact "case" ["OwnerRelease"] [] [608] (Some 606))
        |> Map.add (NodeId 608) (controlFact "record" ["Binding"; "Parameter"] [] [609; 610] (Some 607))
        |> Map.add (NodeId 609) (text "OptionalControl.close" 608)
        |> Map.add (NodeId 610) (number 0I 608)
    let optImp =
        { optImp0 with
            Parameters = optImp0.Parameters @ [NodeId 211, BoundaryScalar.Integer(32, true)]
            DeclarationFacts = optCbFacts }
    let countedFacts =
        [ 751, controlFact "binding" ["countedArg"] [0I; 0I] [750] None
          750, controlFact "quotation" [] [] [752] (Some 751)
          752, record ["Binding"; "Parameter"; "Argument"; "CountArgument"; "Element"] [753; 754; 755; 756; 757] 750
          753, text "OptionalControl.receive" 752
          754, number 0I 752
          755, number 1I 752
          756, number 0I 752
          757, case "Handle" [758] 752
          758, text "sqlite3_value" 757 ]
        |> List.map (fun (id, fact) -> NodeId id, fact) |> Map.ofList
    let counted : BoundaryCountedEntryArray =
        { Identity = NodeId 750; Import = optImp.Identity; Parameter = 0; Invocation = NodeId 220
          Contract =
            { Binding = "OptionalControl.receive"; Parameter = 0; Argument = 1
              CountArgument = 0; Element = BAREWire.Descriptors.CountedElement.Handle "sqlite3_value" }
          DeclarationFacts = countedFacts
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.CountedEntryArrayDeclaration; Node = NodeId 750; Ordinal = 0; Group = NodeId 750 }
              { Role = ParticipantRole.CountedEntryArrayInvocation; Node = NodeId 220; Ordinal = 0; Group = NodeId 750 } ] }
    let sigWithArray : BAREWire.Descriptors.EntrySignature =
        { Parameters =
            [| { Name = "argc"; Type = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 32); PassBy = BAREWire.Descriptors.PassBy.Value }
               { Name = "argv"; Type = BAREWire.Descriptors.TypeRef.Pointer 64; PassBy = BAREWire.Descriptors.PassBy.Value } |]
          ReturnType = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 32)
          CallingConvention = BAREWire.Descriptors.CallConv.CDecl }
    let optCb =
        { optCb0 with
            Contract = { optCb0.Contract with Signature = sigWithArray }
            Signature = { optCb0.Signature with Parameters = [BoundaryScalar.Integer(32, true); BoundaryScalar.ReadOnlyBytes(NodeId 750)] }
            Extent = BoundaryCallbackExtent.Retained(1, [| BAREWire.Descriptors.RetentionRelease.OwnerRelease { Binding = "OptionalControl.close"; Parameter = 0 } |]) }
    let revision =
        { held with
            Nodes = held.Nodes.Add(NodeId 1, callNode)
            CurrentClaims =
                held.CurrentClaims
                    .Add(NodeId 958, absClaim)
                    .Add(NodeId 959, terminationClaim)
                    .Add(NodeId 952, retentionClaim)
                    .Add(NodeId 960, viewClaim)
            Obligations = held.Obligations @ [absClaim; terminationClaim; retentionClaim; viewClaim]
            ObligationSources =
                held.ObligationSources
                    .Add(NodeId 958, [[NodeId 1; NodeId 3]])
                    .Add(NodeId 959, [[NodeId 1; NodeId 3]])
                    .Add(NodeId 952, [[NodeId 1; NodeId 3]])
                    .Add(NodeId 960, [[NodeId 1; NodeId 3]])
            Emission =
                { held.Emission with
                    Boundary =
                        { basis with
                            ByScope = basis.ByScope.Add(optImp.Scope, [optImp.Identity])
                            Imports = Map.ofList [NodeId 72, imported; optImp.Identity, optImp]
                            Calls = Map.ofList [NodeId 1, call]
                            CallbackInvocations = Map.ofList [optCb.Identity, optCb]
                            ReadOnlyBufferDeclarations = Map.ofList [NodeId 1100, roDecl]
                            ReadOnlyBufferUses = Map.ofList [(NodeId 1, 0), roUse]
                            BorrowedResultViewDeclarations = Map.ofList [NodeId 1200, viewDecl]
                            BorrowedResultViewUses = Map.ofList [NodeId 1, viewUse]
                            BufferAbsences = Map.ofList [NodeId 700, absence]
                            CountedEntryArrays = Map.ofList [NodeId 750, counted] }
                    Numeric =
                        { held.Emission.Numeric with
                            Operations = Map.empty; OperationRequired = Set.empty; ResultSites = Set.empty
                            Required = Set.empty; Values = held.Emission.Numeric.Values.Remove(NodeId 1) } } }
        |> covered
    let optHeader = optRev.SourceReadings.ContextHeaders[optImp.Scope]
    let revision =
        { revision with
            Platform = { revision.Platform with Pointer = Ok 64 }
            SourceReadings =
                { revision.SourceReadings with
                    ContextHeaders = revision.SourceReadings.ContextHeaders.Add(NodeId 50, header).Add(optImp.Scope, optHeader)
                    Contexts = revision.SourceReadings.Contexts.Add(NodeId 50, [[]]).Add(optImp.Scope, optRev.SourceReadings.Contexts[optImp.Scope])
                    Ports =
                        revision.SourceReadings.Ports
                            .Add((NodeId 50, OccurrencePort.ModuleDeclaration), header.Ports[OccurrencePort.ModuleDeclaration])
                            .Add((optImp.Scope, OccurrencePort.ModuleDeclaration), optHeader.Ports[OccurrencePort.ModuleDeclaration]) } }
    Assert.Empty(Integrity.check revision)
    let limits : Binary.Limits =
        { MaxBytes = 4 * 1024 * 1024; MaxCollectionLength = 10000; MaxDepth = 128
          MaxStringBytes = 1024 * 1024; MaxBigIntegerBytes = 4096; MaxValues = 1000000 }
    let bytes =
        match Binary.encode limits revision with
        | Ok bytes -> bytes
        | Error err -> failwithf "Unexpected encode refusal: %A" err
    let decoded =
        match Binary.decode limits bytes with
        | Ok rev -> rev
        | Error err -> failwithf "Unexpected decode refusal: %A" err
    Assert.Equal(revision, decoded)
    let view =
        match Binary.openSource limits (BAREWire.Memory.ByteSource.ofArray bytes) with
        | Ok v -> v
        | Error err -> failwithf "Unexpected openSource refusal: %A" err
    let json =
        match Fidelity.PSG.Json.Inspection.render false view with
        | Ok text -> text
        | Error err -> failwithf "Unexpected JSON render refusal: %A" err
    for expected in
        [ "ReadOnlyBufferDeclarations"; "ReadOnlyBufferUses"
          "BorrowedResultViewDeclarations"; "BorrowedResultViewUses"
          "BufferAbsences"; "CountedEntryArrays"
          "ReadOnlyBytes"; "BorrowedBytes"; "Retained" ] do
        Assert.Contains(expected, json)

[<Fact>]
let ``leading PassBy Fixed shifts ReadOnlyBufferDeclaration ReadOnlyBufferUse and Retained callback native ordinals`` () =
    let held = snapshotFacts
    let basis = boundaryCalleeFacts.Emission.Boundary
    let header = boundaryCalleeFacts.SourceReadings.ContextHeaders[NodeId 50]
    let integerType name kind =
        TypeIdentity.Application({ Declaration = { Module = []; Name = name }; Parameters = []; NativeKind = Some kind }, [])
    let byteType = integerType "uint8" (NTUKind.NTUuint(NTUWidth.Fixed 8))
    let countType = integerType "uint64" (NTUKind.NTUuint(NTUWidth.Fixed 64))
    let arrayType = TypeIdentity.Application({ Declaration = { Module = []; Name = "array" }; Parameters = [TypeParamKind.Type]; NativeKind = None }, [byteType])
    let unitType = held.Nodes[NodeId 1].Type
    let record fields ids parent = controlFact "record" fields [] ids (Some parent)
    let binding name child = controlFact "binding" [name] [0I; 0I] [child] (Some 50)
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let number value parent = controlFact "integer" [] [value] [] (Some parent)
    let case name refs parent = controlFact "case" [name] [] refs (Some parent)
    let facts =
        [ 2, binding "readFn" 1003
          1003, controlFact "lambda" ["readFn"; "buf"; "count"] [2I; 0I; 0I] [1004; 1005; 1006] (Some 2)
          1004, { controlFact "formal" ["buf"] [] [] (Some 1003) with SourceType = arrayType }
          1005, { controlFact "formal" ["count"] [] [] (Some 1003) with SourceType = countType }
          1006, controlFact "unit" [] [] [] (Some 1003)
          1073, binding "readFnDescriptor" 1072
          1072, controlFact "quotation" [] [] [72] (Some 1073)
          72, record ["Parameters"; "CName"] [1010; 1020] 1072
          1010, controlFact "array" [] [] [1030; 1011; 1012] (Some 72)
          1030, record ["Type"; "PassBy"] [1031; 1033] 1010
          1031, case "Pointer" [1032] 1030
          1032, number 64I 1031
          1033, case "Fixed" [1034] 1030
          1034, case "EntrySentinel" [1035; 1036] 1033
          1035, text "SQLITE_TRANSIENT" 1034
          1036, number (-1I) 1034
          1011, record ["Type"; "PassBy"] [1013; 1016] 1010
          1013, case "Pointer" [1014] 1011
          1014, number 64I 1013
          1016, case "Value" [] 1011
          1012, record ["Type"; "PassBy"] [1017; 1019] 1010
          1017, case "Integer" [1021] 1012
          1021, controlFact "tuple" [] [] [1022; 1023] (Some 1017)
          1022, case "Unsigned" [] 1021
          1023, number 64I 1021
          1019, case "Value" [] 1012
          1020, text "readFn" 72
          1101, binding "readFnReadOnlyDescriptor" 1100
          1100, controlFact "quotation" [] [] [1102] (Some 1101)
          1102, record ["Binding"; "Parameter"; "Extent"; "Content"; "Retention"; "Hypothesis"] [1103; 1104; 1105; 1115; 1111; 1106] 1100
          1103, text (header.Name + ".readFn") 1102
          1104, number 1I 1102
          1105, case "ExplicitCount" [1110] 1102
          1110, number 2I 1105
          1115, case "RawBytes" [] 1102
          1111, case "DuringCall" [] 1102
          1106, record ["Identity"; "Version"; "Source"] [1107; 1108; 1109] 1102
          1107, text "ro-lead-fixed" 1106
          1108, text "1" 1106
          1109, text "fixture" 1106 ]
        |> List.map (fun (id, fact) -> NodeId id, fact) |> Map.ofList
    let roDecl : BoundaryReadOnlyBufferDeclaration =
        { Identity = NodeId 1100; Declaration = NodeId 2; Body = NodeId 1006
          Formals = [NodeId 1004; NodeId 1005]; Descriptor = NodeId 72
          Parameter = 1; CountParameter = Some 2
          BufferFormal = NodeId 1004; CountFormal = Some(NodeId 1005)
          Contract =
            { Binding = header.Name + ".readFn"; Parameter = 1
              Extent = BAREWire.Descriptors.ReadOnlyBufferExtent.ExplicitCount 2
              Content = BAREWire.Descriptors.BorrowedContent.RawBytes
              Retention = BAREWire.Descriptors.BufferRetention.DuringCall
              Hypothesis = { Identity = "ro-lead-fixed"; Version = "1"; Source = "fixture" } }
          DeclarationFacts = facts
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.ReadOnlyBufferDeclaration; Node = NodeId 1100; Ordinal = 0; Group = NodeId 1100 }
              { Role = ParticipantRole.ReadOnlyBufferFormal; Node = NodeId 1004; Ordinal = 0; Group = NodeId 1100 }
              { Role = ParticipantRole.ReadOnlyBufferFormal; Node = NodeId 1005; Ordinal = 1; Group = NodeId 1100 } ] }
    let imported =
        { basis.Imports[NodeId 72] with
            Symbol = "readFn"
            Parameters = [NodeId 1004, BoundaryScalar.ReadOnlyBytes(NodeId 1100); NodeId 1005, BoundaryScalar.Integer(64, false)]
            Result = None; DeclarationFacts = facts; Participants = facts.Keys |> Set.ofSeq
            SourceTypes = Map.ofList [NodeId 1004, arrayType; NodeId 1005, countType; NodeId 1, unitType] }
    let call =
        { basis.Calls[NodeId 1] with
            Arguments =
                [ { Actual = NodeId 3; Formal = NodeId 1004; Abi = BoundaryScalar.ReadOnlyBytes(NodeId 1100); Adaptation = None; OptionalEntry = None; BufferAbsence = None }
                  { Actual = NodeId 4; Formal = NodeId 1005; Abi = BoundaryScalar.Integer(64, false); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
            Result = None; SourceTypes = imported.SourceTypes; Participants = facts.Keys |> Set.ofSeq }
    let countCarrier =
        { held.Emission.Numeric.Values[NodeId 4] with
            Slot = SettledSlot.Integer(64, Some "uint64"); SourceType = countType
            Range = ValueRange.Bounded(4I, 4I); Obligations = [] }
    let extentClaim =
        controlClaim "ro-extent" "foreign-readonly-buffer-extent"
            (ObligationBody.ZeroCopyBufferExtent
                { Call = NodeId 1; Declaration = NodeId 1100; Parameter = 1; CountParameter = 2
                  Buffer = NodeId 3; Count = NodeId 4; MinimumCount = 4I; MaximumCount = 4I
                  ExtentCapacity = 4I; ElementBytes = 1; CountCoverage = NodeId 951 })
    let retentionClaim =
        controlClaim "ro-ret" "foreign-buffer-retention-domination"
            (ObligationBody.BufferRetentionDomination
                { Call = NodeId 1; Declaration = NodeId 1100; Buffer = NodeId 3; Residence = NodeId 11
                  Mode = BufferRetentionMode.DuringCall; AcquireOrder = 1; RetirementOrders = [] })
    let roUse : BoundaryReadOnlyBufferUse =
        { Call = NodeId 1; Declaration = NodeId 1100; Parameter = 1; Buffer = NodeId 3
          Residence = NodeId 11; Retirements = []; Copies = 0
          Crossing = BoundaryReadOnlyBufferCrossing.ExplicitZeroCopy(2, NodeId 4, 4I, NodeId 951)
          RetentionProof = NodeId 952; AccessExclusivityProof = None
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.ReadOnlyBufferCall; Node = NodeId 1; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.ReadOnlyBufferDeclaration; Node = NodeId 1100; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.ReadOnlyBufferActual; Node = NodeId 3; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.ReadOnlyBufferResidence; Node = NodeId 11; Ordinal = 0; Group = NodeId 1 } ] }
    let callNode = { held.Nodes[NodeId 1] with Kind = SemanticKind.Application(NodeId 2, [NodeId 3; NodeId 4]); Children = [NodeId 2; NodeId 3; NodeId 4]; Type = unitType }
    let roRevision =
        { held with
            Nodes = held.Nodes.Add(NodeId 1, callNode)
            CurrentClaims = held.CurrentClaims.Add(NodeId 951, extentClaim).Add(NodeId 952, retentionClaim)
            Obligations = held.Obligations @ [extentClaim; retentionClaim]
            ObligationSources = held.ObligationSources.Add(NodeId 951, [[NodeId 1; NodeId 3]]).Add(NodeId 952, [[NodeId 1; NodeId 3]])
            Emission =
                { held.Emission with
                    Boundary =
                        { basis with
                            Imports = Map.ofList [NodeId 72, imported]
                            Calls = Map.ofList [NodeId 1, call]
                            ReadOnlyBufferDeclarations = Map.ofList [NodeId 1100, roDecl]
                            ReadOnlyBufferUses = Map.ofList [(NodeId 1, 1), roUse] }
                    Numeric =
                        { held.Emission.Numeric with
                            Operations = Map.empty; OperationRequired = Set.empty; ResultSites = Set.empty
                            Required = Set.singleton(NodeId 4)
                            Values = held.Emission.Numeric.Values.Remove(NodeId 1).Add(NodeId 4, countCarrier) } } }
        |> covered
    let roRevision =
        { roRevision with
            SourceReadings =
                { roRevision.SourceReadings with
                    ContextHeaders = roRevision.SourceReadings.ContextHeaders.Add(NodeId 50, header)
                    Contexts = roRevision.SourceReadings.Contexts.Add(NodeId 50, [[]])
                    Ports = roRevision.SourceReadings.Ports.Add((NodeId 50, OccurrencePort.ModuleDeclaration), header.Ports[OccurrencePort.ModuleDeclaration]) } }
    Assert.Empty(Integrity.check roRevision)
    let optRev = optionalBoundaryControl true
    let optBasis = optRev.Emission.Boundary
    let receiver0 = optBasis.CallbackInvocations[NodeId 220]
    let imp0 = optBasis.Imports[receiver0.Import]
    let retType = TypeIdentity.Application({ Declaration = { Module = ["BAREWire"; "Descriptors"]; Name = "RetainedCallbackDescriptor" }; Parameters = []; NativeKind = None }, [])
    let leadFixedFacts =
        imp0.DeclarationFacts
        |> Map.add (NodeId 212) (controlFact "array" [] [] [240; 218; 245] (Some 210))
        |> Map.add (NodeId 240) (record ["Type"; "PassBy"] [241; 243] 212)
        |> Map.add (NodeId 241) (case "Pointer" [242] 240)
        |> Map.add (NodeId 242) (number 64I 241)
        |> Map.add (NodeId 243) (case "Fixed" [244] 240)
        |> Map.add (NodeId 244) (case "EntrySentinel" [260; 261] 243)
        |> Map.add (NodeId 260) (text "SENTINEL" 244)
        |> Map.add (NodeId 261) (number (-1I) 244)
        |> Map.add (NodeId 245) (record ["Type"; "PassBy"] [246; 249] 212)
        |> Map.add (NodeId 246) (case "Integer" [247] 245)
        |> Map.add (NodeId 247) (controlFact "tuple" [] [] [248; 250] (Some 246))
        |> Map.add (NodeId 248) (case "Signed" [] 247)
        |> Map.add (NodeId 250) (number 32I 247)
        |> Map.add (NodeId 249) (case "Value" [] 245)
        |> Map.add (NodeId 224) (number 1I 222)
        |> Map.add (NodeId 504) (number 1I 502)
        |> Map.add (NodeId 602) { record ["Binding"; "Parameter"; "Owner"; "Releases"] [603; 604; 605; 606] 600 with SourceType = retType }
        |> Map.add (NodeId 605) (number 2I 602)
        |> Map.add (NodeId 606) (controlFact "array" [] [] [607] (Some 602))
        |> Map.add (NodeId 607) (case "OwnerRelease" [608] 606)
        |> Map.add (NodeId 608) (record ["Binding"; "Parameter"] [609; 610] 607)
        |> Map.add (NodeId 609) (text "OptionalControl.close" 608)
        |> Map.add (NodeId 610) (number 0I 608)
    let leadImp = { imp0 with Parameters = imp0.Parameters @ [NodeId 211, BoundaryScalar.Integer(32, true)]; DeclarationFacts = leadFixedFacts }
    let leadCb = { receiver0 with Parameter = 1; Contract = { receiver0.Contract with Parameter = 1 }; Extent = BoundaryCallbackExtent.Retained(2, [| BAREWire.Descriptors.RetentionRelease.OwnerRelease { Binding = "OptionalControl.close"; Parameter = 0 } |]) }
    let leadAbsence =
        { optBasis.CallbackAbsences[NodeId 500] with
            Parameter = 1
            Contract = { optBasis.CallbackAbsences[NodeId 500].Contract with Parameter = 1 }
            DeclarationFacts = [500..508] |> List.map (fun id -> NodeId id, leadFixedFacts[NodeId id]) |> Map.ofList }
    let cbViolations = Integrity.check { optRev with Emission = { optRev.Emission with Boundary = { optBasis with Imports = optBasis.Imports.Add(leadImp.Identity, leadImp); CallbackInvocations = optBasis.CallbackInvocations.Add(leadCb.Identity, leadCb); CallbackAbsences = optBasis.CallbackAbsences.Add(leadAbsence.Quote, leadAbsence) } } }
    Assert.DoesNotContain(cbViolations, fun v -> v.Part.StartsWith("Emission.Boundary.Callback", System.StringComparison.Ordinal))
    let badOwnerCb = { leadCb with Extent = BoundaryCallbackExtent.Retained(1, [| BAREWire.Descriptors.RetentionRelease.OwnerRelease { Binding = "OptionalControl.close"; Parameter = 0 } |]) }
    let badOwnerViolations = Integrity.check { optRev with Emission = { optRev.Emission with Boundary = { optBasis with Imports = optBasis.Imports.Add(leadImp.Identity, leadImp); CallbackInvocations = optBasis.CallbackInvocations.Add(badOwnerCb.Identity, badOwnerCb); CallbackAbsences = optBasis.CallbackAbsences.Add(leadAbsence.Quote, leadAbsence) } } }
    Assert.Contains(badOwnerViolations, fun v -> v.Part = "Emission.Boundary.CallbackInvocations.RetainedExtent")

[<Fact>]
let ``leading PassBy Fixed shifts BorrowedResultViewDeclaration and CompanionCall ordinals`` () =
    let held = snapshotFacts
    let basis = boundaryCalleeFacts.Emission.Boundary
    let header = boundaryCalleeFacts.SourceReadings.ContextHeaders[NodeId 50]
    let record fields ids parent = controlFact "record" fields [] ids (Some parent)
    let binding name child = controlFact "binding" [name] [0I; 0I] [child] (Some 50)
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let number value parent = controlFact "integer" [] [value] [] (Some parent)
    let case name refs parent = controlFact "case" [name] [] refs (Some parent)
    let intType = held.Nodes[NodeId 3].Type
    let viewFacts =
        [ 2, binding "colText" 1003
          1003, controlFact "lambda" ["colText"; "stmt"; "col"] [2I; 0I; 0I] [1004; 1005; 1006] (Some 2)
          1004, { controlFact "formal" ["stmt"] [] [] (Some 1003) with SourceType = intType }
          1005, { controlFact "formal" ["col"] [] [] (Some 1003) with SourceType = intType }
          1006, controlFact "unit" [] [] [] (Some 1003)
          1073, binding "colTextDescriptor" 1072
          1072, controlFact "quotation" [] [] [72] (Some 1073)
          72, record ["Parameters"; "CName"] [1010; 1020] 1072
          1010, controlFact "array" [] [] [1030; 1011; 1012] (Some 72)
          1030, record ["Type"; "PassBy"] [1031; 1033] 1010
          1031, case "Pointer" [1032] 1030
          1032, number 64I 1031
          1033, case "Fixed" [1034] 1030
          1034, case "EntrySentinel" [1035; 1036] 1033
          1035, text "SENTINEL" 1034
          1036, number (-1I) 1034
          1011, record ["Type"; "PassBy"] [1013; 1016] 1010
          1013, case "Pointer" [1014] 1011
          1014, number 64I 1013
          1016, case "Value" [] 1011
          1012, record ["Type"; "PassBy"] [1017; 1019] 1010
          1017, case "Integer" [1021] 1012
          1021, controlFact "tuple" [] [] [1022; 1023] (Some 1017)
          1022, case "Signed" [] 1021
          1023, number 32I 1021
          1019, case "Value" [] 1012
          1020, text "colText" 72
          1201, binding "colTextBorrowedViewDescriptor" 1200
          1200, controlFact "quotation" [] [] [1202] (Some 1201)
          1202, record ["Binding"; "Content"; "Extent"; "Owner"; "InvalidatedBy"; "Hypothesis"] [1203; 1204; 1205; 1206; 1207; 1208] 1200
          1203, text (header.Name + ".colText") 1202
          1204, case "Utf8Text" [] 1202
          1205, case "CompanionCall" [1217] 1202
          1217, controlFact "tuple" [] [] [1213; 1214] (Some 1205)
          1213, text (header.Name + ".colBytes") 1217
          1214, controlFact "array" [] [] [1215; 1216] (Some 1217)
          1215, number 1I 1214
          1216, number 2I 1214
          1206, number 1I 1202
          1207, controlFact "array" [] [] [1212] (Some 1202)
          1212, case "AnyOwnerCall" [] 1207
          1208, record ["Identity"; "Version"; "Source"] [1209; 1210; 1211] 1202
          1209, text "view-comp-lead" 1208
          1210, text "1" 1208
          1211, text "fixture" 1208 ]
        |> List.map (fun (id, fact) -> NodeId id, fact) |> Map.ofList
    let compFacts =
        [ 20, binding "colBytes" 1083
          1083, controlFact "lambda" ["colBytes"; "stmt"; "col"] [2I; 0I; 0I] [1084; 1085; 1086] (Some 20)
          1084, { controlFact "formal" ["stmt"] [] [] (Some 1083) with SourceType = intType }
          1085, { controlFact "formal" ["col"] [] [] (Some 1083) with SourceType = intType }
          1086, controlFact "unit" [] [] [] (Some 1083) ]
        |> List.map (fun (id, fact) -> NodeId id, fact) |> Map.ofList
    let viewDecl : BoundaryBorrowedResultViewDeclaration =
        { Identity = NodeId 1200; Declaration = NodeId 2; Body = NodeId 1006
          Formals = [NodeId 1004; NodeId 1005]; Descriptor = NodeId 72
          OwnerParameter = 1; OwnerFormal = NodeId 1004
          Contract =
            { Binding = header.Name + ".colText"; Content = BAREWire.Descriptors.BorrowedContent.Utf8Text
              Extent = BAREWire.Descriptors.BorrowedExtent.CompanionCall(header.Name + ".colBytes", [| 1; 2 |]); Owner = 1
              InvalidatedBy = [| BAREWire.Descriptors.BorrowInvalidation.AnyOwnerCall |]
              Hypothesis = { Identity = "view-comp-lead"; Version = "1"; Source = "fixture" } }
          DeclarationFacts = viewFacts
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.BorrowedResultViewDeclaration; Node = NodeId 1200; Ordinal = 0; Group = NodeId 1200 }
              { Role = ParticipantRole.BorrowedResultViewOwner; Node = NodeId 1004; Ordinal = 0; Group = NodeId 1200 } ] }
    let scopeClaim =
        controlClaim "borrowed-view-scope" "foreign-borrowed-view-scope"
            (ObligationBody.BorrowedResultViewScope
                { Call = NodeId 1; Declaration = NodeId 1200; Owner = NodeId 3; View = NodeId 1
                  CallOrder = 1; InvalidationOrders = [5]; ReadOrders = [2]; NullToNoneBoundary = true })
    let viewUse : BoundaryBorrowedResultViewUse =
        { Call = NodeId 1; Declaration = NodeId 1200; Owner = NodeId 3; View = NodeId 1
          CompanionCall = Some(NodeId 21); CompanionArguments = [NodeId 3; NodeId 4]; CallOrder = 1
          Invalidations = [NodeId 961]; InvalidationOrders = [5]; Reads = [NodeId 962]; ReadOrders = [2]
          NullToNoneBoundary = true; ScopeProof = NodeId 960
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.BorrowedResultViewCall; Node = NodeId 1; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewDeclaration; Node = NodeId 1200; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewOwner; Node = NodeId 3; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewInvalidation; Node = NodeId 961; Ordinal = 0; Group = NodeId 1 }
              { Role = ParticipantRole.BorrowedResultViewRead; Node = NodeId 962; Ordinal = 0; Group = NodeId 1 } ] }
    let borrowImport =
        { basis.Imports[NodeId 72] with
            Binding = NodeId 2; Symbol = "colText"
            Parameters = [NodeId 1004, BoundaryScalar.Integer(64, false); NodeId 1005, BoundaryScalar.Integer(32, true)]
            Result = Some(BoundaryScalar.BorrowedBytes(NodeId 1200))
            DeclarationFacts = viewFacts; Participants = viewFacts.Keys |> Set.ofSeq
            SourceTypes = Map.ofList [NodeId 1004, intType; NodeId 1005, intType; NodeId 1, held.Nodes[NodeId 1].Type] }
    let compImport =
        { basis.Imports[NodeId 72] with
            Identity = NodeId 73; Binding = NodeId 20; Symbol = "colBytes"
            Parameters = [NodeId 1084, BoundaryScalar.Integer(64, false); NodeId 1085, BoundaryScalar.Integer(32, true)]
            Result = Some(BoundaryScalar.Integer(32, true))
            DeclarationFacts = compFacts; Participants = compFacts.Keys |> Set.ofSeq
            SourceTypes = Map.ofList [NodeId 1084, intType; NodeId 1085, intType; NodeId 21, held.Nodes[NodeId 1].Type] }
    let borrowCall =
        { basis.Calls[NodeId 1] with
            Callee = NodeId 2
            Arguments =
                [ { Actual = NodeId 3; Formal = NodeId 1004; Abi = BoundaryScalar.Integer(64, false); Adaptation = None; OptionalEntry = None; BufferAbsence = None }
                  { Actual = NodeId 4; Formal = NodeId 1005; Abi = BoundaryScalar.Integer(32, true); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
            Result = Some(BoundaryScalar.BorrowedBytes(NodeId 1200))
            SourceTypes = borrowImport.SourceTypes; Participants = viewFacts.Keys |> Set.ofSeq }
    let compCall =
        { basis.Calls[NodeId 1] with
            Site = NodeId 21; Import = NodeId 73; Callee = NodeId 20
            Arguments =
                [ { Actual = NodeId 3; Formal = NodeId 1084; Abi = BoundaryScalar.Integer(64, false); Adaptation = None; OptionalEntry = None; BufferAbsence = None }
                  { Actual = NodeId 4; Formal = NodeId 1085; Abi = BoundaryScalar.Integer(32, true); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
            Result = Some(BoundaryScalar.Integer(32, true))
            SourceTypes = compImport.SourceTypes; Participants = compFacts.Keys |> Set.ofSeq }
    let compSiteNode = { held.Nodes[NodeId 1] with Id = NodeId 21; Kind = SemanticKind.Application(NodeId 20, [NodeId 3; NodeId 4]); Children = [NodeId 20; NodeId 3; NodeId 4] }
    let compCalleeNode = { held.Nodes[NodeId 2] with Id = NodeId 20 }
    let rev =
        { held with
            Nodes = held.Nodes.Add(NodeId 20, compCalleeNode).Add(NodeId 21, compSiteNode)
            CurrentClaims = held.CurrentClaims.Add(NodeId 960, scopeClaim)
            Obligations = held.Obligations @ [scopeClaim]
            ObligationSources = held.ObligationSources.Add(NodeId 960, [[NodeId 1; NodeId 3]])
            Emission =
                { held.Emission with
                    Boundary =
                        { basis with
                            Imports = Map.ofList [NodeId 72, borrowImport; NodeId 73, compImport]
                            Calls = Map.ofList [NodeId 1, borrowCall; NodeId 21, compCall]
                            BorrowedResultViewDeclarations = Map.ofList [NodeId 1200, viewDecl]
                            BorrowedResultViewUses = Map.ofList [NodeId 1, viewUse] }
                    Numeric =
                        { held.Emission.Numeric with
                            Operations = Map.empty; OperationRequired = Set.empty; ResultSites = Set.empty
                            Required = Set.empty; Values = held.Emission.Numeric.Values.Remove(NodeId 1) } } }
        |> covered
    let rev =
        { rev with
            SourceReadings =
                { rev.SourceReadings with
                    ContextHeaders = rev.SourceReadings.ContextHeaders.Add(NodeId 50, header)
                    Contexts = rev.SourceReadings.Contexts.Add(NodeId 50, [[]])
                    Ports = rev.SourceReadings.Ports.Add((NodeId 50, OccurrencePort.ModuleDeclaration), header.Ports[OccurrencePort.ModuleDeclaration]) } }
    Assert.Empty(Integrity.check rev)

[<Fact>]
let ``CallbackInvocations maps Entry Parameter across leading PassBy Fixed formals`` () =
    let held = optionalBoundaryControl true
    let basis = held.Emission.Boundary
    let receiver0 = basis.CallbackInvocations[NodeId 220]
    let imported0 = basis.Imports[receiver0.Import]
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let number value parent = controlFact "integer" [] [value] [] (Some parent)
    let case name refs parent = controlFact "case" [name] [] refs (Some parent)
    let record fields refs parent = controlFact "record" fields [] refs (Some parent)
    let facts =
        imported0.DeclarationFacts
            .Add(NodeId 212, controlFact "array" [] [] [2180; 218] (Some 210))
            .Add(NodeId 2180, record ["Type"; "PassBy"] [2181; 2182] 212)
            .Add(NodeId 2181, case "Integer" [2183] 2180)
            .Add(NodeId 2183, controlFact "tuple" [] [] [2184; 2185] (Some 2181))
            .Add(NodeId 2184, case "Signed" [] 2183)
            .Add(NodeId 2185, number 32I 2183)
            .Add(NodeId 2182, case "Fixed" [2186] 2180)
            .Add(NodeId 2186, case "EntrySentinel" [2187] 2182)
            .Add(NodeId 2187, controlFact "tuple" [] [] [2188; 2189] (Some 2186))
            .Add(NodeId 2188, text "FLAG" 2187)
            .Add(NodeId 2189, number 1I 2187)
            .Add(NodeId 224, number 1I 222)
            .Add(NodeId 504, number 1I 502)
    let imported =
        { imported0 with
            DeclarationFacts = facts
            Participants = facts.Keys |> Set.ofSeq }
    let receiver =
        { receiver0 with
            Parameter = 1
            Contract = { receiver0.Contract with Parameter = 1 }
            Participants = facts.Keys |> Set.ofSeq }
    let absence =
        { basis.CallbackAbsences[NodeId 500] with
            Parameter = 1
            Contract = { basis.CallbackAbsences[NodeId 500].Contract with Parameter = 1 }
            DeclarationFacts = [500..508] |> List.map (fun id -> NodeId id, facts[NodeId id]) |> Map.ofList }
    let addedFactIds = [2180..2189] |> List.map NodeId
    let call0 = basis.Calls[NodeId 200]
    let call = { call0 with Participants = Set.union call0.Participants (Set.ofList addedFactIds) }
    let addSupport (sources: NodeId list list) =
        sources |> List.map (fun group -> List.distinct (group @ addedFactIds))
    let boundary =
        { basis with
            Imports = basis.Imports.Add(imported.Identity, imported)
            Calls = basis.Calls.Add(call.Site, call)
            CallbackInvocations = basis.CallbackInvocations.Add(receiver.Identity, receiver)
            CallbackAbsences = basis.CallbackAbsences.Add(absence.Quote, absence) }
    let rev =
        { held with
            ObligationSources =
                held.ObligationSources
                |> Map.add (NodeId 301) (addSupport held.ObligationSources[NodeId 301])
            Emission = { held.Emission with Boundary = boundary } }
    Assert.Empty(Integrity.check rev)
    let badReceiver = { receiver with Parameter = 0; Contract = { receiver.Contract with Parameter = 0 } }
    let badRev = { rev with Emission = { rev.Emission with Boundary = { boundary with CallbackInvocations = boundary.CallbackInvocations.Add(badReceiver.Identity, badReceiver) } } }
    Assert.Contains(Integrity.check badRev, fun v -> v.Part = "Emission.Boundary.CallbackInvocations.Formal")

[<Fact>]
let ``BufferAbsences maps ReadOnlyBuffer Parameter across leading PassBy Fixed formals`` () =
    let held = snapshotFacts
    let basis = boundaryCalleeFacts.Emission.Boundary
    let header = boundaryCalleeFacts.SourceReadings.ContextHeaders[NodeId 50]
    let record fields ids parent = controlFact "record" fields [] ids (Some parent)
    let binding name child = controlFact "binding" [name] [0I; 0I] [child] (Some 50)
    let text value parent = controlFact "string" [value] [] [] (Some parent)
    let number value parent = controlFact "integer" [] [value] [] (Some parent)
    let case name refs parent = controlFact "case" [name] [] refs (Some parent)
    let unitType = TypeIdentity.Application({ Declaration = { Module = []; Name = "unit" }; Parameters = []; NativeKind = Some NTUKind.NTUunit }, [])
    let charType = TypeIdentity.Application({ Declaration = { Module = []; Name = "uint8" }; Parameters = []; NativeKind = Some(NTUKind.NTUint(NTUWidth.Fixed 8)) }, [])
    let arrayType = TypeIdentity.Application({ Declaration = { Module = []; Name = "array" }; Parameters = [TypeParamKind.Type]; NativeKind = None }, [charType])
    let optionArrayType = TypeIdentity.Application({ Declaration = { Module = []; Name = "option" }; Parameters = [TypeParamKind.Type]; NativeKind = None }, [arrayType])
    let absType = TypeIdentity.Application({ Declaration = { Module = ["BAREWire"; "Descriptors"]; Name = "BufferAbsenceContract" }; Parameters = []; NativeKind = None }, [])
    let facts =
        [ 2, binding "openVfs" 1003
          1003, controlFact "lambda" ["openVfs"; "name"] [1I; 0I; 0I] [1004; 1006] (Some 2)
          1004, { controlFact "formal" ["name"] [] [] (Some 1003) with SourceType = optionArrayType }
          1006, controlFact "unit" [] [] [] (Some 1003)
          1073, binding "openVfsDescriptor" 1072
          1072, controlFact "quotation" [] [] [72] (Some 1073)
          72, record ["Parameters"; "CName"] [1010; 1020] 1072
          1010, controlFact "array" [] [] [1030; 1011] (Some 72)
          1030, record ["Type"; "PassBy"] [1031; 1033] 1010
          1031, case "Pointer" [1032] 1030
          1032, number 64I 1031
          1033, case "Fixed" [1034] 1030
          1034, case "EntrySentinel" [1035; 1036] 1033
          1035, text "FLAGS" 1034
          1036, number 1I 1034
          1011, record ["Type"; "PassBy"] [1013; 1016] 1010
          1013, case "Pointer" [1014] 1011
          1014, number 64I 1013
          1016, case "Value" [] 1011
          1020, text "openVfs" 72
          1101, binding "openVfsRoDescriptor" 1100
          1100, controlFact "quotation" [] [] [1102] (Some 1101)
          1102, record ["Binding"; "Parameter"; "Extent"; "Content"; "Retention"; "Hypothesis"] [1103; 1104; 1105; 1106; 1107; 1108] 1100
          1103, text (header.Name + ".openVfs") 1102
          1104, number 1I 1102
          1105, case "UncountedNulTerminated" [] 1102
          1106, case "Utf8Text" [] 1102
          1107, case "DuringCall" [] 1102
          1108, record ["Identity"; "Version"; "Source"] [1109; 1110; 1111] 1102
          1109, text "ro-abs-lead" 1108; 1110, text "1" 1108; 1111, text "fixture" 1108
          701, { binding "openVfsBufferAbsence" 700 with SourceType = absType }
          700, { controlFact "quotation" [] [1I] [702] (Some 701) with SourceType = absType }
          702, { record ["Binding"; "Parameter"; "Hypothesis"] [703; 704; 705] 700 with SourceType = absType }
          703, text (header.Name + ".openVfs") 702
          704, number 1I 702
          705, record ["Identity"; "Version"; "Source"] [706; 707; 708] 702
          706, text "abs-hyp-lead" 705; 707, text "1" 705; 708, text "fixture" 705 ]
        |> List.map (fun (id, fact) -> NodeId id, fact) |> Map.ofList
    let roDecl : BoundaryReadOnlyBufferDeclaration =
        { Identity = NodeId 1100; Declaration = NodeId 2; Body = NodeId 1006
          Formals = [NodeId 1004]; Descriptor = NodeId 72
          Parameter = 1; CountParameter = None
          BufferFormal = NodeId 1004; CountFormal = None
          Contract =
            { Binding = header.Name + ".openVfs"; Parameter = 1
              Extent = BAREWire.Descriptors.ReadOnlyBufferExtent.UncountedNulTerminated
              Content = BAREWire.Descriptors.BorrowedContent.Utf8Text
              Retention = BAREWire.Descriptors.BufferRetention.DuringCall
              Hypothesis = { Identity = "ro-abs-lead"; Version = "1"; Source = "fixture" } }
          DeclarationFacts = facts
          Participants = ParticipantEvidence.Established
            [ { Role = ParticipantRole.ReadOnlyBufferDeclaration; Node = NodeId 1100; Ordinal = 0; Group = NodeId 1100 }
              { Role = ParticipantRole.ReadOnlyBufferFormal; Node = NodeId 1004; Ordinal = 0; Group = NodeId 1100 } ] }
    let absence : BoundaryBufferAbsence =
        { Quote = NodeId 700; DescriptorBinding = NodeId 701; Record = NodeId 702
          Import = NodeId 72; Parameter = 1; Formal = NodeId 1004; BufferDeclaration = NodeId 1100
          Contract = { Binding = header.Name + ".openVfs"; Parameter = 1; Hypothesis = { Identity = "abs-hyp-lead"; Version = "1"; Source = "fixture" } }
          SourcePath = [NodeId 700; NodeId 702]
          Inputs =
            [ BufferAbsenceInputRole.Binding, [NodeId 703]
              BufferAbsenceInputRole.Parameter, [NodeId 704]
              BufferAbsenceInputRole.Hypothesis, [NodeId 705]
              BufferAbsenceInputRole.HypothesisIdentity, [NodeId 706]
              BufferAbsenceInputRole.HypothesisVersion, [NodeId 707]
              BufferAbsenceInputRole.HypothesisSource, [NodeId 708] ]
          DeclarationFacts = [700..708] |> List.map (fun id -> NodeId id, facts[NodeId id]) |> Map.ofList }
    let sel : BoundaryBufferAbsenceSelection =
        { Construction = NodeId 3; CaseOrdinal = 0; Payload = None; Absence = NodeId 700
          Transport = [NodeId 3]; Obligation = NodeId 958 }
    let absClaim =
        controlClaim "abs-none" "foreign-buffer-absence-conversion-0"
            (ObligationBody.BufferAbsenceArgumentConversion
                { Call = NodeId 1; Parameter = 0; Actual = NodeId 3; Construction = NodeId 3; SourceCase = 0
                  Absence = NodeId 700
                  Arms = [ { CaseOrdinal = 0; Choice = BufferAbsencePlanChoice.AbsentNull }
                           { CaseOrdinal = 1; Choice = BufferAbsencePlanChoice.RequiresNonNullBuffer } ] })
    let imported =
        { basis.Imports[NodeId 72] with
            Symbol = "openVfs"; Parameters = [NodeId 1004, BoundaryScalar.ReadOnlyBytes(NodeId 1100)]; Result = None
            DeclarationFacts = facts; Participants = facts.Keys |> Set.ofSeq
            SourceTypes = Map.ofList [NodeId 1004, optionArrayType; NodeId 1, unitType] }
    let call =
        { basis.Calls[NodeId 1] with
            Arguments = [ { Actual = NodeId 3; Formal = NodeId 1004; Abi = BoundaryScalar.ReadOnlyBytes(NodeId 1100); Adaptation = None; OptionalEntry = None; BufferAbsence = Some(BoundaryBufferAbsenceChoice.Direct sel) } ]
            Result = None; SourceTypes = imported.SourceTypes; Participants = facts.Keys |> Set.ofSeq }
    let callNode = { held.Nodes[NodeId 1] with Kind = SemanticKind.Application(NodeId 2, [NodeId 3]); Children = [NodeId 2; NodeId 3]; Type = unitType }
    let revision =
        { held with
            Nodes = held.Nodes.Add(NodeId 1, callNode)
            CurrentClaims = held.CurrentClaims.Add(NodeId 958, absClaim)
            Obligations = held.Obligations @ [absClaim]
            ObligationSources = held.ObligationSources.Add(NodeId 958, [[NodeId 1; NodeId 3]])
            Emission =
                { held.Emission with
                    Boundary =
                        { basis with
                            Imports = Map.ofList [NodeId 72, imported]
                            Calls = Map.ofList [NodeId 1, call]
                            ReadOnlyBufferDeclarations = Map.ofList [NodeId 1100, roDecl]
                            BufferAbsences = Map.ofList [NodeId 700, absence] }
                    Numeric =
                        { held.Emission.Numeric with
                            Operations = Map.empty; OperationRequired = Set.empty; ResultSites = Set.empty
                            Required = Set.empty; Values = held.Emission.Numeric.Values.Remove(NodeId 1) } } }
        |> covered
    let revision =
        { revision with
            SourceReadings =
                { revision.SourceReadings with
                    ContextHeaders = revision.SourceReadings.ContextHeaders.Add(NodeId 50, header)
                    Contexts = revision.SourceReadings.Contexts.Add(NodeId 50, [[]])
                    Ports = revision.SourceReadings.Ports.Add((NodeId 50, OccurrencePort.ModuleDeclaration), header.Ports[OccurrencePort.ModuleDeclaration]) } }
    Assert.Empty(Integrity.check revision)
    let badAbsence = { absence with Parameter = 0; Contract = { absence.Contract with Parameter = 0 } }
    let badRev = { revision with Emission = { revision.Emission with Boundary = { revision.Emission.Boundary with BufferAbsences = Map.ofList [NodeId 700, badAbsence] } } }
    Assert.NotEmpty(Integrity.check badRev)
