module Fidelity.PSG.Tests.CallableAggregateTests

open Xunit
open Fidelity.PSG
open Fidelity.PSG.Tests.Build

let private p role ordinal group node : Participant =
    { Role = role; Ordinal = ordinal; Group = NodeId group; Node = NodeId node }

let private failure rule revision =
    Assert.Contains(Integrity.callableAggregates revision, fun violation -> violation.Part.EndsWith("." + rule))

let private publish (callable: CallableEmissionProjection) revision =
    { revision with
        Codata = { revision.Codata with
                    CallableContracts = callable.Contracts; CallableCarriers = callable.Carriers
                    CallableAggregateSlots = callable.AggregateSlots; CallableAggregateValues = callable.AggregateValues
                    CallableAggregateDependencies = callable.AggregateDependencies }
        Emission = { revision.Emission with Callable = callable } }

// Fixture accounting spells every input directly, independently of the reader.
let private renewWithSlots slotIds revision =
    let c = revision.Emission.Callable
    let values = c.AggregateValues[NodeId 1]
    let slots = slotIds |> List.map (fun id -> c.AggregateSlots[NodeId id])
    let carriers = values |> List.collect _.Alternatives |> List.map _.Carrier |> List.distinct |> List.map (fun id -> c.Carriers[id])
    let contracts = c.Contracts.TryFind(NodeId 100) |> Option.toList
    let participants =
        (slots |> List.collect _.Participants) @
        (values |> List.collect (fun row -> row.Participants @ (row.Tag |> Option.map _.Participants |> Option.defaultValue []))) @
        (carriers |> List.collect _.Lifetime) @ (contracts |> List.collect _.Participants)
    let sources =
        participants |> List.map _.Node |> List.distinct |> List.choose (fun id ->
            let premise = contracts |> List.exists (fun contract -> contract.SourcePremises.ContainsKey id)
            (if premise then None else revision.Nodes.TryFind id) |> Option.map (fun node ->
                { Node = id; Kind = node.Kind; Type = node.Type; Children = node.Children; Anchors = node.ObligationAnchors }))
    let claims = participants |> List.map _.Node |> List.distinct |> List.choose (fun id ->
        revision.CurrentClaims.TryFind id |> Option.map (fun claim -> id, claim))
    let account : CallableAggregateDependencyAccount =
        { Occurrence = NodeId 1; Slots = slots; Values = values; Carriers = carriers; Contracts = contracts
          Flows = []; Joins = []; Participants = participants; Sources = sources; Claims = claims }
    publish { c with AggregateDependencies = Map.ofList [NodeId 1, account] } revision

let private renew revision = renewWithSlots [101] revision

let private nativeTarget : BoundaryPlatformPremise =
    { Id = "native-entry-contract-control"; Description = None; LibraryPath = None
      SourcePaths = Set.singleton "contract-test.clef"; Architecture = Some "x86_64"; OS = Some "linux"
      RuntimeClaim = Some RuntimeModel.Libc; Substrate = Some SubstrateKind.CPU
      Dimensions = Map.ofList ["Register", 64; "Pointer", 64]
      Representations = Map.empty; EndpointReturns = Map.empty }

// Independent source evidence: declarations describe residence, never a C
// address or a fabricated lifetime obligation. The exact parent/membership
// pair is intentional; presence of three arbitrary nodes proves nothing.
let private nativeResidencePremises () =
    let fnType = TypeIdentity.Function(boolType, boolType)
    let premise shape embedded : BoundarySourcePremise =
        { Shape = shape; EmbeddedTypes = embedded; ConstructorFacts = []; Reachable = true; Range = None
          ExternLibrary = None; ExternSymbol = None; HasExtern = false; Metadata = Map.empty }
    // Startup clears executable module children; lexical Member incidence
    // remains in References and does not make the declaration executable.
    let scope =
        premise
            { Form = "module"; Text = ["NativeLibrary"]; Numbers = []; References = [NodeId 401]
              Children = []; Parent = None; SourceType = unitType } []
    Map.ofList [
        NodeId 400, {scope with Reachable = false}
        NodeId 401, premise
            { Form = "binding"; Text = ["callback"; "no-declaration-root"]; Numbers = [0I; 0I]
              References = [NodeId 10]; Children = [NodeId 10]; Parent = Some(NodeId 400); SourceType = fnType } []
        NodeId 10, premise
            { Form = "lambda"; Text = ["RegularClosure"; "argument"]; Numbers = [1I; 0I; 0I]
              References = [NodeId 41; NodeId 11]; Children = [NodeId 41; NodeId 11]
              Parent = Some(NodeId 401); SourceType = fnType } [boolType]
    ]

let private fixture union captured native =
    let kind = if native then CallableKind.NativeEntry else CallableKind.OrdinaryFlatClosure
    let fnType =
        if native then
            let constructor : ConstructorIdentity =
                { Declaration = {Module = []; Name = "FnPtr"}; Parameters = []; NativeKind = Some NTUKind.NTUfnptr }
            TypeIdentity.Application(constructor, [TypeIdentity.Function(boolType, boolType)])
        else TypeIdentity.Function(unitType, unitType)
    let nativeLifetime =
        [p ParticipantRole.CallableLifetime 0 100 400; p ParticipantRole.CallableLifetime 1 100 401
         p ParticipantRole.CallableLifetime 2 100 10]
    let carrier occurrence environment : CallableCarrier =
        { Occurrence = NodeId occurrence; Kind = kind; Formation = NodeId occurrence
          EnvironmentValue = environment |> Option.map NodeId; Contract = Ok(NodeId 100)
          Lifetime = if native then nativeLifetime elif captured then [p ParticipantRole.CallableLifetime 0 occurrence 90] else []
          SourceType = fnType; Implementation = NodeId 10
          Parameters = if native then ["argument", boolType, NodeId 41] else []
          ParameterShapes = if native then [CallableValueShape.Data(NodeId 41)] else []
          OmittedParameters = Set.empty; Result = NodeId 11; ResultShape = CallableValueShape.Data(NodeId 11)
          Environment = if captured then Some {Owner = NodeId 40; Formal = NodeId 41} else None }
    let carriers = [carrier 30 (if captured then Some 20 else None); carrier 31 (if captured then Some 21 else None)]
    let physical = ValueRepresentation.Scalar SettledSlot.Bool
    let convention =
        if native then
            CallableConvention.CompilerOwnedPortable {
                Target = nativeTarget; ParameterConversions = [0, CallableConversion.Identity physical]
                ResultConversion = CallableConversion.Identity physical
                CodeLifetime = {Module = NodeId 400; Binding = NodeId 401; Implementation = NodeId 10} }
        else CallableConvention.Ordinary
    let contract : CallableContract =
        { Identity = NodeId 100; Kind = kind; Convention = convention
          ParameterTypes = if native then [boolType] else []
          OmittedParameters = []; ParameterRepresentations = if native then [0, physical] else []
          ResultType = if native then boolType else unitType
          ResultRepresentation = physical
          EnvironmentBytes = if captured then Some 16 else None
          SourcePremises = if native then nativeResidencePremises () else Map.empty
          Participants =
              [p ParticipantRole.CallableContract 0 100 100] @
              (if native then
                   [p ParticipantRole.Source 0 100 400; p ParticipantRole.Source 1 100 401; p ParticipantRole.Source 2 100 10] @ nativeLifetime
               else []) }
    let slot : CallableAggregateSlot =
        { Identity = NodeId 101; AggregateType = unitType; Declaration = None; DeclarationFacts = []
          Path = if union then [CallableAggregatePathStep.UnionPayload(0, 0)] else [CallableAggregatePathStep.RecordField 0]
          SourceType = fnType; Contract = Ok(NodeId 100)
          Participants = [p ParticipantRole.AggregateSlot 0 101 101; p ParticipantRole.CallableContract 0 101 100] }
    let alternatives = carriers |> List.mapi (fun ordinal carrier ->
        { Ordinal = ordinal; Carrier = carrier.Occurrence; Formation = carrier.Formation
          EnvironmentValue = carrier.EnvironmentValue; Contract = NodeId 100; Adapter = None
          EnvironmentPlacement = carrier.EnvironmentValue |> Option.map (fun value ->
              { Source = CallableAggregateEnvironmentSource.EnvironmentValue
                Value = value; Owner = NodeId 40; ViewBytes = 16; ByteOffset = 8; StorageBytes = 40; Alignment = 8; Adaptation = None }) })
    let tag : CallableAggregateTag option =
        if union then
            Some { Constructor = NodeId 1; TagRead = Some(NodeId 5); CaseOrdinal = 0
                   PayloadOrdinal = Some 0; Payload = Some(NodeId 30)
                   Participants = [p ParticipantRole.AggregateConstructor 0 1 1; p ParticipantRole.AggregateTag 0 1 5
                                   p ParticipantRole.AggregatePayload 0 1 30] }
        else None
    let participants =
        [p ParticipantRole.AggregateValue 0 1 1; p ParticipantRole.AggregateSource 0 1 1
         p ParticipantRole.AggregateSlot 0 1 101; p ParticipantRole.AggregateInput 0 1 30
         p ParticipantRole.AggregateInput 1 1 31; p ParticipantRole.AggregateWrite 0 1 30
         p ParticipantRole.AggregateSelector 0 1 6] @
        (alternatives |> List.collect (fun alternative ->
            [p ParticipantRole.CallableCarrier alternative.Ordinal 1 (NodeId.value alternative.Carrier)
             p ParticipantRole.CallableFormation alternative.Ordinal 1 (NodeId.value alternative.Formation)
             p ParticipantRole.CallableContract alternative.Ordinal 1 100] @
            (alternative.EnvironmentValue |> Option.toList |> List.map (fun value -> p ParticipantRole.CallableEnvironment alternative.Ordinal 1 (NodeId.value value)))))
    let row : CallableAggregateValue =
        { Occurrence = NodeId 1; Aggregate = NodeId 1; Slot = NodeId 101; Alternatives = alternatives
          Selector = Some {Lower = 0; UpperExclusive = 2; Storage = Some(NodeId 6); Slot = Some(SettledSlot.Integer(8, None)); ByteOffset = Some 0}
          FormationInputs = [NodeId 30; NodeId 31]; Value = Some(NodeId 30); SelectedAlternative = Some 0
          Operation = CallableAggregateOperation.Construct; Frontier = None; Tag = tag
          Bytes = (if captured then 48 else 1)
          Alignment = (if captured then 8 else 1)
          Participants = participants }
    let aggregateKind = if union then SemanticKind.UnionCase("Some", 0, Some(NodeId 30)) else SemanticKind.RecordExpr(["invoke", NodeId 30], None)
    let nodes =
        [node 1 aggregateKind [30]; node 5 (SemanticKind.DUGetTag(NodeId 1, unitType)) [1]] @
        ([6;10;11;20;21;30;31;40;41;90;91] |> List.map (fun id -> node id (SemanticKind.Literal NativeLiteral.Unit) []))
    let nodes =
        if not native then nodes else
        nodes |> List.map (fun value ->
            match value.Id with
            | NodeId 10 ->
                {value with Type = TypeIdentity.Function(boolType, boolType); Parent = Some(NodeId 401)
                            Kind = SemanticKind.Lambda(["argument", boolType, NodeId 41], NodeId 11, [], Some "callback", LambdaContext.RegularClosure)
                            Children = [NodeId 41; NodeId 11]}
            | NodeId 11 -> {value with Type = boolType; Kind = SemanticKind.Literal(NativeLiteral.Bool true); Parent = Some(NodeId 10)}
            | NodeId 41 -> {value with Type = boolType; Kind = SemanticKind.PatternBinding "argument"; Parent = Some(NodeId 10)}
            | _ -> value)
    let data = ValueRepresentation.Record(["selector", ValueRepresentation.Scalar(SettledSlot.Integer(8, None))], Some([0], row.Bytes, row.Alignment))
    let heldComponent = ValueRepresentation.CallableComponent(NodeId 101, data)
    let representation =
        if union then ValueRepresentation.Union(["Some", [heldComponent]; "None", []], Some(1, row.Bytes + 1, row.Alignment))
        else ValueRepresentation.Record(["invoke", heldComponent], Some([0], row.Bytes, row.Alignment))
    let initial = revision nodes
    let c =
        { initial.Emission.Callable with
            Declarations =
                if native then
                    Map.ofList [NodeId 10,
                        {Lookup = NodeId 10; Implementation = NodeId 10; Parameters = ["argument", boolType, NodeId 41]
                         Result = NodeId 11; Context = LambdaContext.RegularClosure; Captures = []
                         Name = CallableSymbolName.ModuleBinding("NativeLibrary", "callback"); Parent = Some(NodeId 401)
                         Participants = Set.ofList [NodeId 10; NodeId 11; NodeId 41]}]
                else initial.Emission.Callable.Declarations
            Contracts = Map.ofList [NodeId 100, contract]
            Carriers = carriers |> List.map (fun row -> row.Occurrence, row) |> Map.ofList
            AggregateSlots = Map.ofList [NodeId 101, slot]
            AggregateValues = Map.ofList [NodeId 1, [row]] }
    let env : EnvironmentLayout = { Owner = NodeId 40; Implementation = NodeId 10; Formal = NodeId 41; Slots = []; Bytes = 16; Alignment = 8; Obligations = [] }
    { initial with
        Platform = if native then {Register = Ok 64; Pointer = Ok 64} else initial.Platform
        Codata = { initial.Codata with EnvironmentLayouts = Map.ofList [NodeId 40, env] }
        Emission = { initial.Emission with Numeric = {initial.Emission.Numeric with OccurrenceRepresentations = initial.Emission.Numeric.OccurrenceRepresentations.Add(NodeId 1, Ok representation)} } }
    |> publish c |> renew

let private changeRow change revision =
    let c = revision.Emission.Callable
    publish { c with AggregateValues = c.AggregateValues.Add(NodeId 1, c.AggregateValues[NodeId 1] |> List.map change) } revision

let private changeSlot change revision =
    let c = revision.Emission.Callable
    publish {c with AggregateSlots = c.AggregateSlots.Add(NodeId 101, change c.AggregateSlots[NodeId 101])} revision

let private changeContract change revision =
    let c = revision.Emission.Callable
    publish {c with Contracts = c.Contracts.Add(NodeId 100, change c.Contracts[NodeId 100])} revision

let private changeNativeConvention change revision =
    revision |> changeContract (fun contract ->
        match contract.Convention with
        | CallableConvention.CompilerOwnedPortable convention ->
            {contract with Convention = CallableConvention.CompilerOwnedPortable(change convention)}
        | _ -> failwith "Expected the independent native fixture's portable convention.")

let private nominalFixture union =
    let held = fixture union false false
    let constructor : ConstructorIdentity =
        {Declaration = {Module = ["ContractTests"]; Name = "CallableContainer"}; Parameters = []; NativeKind = None}
    let aggregateType = TypeIdentity.Application(constructor, [])
    let sourceType = held.Emission.Callable.AggregateSlots[NodeId 101].SourceType
    let definition =
        if union then CallableAggregateDeclarationDefinition.UnionDef ["Some", [None, sourceType]; "None", []]
        else CallableAggregateDeclarationDefinition.RecordDef ["invoke", sourceType]
    let nominal =
        {held with Nodes = held.Nodes.Add(NodeId 1, {held.Nodes[NodeId 1] with Type = aggregateType})
                   Emission = {held.Emission with Numeric = {held.Emission.Numeric with SourceTypes = held.Emission.Numeric.SourceTypes.Add(NodeId 1, aggregateType)}}}
    nominal |> changeSlot (fun slot ->
        {slot with AggregateType = aggregateType; Declaration = Some(NodeId 200)
                   DeclarationFacts = [{Identity = NodeId 200; DeclaredType = aggregateType; Definition = definition}]
                   Participants = slot.Participants @ [p ParticipantRole.AggregateDeclaration 0 101 200]}) |> renew

let private elideSecond (row: CallableAggregateValue) =
    let participants =
        row.Participants |> List.filter (fun p ->
            p.Role <> ParticipantRole.AggregateSelector &&
            not (p.Ordinal = 1 && List.contains p.Role [ParticipantRole.CallableCarrier; ParticipantRole.CallableFormation; ParticipantRole.CallableContract]))
    { row with
        Alternatives = [row.Alternatives.Head]
        Selector = Some {Lower = 0; UpperExclusive = 1; Storage = None; Slot = None; ByteOffset = None}
        Participants = participants }

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``I1-I6 record and union retain two formations of one implementation`` union =
    let held = fixture union true false
    Assert.Empty(Integrity.callableAggregates held)
    Assert.NotEqual(held.Emission.Callable.Carriers[NodeId 30].EnvironmentValue, held.Emission.Callable.Carriers[NodeId 31].EnvironmentValue)
    Assert.Equal(held.Emission.Callable.Carriers[NodeId 30].Implementation, held.Emission.Callable.Carriers[NodeId 31].Implementation)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``I1 code is never recovered from an integer or address data slot`` union =
    let held = fixture union false false
    for data in [SettledSlot.Integer(64, None); SettledSlot.Pointer 1; SettledSlot.InlineBytes(8, 8)] do
        let representation =
            if union then ValueRepresentation.Union(["Some", [ValueRepresentation.Scalar data]], None)
            else ValueRepresentation.Record(["invoke", ValueRepresentation.Scalar data], None)
        { held with Emission = { held.Emission with Numeric = { held.Emission.Numeric with OccurrenceRepresentations = held.Emission.Numeric.OccurrenceRepresentations.Add(NodeId 1, Ok representation) } } }
        |> failure "I1"

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``I2 selector exactly covers alternatives including elided singleton`` union =
    let held = fixture union false false
    let singleton = held |> changeRow elideSecond |> renew
    Assert.Empty(Integrity.callableAggregates singleton)
    for count in [0;1;3] do
        held |> changeRow (fun row -> {row with Selector = row.Selector |> Option.map (fun selector -> {selector with UpperExclusive = count})}) |> failure "I2"
    held |> changeRow (fun row -> {row with Alternatives = [row.Alternatives.Head; {row.Alternatives.Head with Ordinal = 1}]}) |> failure "I2"

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``I3 equal code and layouts do not permit crossing or dropping environments`` union =
    let held = fixture union true false
    for environment in [Some(NodeId 21); None] do
        held |> changeRow (fun row -> {row with Alternatives = {row.Alternatives.Head with EnvironmentValue = environment} :: row.Alternatives.Tail}) |> failure "I3"
    let carrier = held.Emission.Callable.Carriers[NodeId 30]
    publish {held.Emission.Callable with Carriers = held.Emission.Callable.Carriers.Add(NodeId 30, {carrier with Lifetime = []})} held |> failure "I3"

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``I1 explicit environment projection retains only the callable environment`` union =
    let held = fixture union true false
    let c = held.Emission.Callable
    let changedProjection =
        { c with
            Carriers = c.Carriers.Add(NodeId 30, {c.Carriers[NodeId 30] with EnvironmentValue = Some(NodeId 30)})
            ValueShapes = c.ValueShapes.Add(NodeId 30, CallableValueShape.Callable(NodeId 30)) }
    let changed = publish changedProjection held
    let projected = changed |> changeRow (fun row ->
        let first = row.Alternatives.Head
        let placement = first.EnvironmentPlacement |> Option.map (fun placement ->
            {placement with Value = NodeId 30; Source = CallableAggregateEnvironmentSource.CallableEnvironmentView})
        let alternative = {first with EnvironmentValue = Some(NodeId 30); EnvironmentPlacement = placement}
        let participants = row.Participants |> List.map (fun participant ->
            if participant.Role = ParticipantRole.CallableEnvironment && participant.Ordinal = 0 then {participant with Node = NodeId 30} else participant)
        {row with Alternatives = alternative :: row.Alternatives.Tail; Participants = participants}) |> renew
    Assert.Empty(Integrity.callableAggregates projected)
    projected |> changeRow (fun row ->
        let first = row.Alternatives.Head
        let placement = first.EnvironmentPlacement |> Option.map (fun placement ->
            {placement with Source = CallableAggregateEnvironmentSource.EnvironmentValue})
        {row with Alternatives = {first with EnvironmentPlacement = placement} :: row.Alternatives.Tail}) |> failure "I1"

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``I4 identical signatures do not identify the receiving contract`` union =
    let held = fixture union false false
    let c = held.Emission.Callable
    let other = {c.Contracts[NodeId 100] with Identity = NodeId 102; Participants = [p ParticipantRole.CallableContract 0 102 102]}
    let crossedProjection =
        { c with
            Contracts = c.Contracts.Add(NodeId 102, other)
            Carriers = c.Carriers.Add(NodeId 30, {c.Carriers[NodeId 30] with Contract = Ok(NodeId 102)}) }
    let crossed = publish crossedProjection held
    crossed |> changeRow (fun row -> {row with Alternatives = {row.Alternatives.Head with Contract = NodeId 102} :: row.Alternatives.Tail}) |> failure "I4"
    publish {c with Contracts = Map.empty} held |> failure "I4"

[<Fact>]
let ``I4 physically omitted parameters are part of the convention`` () =
    let held = fixture false false false
    let c = held.Emission.Callable
    let carriers = c.Carriers |> Map.map (fun _ carrier ->
        {carrier with Parameters = ["unused", unitType, NodeId 41]; ParameterShapes = [CallableValueShape.Data(NodeId 41)]
                      OmittedParameters = Set.singleton(NodeId 41)})
    let contract = {c.Contracts[NodeId 100] with ParameterTypes = [unitType]; OmittedParameters = [0]}
    let matched = publish {c with Carriers = carriers; Contracts = c.Contracts.Add(NodeId 100, contract)} held |> renew
    Assert.Empty(Integrity.callableAggregates matched)
    let wrongContract = {contract with OmittedParameters = []}
    publish {matched.Emission.Callable with Contracts = matched.Emission.Callable.Contracts.Add(NodeId 100, wrongContract)} matched |> failure "I4"

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``I5 missing duplicate and changed formation incidence is rejected`` union =
    let held = fixture union true false
    held |> changeRow (fun row -> {row with Participants = row.Participants.Head :: row.Participants}) |> failure "I5"
    held |> changeRow (fun row -> {row with Participants = row.Participants |> List.filter (fun p -> p.Role <> ParticipantRole.CallableFormation)}) |> failure "I5"
    let missing = {held with Nodes = held.Nodes.Remove(NodeId 30)}
    missing |> failure "I5"

[<Fact>]
let ``I5 implementation evidence accepts an explicit symbol without importing its body`` () =
    let held = fixture false false false
    let c = held.Emission.Callable
    let contract = {c.Contracts[NodeId 100] with Participants = c.Contracts[NodeId 100].Participants @ [p ParticipantRole.CallableImplementation 0 100 10]}
    let symbols = c.Symbols.Add(NodeId 10, CallableSymbolName.ModuleBinding("Library", "callback"))
    let bodyFree =
        {held with Nodes = held.Nodes.Remove(NodeId 10)}
        |> publish {c with Contracts = c.Contracts.Add(NodeId 100, contract); Symbols = symbols}
        |> renew
    Assert.Empty(Integrity.callableAggregates bodyFree)
    Assert.False(bodyFree.Nodes.ContainsKey(NodeId 10))
    let absent = bodyFree.Emission.Callable
    publish {absent with Symbols = absent.Symbols.Remove(NodeId 10)} bodyFree |> failure "I5"

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``I5 a symbol never substitutes for a contract body or formal occurrence`` formal =
    let held = fixture false false false
    let role, id = if formal then ParticipantRole.CalleeParameter, 41 else ParticipantRole.CalleeBody, 11
    let c = held.Emission.Callable
    let contract = {c.Contracts[NodeId 100] with Participants = c.Contracts[NodeId 100].Participants @ [p role 0 100 id]}
    let admitted = publish {c with Contracts = c.Contracts.Add(NodeId 100, contract)} held |> renew
    Assert.Empty(Integrity.callableAggregates admitted)
    let absent = admitted.Emission.Callable
    {admitted with Nodes = admitted.Nodes.Remove(NodeId id)}
    |> publish {absent with Symbols = absent.Symbols.Add(NodeId id, CallableSymbolName.RootBinding "not-a-body")}
    |> renew
    |> failure "I5"

let private withSourcePremise () =
    let held = fixture false false false
    let premise : BoundarySourcePremise =
        { Shape = { Form = "representation-declaration"; Text = ["boolean"]; Numbers = []
                    References = []; Children = []; Parent = None; SourceType = unitType }
          EmbeddedTypes = []; ConstructorFacts = []; Reachable = false; Range = None
          ExternLibrary = None; ExternSymbol = None; HasExtern = false; Metadata = Map.empty }
    let c = held.Emission.Callable
    let contract =
        {c.Contracts[NodeId 100] with
            Participants = c.Contracts[NodeId 100].Participants @ [p ParticipantRole.Source 0 100 200]
            SourcePremises = Map.ofList [NodeId 200, premise]}
    publish {c with Contracts = c.Contracts.Add(NodeId 100, contract)} held |> renew

[<Fact>]
let ``I5 metadata premises require exact contract ownership and cannot borrow sibling evidence`` () =
    let held = withSourcePremise ()
    Assert.Empty(Integrity.callableAggregates held)
    Assert.False(held.Nodes.ContainsKey(NodeId 200))
    let c = held.Emission.Callable
    let contract = c.Contracts[NodeId 100]
    let missing = {contract with SourcePremises = Map.empty}
    publish {c with Contracts = c.Contracts.Add(NodeId 100, missing)} held |> failure "I5"
    let extra = {contract with SourcePremises = contract.SourcePremises.Add(NodeId 201, contract.SourcePremises[NodeId 200])}
    publish {c with Contracts = c.Contracts.Add(NodeId 100, extra)} held |> failure "I5"
    let sibling =
        {contract with Identity = NodeId 102
                       Participants = [p ParticipantRole.CallableContract 0 102 102; p ParticipantRole.Source 0 102 200]}
    publish {c with Contracts = c.Contracts.Add(NodeId 100, missing).Add(NodeId 102, sibling)} held |> failure "I5"

[<Fact>]
let ``I6 changed premise with identical physical results invalidates the earlier dependency account`` () =
    let held = withSourcePremise ()
    let c = held.Emission.Callable
    let contract = c.Contracts[NodeId 100]
    let premise = contract.SourcePremises[NodeId 200]
    let changed =
        {contract with SourcePremises = contract.SourcePremises.Add(NodeId 200, {premise with Metadata = Map.ofList ["source-version", (["changed"], [], [], None)]})}
    let next = publish {c with Contracts = c.Contracts.Add(NodeId 100, changed)} held
    Assert.Equal(contract.ResultRepresentation, changed.ResultRepresentation)
    Assert.Equal<(int * ValueRepresentation) list>(contract.ParameterRepresentations, changed.ParameterRepresentations)
    next |> failure "I6"
    let renewed = renew next
    Assert.Empty(Integrity.callableAggregates renewed)
    Assert.NotEqual<CallableAggregateDependencyAccount>(c.AggregateDependencies[NodeId 1], renewed.Emission.Callable.AggregateDependencies[NodeId 1])
    publish {renewed.Emission.Callable with AggregateDependencies = c.AggregateDependencies} renewed |> failure "I6"

[<Fact>]
let ``I5 union tag and payload evidence must match the current constructor`` () =
    let held = fixture true false false
    held |> changeRow (fun row -> {row with Tag = None}) |> failure "I5"
    for kind in [SemanticKind.UnionCase("None", 1, None); SemanticKind.UnionCase("Some", 0, Some(NodeId 31))] do
        {held with Nodes = held.Nodes.Add(NodeId 1, {held.Nodes[NodeId 1] with Kind = kind})} |> failure "I5"

[<Fact>]
let ``interior Option FnPtr has no absent callable alternative or native null carrier`` () =
    let held = fixture true false true
    Assert.Empty(Integrity.callableAggregates held)
    let absent = held |> changeRow (fun row ->
        let tag =
            { row.Tag.Value with
                CaseOrdinal = 1; PayloadOrdinal = None; Payload = None
                Participants = [p ParticipantRole.AggregateConstructor 0 1 1; p ParticipantRole.AggregateTag 0 1 5] }
        { row with
            Alternatives = []; Selector = None; FormationInputs = []; Value = None; SelectedAlternative = None; Tag = Some tag
            Participants = [p ParticipantRole.AggregateValue 0 1 1; p ParticipantRole.AggregateSource 0 1 1; p ParticipantRole.AggregateSlot 0 1 101] })
    let absent = {absent with Nodes = absent.Nodes.Add(NodeId 1, {absent.Nodes[NodeId 1] with Kind = SemanticKind.UnionCase("None", 1, None); Children = []})} |> renew
    Assert.Empty(Integrity.callableAggregates absent)
    absent |> changeRow (fun row -> {row with Selector = Some {Lower = 0; UpperExclusive = 0; Storage = None; Slot = None; ByteOffset = None}}) |> failure "I2"
    absent |> changeRow (fun row -> {row with Alternatives = held.Emission.Callable.AggregateValues[NodeId 1].Head.Alternatives}) |> failure "I2"

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``I6 same output and code with changed lifetime support requires a new published account`` union =
    let held = fixture union true false
    let oldAccount = held.Emission.Callable.AggregateDependencies[NodeId 1]
    let c = held.Emission.Callable
    let changed = publish {c with Carriers = c.Carriers.Add(NodeId 30, {c.Carriers[NodeId 30] with Lifetime = [p ParticipantRole.CallableLifetime 0 30 91]})} held
    Assert.Equal(held.Nodes[NodeId 11], changed.Nodes[NodeId 11])
    Assert.Equal(c.Carriers[NodeId 30].Implementation, changed.Emission.Callable.Carriers[NodeId 30].Implementation)
    changed |> failure "I6"
    let renewed = renew changed
    Assert.Empty(Integrity.callableAggregates renewed)
    Assert.NotEqual<CallableAggregateDependencyAccount>(oldAccount, renewed.Emission.Callable.AggregateDependencies[NodeId 1])
    publish {renewed.Emission.Callable with AggregateDependencies = Map.ofList [NodeId 1, oldAccount]} renewed |> failure "I6"

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``I6 duplicated rows and source operand changes cannot reuse selection evidence`` union =
    let held = fixture union true false
    let c = held.Emission.Callable
    let account = c.AggregateDependencies[NodeId 1]
    publish {c with AggregateDependencies = c.AggregateDependencies.Add(NodeId 1, {account with Values = account.Values @ account.Values})} held |> failure "I6"
    {held with Nodes = held.Nodes.Add(NodeId 30, {held.Nodes[NodeId 30] with Children = [NodeId 90;NodeId 90]})} |> failure "I6"

[<Fact>]
let ``native pending contract cannot become an aggregate callable selection`` () =
    let held = fixture true false true
    let c = held.Emission.Callable
    publish {c with Carriers = c.Carriers.Add(NodeId 30, {c.Carriers[NodeId 30] with Contract = Error "native ABI is pending"})} held |> failure "I4"

[<Fact>]
let ``closed singleton component occupies zero bytes`` () =
    let held = fixture false false false |> changeRow (fun row ->
        let singleton = elideSecond row
        {singleton with Bytes = 0; Alignment = 1})
    let representation = ValueRepresentation.Record(["invoke", ValueRepresentation.CallableComponent(NodeId 101, ValueRepresentation.Record([], Some([], 0, 1)))], Some([0], 0, 1))
    let held = {held with Emission = {held.Emission with Numeric = {held.Emission.Numeric with OccurrenceRepresentations = held.Emission.Numeric.OccurrenceRepresentations.Add(NodeId 1, Ok representation)}}} |> renew
    Assert.Empty(Integrity.callableAggregates held)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``absent callable needs no invented contract even when other case has scalar payload`` scalarPayload =
    let held = fixture true false true
    let payload = if scalarPayload then Some(NodeId 91) else None
    let ordinal = if scalarPayload then Some 0 else None
    let tagParticipants =
        [p ParticipantRole.AggregateConstructor 0 1 1; p ParticipantRole.AggregateTag 0 1 5] @
        (if scalarPayload then [p ParticipantRole.AggregatePayload 0 1 91] else [])
    let absent = held |> changeRow (fun row ->
        { row with
            Alternatives = []; Selector = None; FormationInputs = []; Value = None; SelectedAlternative = None
            Bytes = 0; Alignment = 1
            Tag = Some {row.Tag.Value with CaseOrdinal = 1; PayloadOrdinal = ordinal; Payload = payload; Participants = tagParticipants}
            Participants = [p ParticipantRole.AggregateValue 0 1 1; p ParticipantRole.AggregateSource 0 1 1; p ParticipantRole.AggregateSlot 0 1 101] })
    let c = absent.Emission.Callable
    let slot =
        { c.AggregateSlots[NodeId 101] with
            Contract = Error "No callable formation exists in the selected case."
            Participants = [p ParticipantRole.AggregateSlot 0 101 101] }
    let absentProjection = {c with Contracts = Map.empty; Carriers = Map.empty; AggregateSlots = c.AggregateSlots.Add(NodeId 101, slot)}
    let absent =
        {absent with Nodes = absent.Nodes.Add(NodeId 1, {absent.Nodes[NodeId 1] with Kind = SemanticKind.UnionCase("Other", 1, payload); Children = Option.toList payload})}
        |> publish absentProjection
        |> renew
    Assert.Empty(Integrity.callableAggregates absent)
    Assert.Empty(absent.Emission.Callable.AggregateDependencies[NodeId 1].Contracts)
    Assert.Empty(absent.Emission.Callable.AggregateDependencies[NodeId 1].Carriers)

[<Fact>]
let ``I4 equal source types cannot conceal different physical scalar conventions`` () =
    let held = fixture false false false
    let c = held.Emission.Callable
    let physical = ValueRepresentation.Scalar SettledSlot.Bool
    let carriers = c.Carriers |> Map.map (fun _ carrier ->
        {carrier with Parameters = ["argument", unitType, NodeId 41]; ParameterShapes = [CallableValueShape.Data(NodeId 41)]})
    let contract = {c.Contracts[NodeId 100] with ParameterTypes = [unitType]; ParameterRepresentations = [0, physical]}
    let matched = publish {c with Carriers = carriers; Contracts = c.Contracts.Add(NodeId 100, contract)} held |> renew
    Assert.Empty(Integrity.callableAggregates matched)
    for site in [NodeId 41; NodeId 11] do
        let numeric =
            { matched.Emission.Numeric with
                OccurrenceRepresentations = matched.Emission.Numeric.OccurrenceRepresentations.Add(site, Ok(ValueRepresentation.Scalar(SettledSlot.Integer(8, None)))) }
        {matched with Emission = {matched.Emission with Numeric = numeric}}
        |> failure "I4"

[<Fact>]
let ``I6 numeric support claims remain exact without publishing an obligation body node`` () =
    let held = fixture false false false
    let claim : ObligationInfo =
        { Id = "aggregate-numeric-support"; Kind = "storage-reservation"; Logic = "QF_LIA"
          Statement = "Exact admitted representation premise"; Source = "contract-test.clef:1:0"; Refs = []
          Body = ObligationBody.StorageReservation(1, 2) }
    let c = held.Emission.Callable
    let contract = c.Contracts[NodeId 100]
    let current =
        {held with CurrentClaims = Map.ofList [NodeId 99, claim]}
        |> publish {c with Contracts = c.Contracts.Add(NodeId 100, {contract with Participants = contract.Participants @ [p ParticipantRole.Source 0 100 99]})}
        |> renew
    Assert.False(current.Nodes.ContainsKey(NodeId 99))
    Assert.Empty(Integrity.callableAggregates current)
    let changed = {current with CurrentClaims = current.CurrentClaims.Add(NodeId 99, {claim with Body = ObligationBody.StorageReservation(2, 3)})}
    Assert.Equal(current.Nodes[NodeId 11], changed.Nodes[NodeId 11])
    changed |> failure "I6"
    let fresh = renew changed
    Assert.Empty(Integrity.callableAggregates fresh)
    Assert.NotEqual<CallableAggregateDependencyAccount>(current.Emission.Callable.AggregateDependencies[NodeId 1], fresh.Emission.Callable.AggregateDependencies[NodeId 1])
    {fresh with CurrentClaims = Map.empty} |> failure "I5"

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``I5 nominal declaration facts authorize metadata without executable type bodies`` union =
    let held = nominalFixture union
    Assert.Empty(Integrity.callableAggregates held)
    Assert.False(held.Nodes.ContainsKey(NodeId 200))
    Assert.DoesNotContain(held.SourceReadings.Entries, fun entry -> entry.Focus = NodeId 200)
    Assert.DoesNotContain(held.Emission.Callable.AggregateDependencies[NodeId 1].Sources, fun source -> source.Node = NodeId 200)
    Assert.Single(held.Emission.Callable.AggregateDependencies[NodeId 1].Slots.Head.DeclarationFacts) |> ignore
    // Metadata authority is role-specific; it cannot supply a value occurrence.
    held |> changeRow (fun row -> {row with Participants = row.Participants @ [p ParticipantRole.Source 0 1 200]})
    |> failure "I5"

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``I5 declaration facts require exact role group ordinal and nominal shape`` union =
    let held = nominalFixture union
    held |> changeSlot (fun slot -> {slot with DeclarationFacts = []}) |> failure "I5"
    held |> changeSlot (fun slot -> {slot with DeclarationFacts = slot.DeclarationFacts @ slot.DeclarationFacts}) |> failure "I5"
    for group, ordinal in [100, 0; 101, -1; 101, 1] do
        held |> changeSlot (fun slot ->
            let participants =
                slot.Participants |> List.map (fun participant ->
                    if participant.Role = ParticipantRole.AggregateDeclaration then
                        {participant with Group = NodeId group; Ordinal = ordinal}
                    else participant)
            {slot with Participants = participants}) |> failure "I5"
    for definition in [CallableAggregateDeclarationDefinition.RecordDef []; CallableAggregateDeclarationDefinition.UnionDef []] do
        held |> changeSlot (fun slot ->
            {slot with DeclarationFacts = [{slot.DeclarationFacts.Head with Definition = definition}]}) |> failure "I5"
    for declaredType in [unitType; TypeIdentity.Tuple(false, [])] do
        held |> changeSlot (fun slot ->
            {slot with DeclarationFacts = [{slot.DeclarationFacts.Head with DeclaredType = declaredType}]}) |> failure "I5"

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``I6 same declaration identity with changed metadata cannot reuse its earlier account`` union =
    let held = nominalFixture union
    let oldAccount = held.Emission.Callable.AggregateDependencies[NodeId 1]
    let changed = held |> changeSlot (fun slot ->
        let fact = slot.DeclarationFacts.Head
        let definition =
            match fact.Definition with
            | CallableAggregateDeclarationDefinition.RecordDef fields ->
                CallableAggregateDeclarationDefinition.RecordDef(fields @ ["newData", boolType])
            | CallableAggregateDeclarationDefinition.UnionDef cases ->
                CallableAggregateDeclarationDefinition.UnionDef(cases @ ["Other", []])
        {slot with DeclarationFacts = [{fact with Definition = definition}]})
    Assert.Equal(held.Nodes[NodeId 11], changed.Nodes[NodeId 11])
    Assert.Equal(held.Emission.Callable.Carriers[NodeId 30], changed.Emission.Callable.Carriers[NodeId 30])
    Assert.Equal(held.Emission.Callable.AggregateSlots[NodeId 101].Declaration,
                 changed.Emission.Callable.AggregateSlots[NodeId 101].Declaration)
    changed |> failure "I6"
    let fresh = renew changed
    Assert.Empty(Integrity.callableAggregates fresh)
    Assert.NotEqual<CallableAggregateDependencyAccount>(oldAccount, fresh.Emission.Callable.AggregateDependencies[NodeId 1])
    publish {fresh.Emission.Callable with AggregateDependencies = Map.ofList [NodeId 1, oldAccount]} fresh |> failure "I6"

let private sharedGenericDeclaration () =
    let held = nominalFixture false
    let variable = TypeIdentity.Variable(7, TypeParamKind.Type)
    let constructor : ConstructorIdentity =
        {Declaration = {Module = ["ContractTests"]; Name = "GenericFunctions"}
         Parameters = [TypeParamKind.Type]; NativeKind = None}
    let aggregateType = TypeIdentity.Application(constructor, [unitType])
    let definition =
        CallableAggregateDeclarationDefinition.RecordDef
            ["left", TypeIdentity.Function(variable, variable); "right", TypeIdentity.Function(variable, variable)]
    let fact : CallableAggregateDeclarationFact =
        {Identity = NodeId 200; DeclaredType = TypeIdentity.Application(constructor, [variable])
         Definition = definition}
    let c = held.Emission.Callable
    let firstSlot = {c.AggregateSlots[NodeId 101] with AggregateType = aggregateType; DeclarationFacts = [fact]}
    let slotParticipants =
        firstSlot.Participants |> List.map (fun participant ->
            let node = if participant.Role = ParticipantRole.AggregateSlot then NodeId 102 else participant.Node
            {participant with Group = NodeId 102; Node = node})
    let secondSlot =
        {firstSlot with Identity = NodeId 102; Path = [CallableAggregatePathStep.RecordField 1]
                        Participants = slotParticipants}
    let firstValue = c.AggregateValues[NodeId 1].Head
    let valueParticipants =
        firstValue.Participants |> List.map (fun participant ->
            if participant.Role = ParticipantRole.AggregateSlot then {participant with Node = NodeId 102}
            else participant)
    let secondValue = {firstValue with Slot = NodeId 102; Participants = valueParticipants}
    let data = ValueRepresentation.Record(["selector", ValueRepresentation.Scalar(SettledSlot.Integer(8, None))], Some([0], 1, 1))
    let representation =
        ValueRepresentation.Record(
            ["left", ValueRepresentation.CallableComponent(NodeId 101, data)
             "right", ValueRepresentation.CallableComponent(NodeId 102, data)], Some([0; 1], 2, 1))
    let aggregate =
        {held.Nodes[NodeId 1] with
            Type = aggregateType
            Kind = SemanticKind.RecordExpr(["left", NodeId 30; "right", NodeId 30], None)
            Children = [NodeId 30; NodeId 30]}
    let numeric =
        {held.Emission.Numeric with
            SourceTypes = held.Emission.Numeric.SourceTypes.Add(NodeId 1, aggregateType)
            OccurrenceRepresentations = held.Emission.Numeric.OccurrenceRepresentations.Add(NodeId 1, Ok representation)}
    let nominal = {held with Nodes = held.Nodes.Add(NodeId 1, aggregate); Emission = {held.Emission with Numeric = numeric}}
    publish {c with AggregateSlots = Map.ofList [NodeId 101, firstSlot; NodeId 102, secondSlot]
                    AggregateValues = Map.ofList [NodeId 1, [firstValue; secondValue]]} nominal
    |> renewWithSlots [101; 102]

[<Fact>]
let ``I5 separate slots retain repeated shared generic declaration incidence`` () =
    let held = sharedGenericDeclaration ()
    Assert.Empty(Integrity.callableAggregates held)
    let account = held.Emission.Callable.AggregateDependencies[NodeId 1]
    Assert.Equal(2, account.Slots.Length)
    Assert.Equal<CallableAggregateDeclarationFact list>(account.Slots[0].DeclarationFacts, account.Slots[1].DeclarationFacts)
    let uses = account.Participants |> List.filter (fun participant -> participant.Role = ParticipantRole.AggregateDeclaration)
    Assert.Equal<Participant list>([p ParticipantRole.AggregateDeclaration 0 101 200; p ParticipantRole.AggregateDeclaration 0 102 200], uses)

[<Fact>]
let ``I5 one declaration identity cannot carry conflicting canonical slot facts`` () =
    let held = sharedGenericDeclaration ()
    let c = held.Emission.Callable
    let second = c.AggregateSlots[NodeId 102]
    let fact = second.DeclarationFacts.Head
    let definition = CallableAggregateDeclarationDefinition.RecordDef ["left", second.SourceType; "renamed", second.SourceType]
    let changed = {fact with Definition = definition}
    publish {c with AggregateSlots = c.AggregateSlots.Add(NodeId 102, {second with DeclarationFacts = [changed]})} held
    |> renewWithSlots [101; 102]
    |> failure "I5"

let private nativeSingleton width =
    let held =
        fixture false false true
        |> changeRow (fun row -> {elideSecond row with Bytes = 0; Alignment = 1})
        |> changeNativeConvention (fun convention ->
            {convention with Target = {convention.Target with Dimensions = Map.ofList ["Register", width; "Pointer", width]}})
    let heldComponent = ValueRepresentation.CallableComponent(NodeId 101, ValueRepresentation.Record([], Some([], 0, 1)))
    let representation = ValueRepresentation.Record(["invoke", heldComponent], Some([0], 0, 1))
    let numeric =
        {held.Emission.Numeric with
            OccurrenceRepresentations = held.Emission.Numeric.OccurrenceRepresentations.Add(NodeId 1, Ok representation)}
    {held with
        Platform = {Register = Ok width; Pointer = Ok width}
        Emission = {held.Emission with Numeric = numeric}}
    |> renew

[<Theory>]
[<InlineData(32)>]
[<InlineData(64)>]
let ``native singleton retains portable convention and program residence without code storage`` width =
    let held = nativeSingleton width
    Assert.Empty(Integrity.callableAggregates held)
    let c = held.Emission.Callable
    let carrier = c.Carriers[NodeId 30]
    Assert.Equal(CallableKind.NativeEntry, carrier.Kind)
    Assert.Equal(Ok(NodeId 100), carrier.Contract)
    Assert.Equal<CallableEnvironment option>(None, carrier.Environment)
    Assert.Equal<NodeId option>(None, carrier.EnvironmentValue)
    Assert.Equal(0, c.AggregateValues[NodeId 1].Head.Bytes)
    Assert.Empty(held.CurrentClaims)
    Assert.False(held.Nodes.ContainsKey(NodeId 400))
    Assert.False(held.Nodes.ContainsKey(NodeId 401))
    Assert.Equal<Participant list>(
        [p ParticipantRole.CallableLifetime 0 100 400; p ParticipantRole.CallableLifetime 1 100 401
         p ParticipantRole.CallableLifetime 2 100 10], carrier.Lifetime)
    match c.Contracts[NodeId 100].Convention with
    | CallableConvention.CompilerOwnedPortable convention ->
        Assert.Equal(width, convention.Target.Dimensions["Pointer"])
        Assert.Equal<(int * CallableConversion) list>([0, CallableConversion.Identity(ValueRepresentation.Scalar SettledSlot.Bool)], convention.ParameterConversions)
        Assert.Equal(CallableConversion.Identity(ValueRepresentation.Scalar SettledSlot.Bool), convention.ResultConversion)
        Assert.Equal(NodeId 400, convention.CodeLifetime.Module)
    | _ -> failwith "A native entry lost its compiler-owned receiving convention."

[<Theory>]
[<InlineData("missing")>]
[<InlineData("ordinal")>]
[<InlineData("duplicate")>]
[<InlineData("parameter")>]
[<InlineData("result")>]
let ``I4 native identity conversions must match the exact physical signature`` mutation =
    let held = nativeSingleton 64
    Assert.Empty(Integrity.callableAggregates held)
    held |> changeNativeConvention (fun convention ->
        match mutation with
        | "missing" -> {convention with ParameterConversions = []}
        | "ordinal" -> {convention with ParameterConversions = [1, snd convention.ParameterConversions.Head]}
        | "duplicate" -> {convention with ParameterConversions = convention.ParameterConversions @ convention.ParameterConversions}
        | "parameter" -> {convention with ParameterConversions = [0, CallableConversion.Identity(ValueRepresentation.Scalar(SettledSlot.Integer(8, None)))]}
        | "result" -> {convention with ResultConversion = CallableConversion.Identity(ValueRepresentation.Scalar SettledSlot.Unit)}
        | _ -> failwith "Unknown conversion control.")
    |> renew |> failure "I4"

[<Fact>]
let ``I4 internally matching pointer representations do not authorize the scalar native convention`` () =
    let held = nativeSingleton 64
    Assert.Empty(Integrity.callableAggregates held)
    let pointer = ValueRepresentation.Scalar(SettledSlot.Pointer 1)
    let changed =
        held
        |> changeContract (fun contract -> {contract with ParameterRepresentations = [0, pointer]})
        |> changeNativeConvention (fun convention -> {convention with ParameterConversions = [0, CallableConversion.Identity pointer]})
    let numeric =
        {changed.Emission.Numeric with
            OccurrenceRepresentations = changed.Emission.Numeric.OccurrenceRepresentations.Add(NodeId 41, Ok pointer)}
    {changed with Emission = {changed.Emission with Numeric = numeric}}
    |> renew |> failure "I4"

[<Fact>]
let ``I4 native target and callable kind cannot be substituted`` () =
    let held = nativeSingleton 64
    Assert.Empty(Integrity.callableAggregates held)
    held |> changeNativeConvention (fun convention ->
        {convention with Target = {convention.Target with Dimensions = convention.Target.Dimensions.Add("Pointer", 32)}})
    |> renew |> failure "I4"
    held |> changeNativeConvention (fun convention ->
        {convention with Target = {convention.Target with Dimensions = convention.Target.Dimensions.Remove "Register"}})
    |> renew |> failure "I4"
    held |> changeContract (fun contract -> {contract with Convention = CallableConvention.Ordinary})
    |> renew |> failure "I4"
    // Change both kind fields together: equal signatures still cannot give an
    // ordinary carrier authority to use a native-entry convention.
    let c = held.Emission.Callable
    let substituted =
        {c with
            Contracts = c.Contracts.Add(NodeId 100, {c.Contracts[NodeId 100] with Kind = CallableKind.OrdinaryFlatClosure})
            Carriers = c.Carriers |> Map.map (fun _ carrier -> {carrier with Kind = CallableKind.OrdinaryFlatClosure})}
    publish substituted held
    |> renew |> failure "I4"

[<Fact>]
let ``I3 native receiving convention preserves explicit environment absence`` () =
    let held = nativeSingleton 64
    Assert.Empty(Integrity.callableAggregates held)
    held |> changeContract (fun contract -> {contract with EnvironmentBytes = Some 0})
    |> renew |> failure "I3"
    let c = held.Emission.Callable
    let captured = {c.Carriers[NodeId 30] with Environment = Some {Owner = NodeId 40; Formal = NodeId 41}; EnvironmentValue = Some(NodeId 20)}
    publish {c with Carriers = c.Carriers.Add(NodeId 30, captured)} held |> renew |> failure "I3"

[<Theory>]
[<InlineData("empty")>]
[<InlineData("unrelated")>]
[<InlineData("ordinal")>]
[<InlineData("group")>]
let ``I3 native lifetime requires the exact contract owned residence vector`` mutation =
    let held = nativeSingleton 64
    Assert.Empty(Integrity.callableAggregates held)
    let c = held.Emission.Callable
    let carrier = c.Carriers[NodeId 30]
    let lifetime =
        match mutation with
        | "empty" -> []
        | "unrelated" -> [p ParticipantRole.CallableLifetime 0 100 90]
        | "ordinal" -> carrier.Lifetime |> List.map (fun participant -> {participant with Ordinal = 2 - participant.Ordinal})
        | "group" -> carrier.Lifetime |> List.map (fun participant -> {participant with Group = NodeId 1})
        | _ -> failwith "Unknown lifetime control."
    publish {c with Carriers = c.Carriers.Add(NodeId 30, {carrier with Lifetime = lifetime})} held
    |> renew |> failure "I3"

[<Theory>]
[<InlineData("parent")>]
[<InlineData("membership")>]
[<InlineData("duplicate-member")>]
[<InlineData("binding-child")>]
[<InlineData("capture")>]
let ``I3 native residence checks current declaration incidence not just node presence`` mutation =
    let held = nativeSingleton 64
    Assert.Empty(Integrity.callableAggregates held)
    held |> changeContract (fun contract ->
        let node, change : NodeId * (BoundaryDeclarationFact -> BoundaryDeclarationFact) =
            match mutation with
            | "parent" -> NodeId 401, fun shape -> {shape with Parent = Some(NodeId 90)}
            | "membership" -> NodeId 400, fun shape -> {shape with References = []}
            | "duplicate-member" -> NodeId 400, fun shape -> {shape with References = [NodeId 401; NodeId 401]}
            | "binding-child" -> NodeId 401, fun shape -> {shape with Children = [NodeId 11]}
            | "capture" -> NodeId 10, fun shape -> {shape with Text = ["RegularClosure"; "argument"; "captured"]; Numbers = [1I; 1I; 1I; 0I; 0I]}
            | _ -> failwith "Unknown residence control."
        let premise = contract.SourcePremises[node]
        {contract with SourcePremises = contract.SourcePremises.Add(node, {premise with Shape = change premise.Shape})})
    |> renew |> failure "I3"

[<Fact>]
let ``I3 native module membership distinguishes lexical members from attached children`` () =
    let held = nativeSingleton 64
    Assert.Empty(Integrity.callableAggregates held)
    let withModuleIncidence references =
        held |> changeContract (fun contract ->
            let scope = contract.SourcePremises[NodeId 400]
            let shape = {scope.Shape with References = references; Children = [NodeId 401]}
            {contract with SourcePremises = contract.SourcePremises.Add(NodeId 400, {scope with Shape = shape})})
        |> renew
    // Before Startup, both the kind's Reference/Member edge and the attached
    // structural child occur. The member prefix authorizes the declaration.
    let beforeStartup = withModuleIncidence [NodeId 401; NodeId 401]
    Assert.Empty(Integrity.callableAggregates beforeStartup)
    Assert.False(beforeStartup.Nodes.ContainsKey(NodeId 400))
    Assert.False(beforeStartup.Nodes.ContainsKey(NodeId 401))
    // A structural attachment alone is not lexical module membership.
    withModuleIncidence [NodeId 401] |> failure "I3"

[<Fact>]
let ``I6 changed native residence preserves the result but withdraws the old dependency account`` () =
    let held = nativeSingleton 64
    Assert.Empty(Integrity.callableAggregates held)
    let c = held.Emission.Callable
    let oldAccount = c.AggregateDependencies[NodeId 1]
    let moveParticipant (participant: Participant) =
        if participant.Node = NodeId 400 then {participant with Node = NodeId 402} else participant
    let changed =
        held
        |> changeNativeConvention (fun convention -> {convention with CodeLifetime = {convention.CodeLifetime with Module = NodeId 402}})
        |> changeContract (fun contract ->
            let binding = contract.SourcePremises[NodeId 401]
            let premises =
                contract.SourcePremises
                |> Map.remove (NodeId 400)
                |> Map.add (NodeId 402) contract.SourcePremises[NodeId 400]
                |> Map.add (NodeId 401) {binding with Shape = {binding.Shape with Parent = Some(NodeId 402)}}
            {contract with
                Participants = contract.Participants |> List.map moveParticipant
                SourcePremises = premises})
    let callable =
        {changed.Emission.Callable with
            Carriers = c.Carriers |> Map.map (fun _ carrier -> {carrier with Lifetime = List.map moveParticipant carrier.Lifetime})}
    let changed = publish callable changed
    Assert.Equal(held.Nodes[NodeId 11], changed.Nodes[NodeId 11])
    Assert.Equal(held.Emission.Numeric, changed.Emission.Numeric)
    Assert.Equal(c.Carriers[NodeId 30].Implementation, changed.Emission.Callable.Carriers[NodeId 30].Implementation)
    changed |> failure "I6"
    let fresh = renew changed
    Assert.Empty(Integrity.callableAggregates fresh)
    Assert.NotEqual<CallableAggregateDependencyAccount>(oldAccount, fresh.Emission.Callable.AggregateDependencies[NodeId 1])
    publish {fresh.Emission.Callable with AggregateDependencies = Map.ofList [NodeId 1, oldAccount]} fresh |> failure "I6"
