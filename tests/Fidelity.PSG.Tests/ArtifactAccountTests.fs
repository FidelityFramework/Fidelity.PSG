/// These fixtures state contract rows. They neither admit source residence nor
/// discharge a source or artifact obligation on behalf of the compiler.
module Fidelity.PSG.Tests.ArtifactAccountTests

open Xunit
open Fidelity.PSG
open Fidelity.PSG.Tests.Build

let private participant role ordinal group node : Participant =
    { Node = NodeId node; Role = role; Ordinal = ordinal; Group = NodeId group }

let private obligation name kind body : ObligationInfo =
    { Id = name; Kind = kind; Logic = "QF_LIA"; Statement = "Contract fixture"
      Source = "contract-test.clef"; Refs = []; Body = body }

let private withStorage storage (original: Revision) =
    { original with Emission = { original.Emission with Storage = storage } }

let private hasViolation part (original: Revision) =
    Assert.Contains(Integrity.check original, fun violation -> violation.Part = part)
    match Binary.encode BinaryTests.limits original with
    | Error(BinaryError.InvalidRevision failures) ->
        Assert.Contains(failures, fun violation -> violation.Part = part)
    | other -> failwithf "An inconsistent artifact account was accepted: %A" other

let private pendingReservations =
    let original = revision [node 1 (SemanticKind.EnvironmentAllocate(NodeId 1)) []
                             node 2 (SemanticKind.Binding("first", false, false, None)) []
                             node 3 (SemanticKind.Binding("second", false, false, None)) []]
    let reservation claim binding : EnvironmentReservationAccount =
        { Claim = NodeId claim; Allocation = NodeId 1; Binding = NodeId binding; Initializer = NodeId 1
          Participants =
            [ participant ParticipantRole.EnvironmentAllocation 0 1 1
              participant ParticipantRole.EnvironmentBinding 0 1 binding
              participant ParticipantRole.EnvironmentInitializer 0 1 1
              // Repeated identity, different ordered role occurrences; no body.
              participant ParticipantRole.EnvironmentAuthorityInput 0 1 900
              participant ParticipantRole.EnvironmentAuthorityInput 1 1 900
              participant ParticipantRole.EnvironmentDeclarationInput 0 1 901 ] }
    let accounts = [reservation 40 2; reservation 41 3]
    let claims =
        accounts
        |> List.map (fun row ->
            let claim =
                obligation (sprintf "proposal-%d" (NodeId.value row.Claim)) "environment-storage-reservation"
                    (ObligationBody.EnvironmentStorageReservation(None, None, None, None, None))
            row.Claim, claim)
        |> Map.ofList
    let storage = { original.Emission.Storage with EnvironmentReservations = accounts |> List.map (fun row -> row.Claim, row) |> Map.ofList }
    let assembled = withStorage storage original
    { assembled with
        CurrentClaims = claims; Obligations = claims |> Map.values |> Seq.toList
        ObligationSources = accounts |> List.map (fun row -> row.Claim, [row.Participants |> List.map (fun (p: Participant) -> p.Node)]) |> Map.ofList }

[<Fact>]
let ``two unresolved proposals retain separate claims without admitting a residence`` () =
    Assert.Empty(Integrity.check pendingReservations)
    Assert.Equal(2, pendingReservations.Emission.Storage.EnvironmentReservations.Count)
    Assert.Empty pendingReservations.Emission.Storage.EnvironmentResidences
    Assert.False(pendingReservations.Nodes.ContainsKey(NodeId 900))
    let bytes = Binary.encode BinaryTests.limits pendingReservations |> BinaryTests.take
    let copy = Binary.decode BinaryTests.limits bytes |> BinaryTests.take
    Assert.Equal(pendingReservations.Emission.Storage, copy.Emission.Storage)
    Assert.Equal<Map<NodeId, NodeId list list>>(pendingReservations.ObligationSources, copy.ObligationSources)
    Assert.Equal<byte>(bytes, Binary.encode BinaryTests.limits copy |> BinaryTests.take)

[<Theory>]
[<InlineData("key")>]
[<InlineData("claim-family")>]
[<InlineData("current-claim")>]
[<InlineData("source-vector")>]
[<InlineData("role-order")>]
[<InlineData("duplicate-role")>]
[<InlineData("ordinal")>]
[<InlineData("group")>]
let ``reservation accounts refuse stale keys claims and ordered role occurrences`` change =
    let original = pendingReservations
    let storage = original.Emission.Storage
    let row = storage.EnvironmentReservations[NodeId 40]
    let update participants =
        withStorage { storage with EnvironmentReservations = storage.EnvironmentReservations.Add(row.Claim, { row with Participants = participants }) } original
    let part, altered =
        match change with
        | "key" -> "Claim", withStorage { storage with EnvironmentReservations = storage.EnvironmentReservations.Remove(row.Claim).Add(NodeId 42, row) } original
        | "claim-family" -> "Claim", { original with CurrentClaims = original.CurrentClaims.Add(row.Claim, { original.CurrentClaims[row.Claim] with Kind = "other" }) }
        | "current-claim" -> "Claim", { original with CurrentClaims = original.CurrentClaims.Remove row.Claim }
        | "source-vector" -> "Participants", { original with ObligationSources = original.ObligationSources.Add(row.Claim, [row.Participants |> List.map (fun (p: Participant) -> p.Node) |> List.rev]) }
        | "role-order" -> "Participants", update (row.Participants |> List.rev)
        | "duplicate-role" -> "Allocation", update (row.Participants.Head :: row.Participants)
        | "ordinal" -> "Participants", update (row.Participants |> List.map (fun p -> if p.Role = ParticipantRole.EnvironmentAuthorityInput then {p with Ordinal = 0} else p))
        | "group" -> "Binding", update (row.Participants |> List.map (fun p -> if p.Role = ParticipantRole.EnvironmentBinding then {p with Group = NodeId 3} else p))
        | other -> failwithf "Unknown mutation %s" other
    hasViolation ("Emission.Storage.EnvironmentReservations." + part) altered

let private factoryResults =
    let parameters = ["value", boolType, NodeId 6; "destination", boolType, NodeId 7]
    let original = revision [node 1 (SemanticKind.EnvironmentAllocate(NodeId 1)) []
                             node 3 (SemanticKind.Literal(NativeLiteral.Bool true)) []
                             node 4 (SemanticKind.Application(NodeId 5, [NodeId 6; NodeId 3])) [5; 6; 3]
                             node 5 (SemanticKind.Lambda(parameters, NodeId 8, [], None, LambdaContext.RegularClosure)) [6; 7; 8]
                             node 6 (SemanticKind.PatternBinding "value") []
                             node 7 (SemanticKind.PatternBinding "destination") []
                             node 8 (SemanticKind.Literal(NativeLiteral.Bool true)) []
                             node 9 (SemanticKind.EnvironmentCreate(NodeId 1, [])) []]
    let name = CallableSymbolName.Anonymous(NodeId 5)
    let declaration : CallableEmissionDeclaration =
        { Lookup = NodeId 5; Implementation = NodeId 5; Parameters = parameters; Result = NodeId 8
          Context = LambdaContext.RegularClosure; Captures = []; Name = name; Parent = None; Participants = Set.empty }
    let call : CallableEmissionCall =
        { Site = NodeId 4; Implementation = NodeId 5; Parameters = parameters; Arguments = [NodeId 6; NodeId 3]
          Result = NodeId 8; SignatureData = Set.ofList [NodeId 6; NodeId 7; NodeId 8]; Participants = Set.empty }
    let account : EnvironmentFactoryResultAccount =
        { Call = NodeId 4; Ordinal = 0; Factory = NodeId 5; Constructor = NodeId 9
          Formal = NodeId 7; Allocation = NodeId 1; Destination = NodeId 3 }
    { original with
        Codata = { original.Codata with EnvironmentDestinations = Map.ofList [NodeId 9, NodeId 7] }
        Emission =
            { original.Emission with
                Callable =
                    { original.Emission.Callable with
                        Calls = Map.ofList [NodeId 4, call]
                        Symbols = Map.ofList [NodeId 5, name]
                        Declarations = Map.ofList [NodeId 5, declaration] }
                Storage = { original.Emission.Storage with EnvironmentFactoryResults = Map.ofList [account.Call, account] } } }

[<Fact>]
let ``factory result ordinal is independent of destination formal position`` () =
    Assert.Empty(Integrity.check factoryResults)
    let row = factoryResults.Emission.Storage.EnvironmentFactoryResults[NodeId 4]
    Assert.Equal(0, row.Ordinal)
    let _, _, destinationFormal = factoryResults.Emission.Callable.Calls[row.Call].Parameters[1]
    Assert.Equal(row.Formal, destinationFormal)
    let bytes = Binary.encode BinaryTests.limits factoryResults |> BinaryTests.take
    Assert.Equal(factoryResults.Emission.Storage, (Binary.decode BinaryTests.limits bytes |> BinaryTests.take).Emission.Storage)

[<Theory>]
[<InlineData("call")>]
[<InlineData("factory")>]
[<InlineData("formal")>]
[<InlineData("allocation")>]
[<InlineData("destination")>]
[<InlineData("constructor")>]
let ``factory account identities cannot be replaced by other current nodes`` change =
    let original = factoryResults
    let storage = original.Emission.Storage
    let row = storage.EnvironmentFactoryResults[NodeId 4]
    let field, altered =
        match change with
        | "call" -> "Call", { row with Call = NodeId 3 }
        | "factory" -> "Factory", { row with Factory = NodeId 6 }
        | "formal" -> "Formal", { row with Formal = NodeId 6 }
        | "allocation" -> "Allocation", { row with Allocation = NodeId 3 }
        | "destination" -> "Formal", { row with Destination = NodeId 6 }
        | "constructor" -> "Formal", { row with Constructor = NodeId 8 }
        | other -> failwithf "Unknown mutation %s" other
    withStorage {storage with EnvironmentFactoryResults = Map.ofList [NodeId 4, altered]} original
    |> hasViolation ("Emission.Storage.EnvironmentFactoryResults." + field)

let private initializationOrders =
    let original = revision [node 1 (SemanticKind.Literal(NativeLiteral.Bool true)) []
                             node 2 (SemanticKind.Binding("second", false, false, None)) []
                             node 3 (SemanticKind.Binding("first", false, false, None)) []]
    let moduleId = NodeId 100
    let port : SourcePortAccount = { Extent = 0; Stamp = "module-declarations"; Positions = Map.empty }
    let startup : StartupWitness =
        { EntryBinding = NodeId 1; EntryLambda = NodeId 1; SourceBinding = NodeId 1; SourceLambda = NodeId 1
          OriginalBody = NodeId 1; Spine = NodeId 1; EntryCall = NodeId 1; Symbol = "main"
          Initializers = [{Module = moduleId; Binding = NodeId 3; Initializer = NodeId 1; Ordinal = 0}
                          {Module = moduleId; Binding = NodeId 2; Initializer = NodeId 1; Ordinal = 1}]
          ValueBindings = Set.ofList [NodeId 2; NodeId 3] }
    let participants =
        [ participant ParticipantRole.InitializationBinding 0 2 2
          participant ParticipantRole.InitializationEntry 1 2 1
          participant ParticipantRole.InitializationSpine 1 2 1
          participant ParticipantRole.InitializationValue 1 2 1
          participant ParticipantRole.InitializationPhase 0 2 3
          participant ParticipantRole.InitializationPhase 1 2 2
          participant ParticipantRole.InitializationPhase 2 2 1
          participant ParticipantRole.InitializationParent 0 2 900 ]
    let account : ProgramInitializationOrderAccount = {Binding = NodeId 2; Claim = NodeId 40; Participants = participants}
    let claim = obligation "second-order" "program-initialization-order" (ObligationBody.ProgramInitializationOrder(1, 2, [0; 1; 2]))
    { original with
        SourceReadings =
            { original.SourceReadings with
                Ports = original.SourceReadings.Ports.Add((moduleId, OccurrencePort.ModuleDeclaration), port)
                ContextHeaders = Map.ofList [moduleId, {Identity = moduleId; Name = "module"; Ports = Map.ofList [OccurrencePort.ModuleDeclaration, port]}] }
        CurrentClaims = Map.ofList [account.Claim, claim]; Obligations = [claim]
        ObligationSources = Map.ofList [account.Claim, [participants |> List.map (fun (p: Participant) -> p.Node)]]
        Emission =
            { original.Emission with
                Storage =
                    { original.Emission.Storage with
                        Startup = Some startup
                        ProgramInitializationOrders = Map.ofList [account.Binding, account] } } }

[<Fact>]
let ``initialization binding zero and initializer ordinal one retain their distinct roles`` () =
    Assert.Empty(Integrity.check initializationOrders)
    Assert.False(initializationOrders.Nodes.ContainsKey(NodeId 900))
    let bytes = Binary.encode BinaryTests.limits initializationOrders |> BinaryTests.take
    let copy = Binary.decode BinaryTests.limits bytes |> BinaryTests.take
    Assert.Equal(initializationOrders.Emission.Storage, copy.Emission.Storage)

[<Theory>]
[<InlineData("key")>]
[<InlineData("ordinal")>]
[<InlineData("phase")>]
[<InlineData("vector")>]
let ``initialization accounts refuse changed binding ordinal phase and complete sources`` change =
    let original = initializationOrders
    let storage = original.Emission.Storage
    let account = storage.ProgramInitializationOrders[NodeId 2]
    let replace participants = withStorage {storage with ProgramInitializationOrders = Map.ofList [account.Binding, {account with Participants = participants}]} original
    let field, altered =
        match change with
        | "key" -> "Binding", withStorage {storage with ProgramInitializationOrders = Map.ofList [NodeId 3, account]} original
        | "ordinal" -> "Initializer", replace (account.Participants |> List.map (fun p -> if p.Role = ParticipantRole.InitializationValue then {p with Ordinal = 0} else p))
        | "phase" -> "Participants", replace (account.Participants |> List.map (fun p -> if p.Role = ParticipantRole.InitializationPhase && p.Ordinal = 1 then {p with Node = NodeId 3} else p))
        | "vector" -> "Participants", {original with ObligationSources = original.ObligationSources.Add(account.Claim, [[]])}
        | other -> failwithf "Unknown mutation %s" other
    hasViolation ("Emission.Storage.ProgramInitializationOrders." + field) altered

[<Fact>]
let ``all artifact tables preserve exact ordered fields through the generated storage codec`` () =
    // A field-level codec fixture does not claim these independently stated
    // rows together form a structurally valid, source-admitted revision.
    let reservations = pendingReservations.Emission.Storage.EnvironmentReservations
    let residence : EnvironmentResidenceAccount =
        { Allocation = NodeId 1; Binding = NodeId 2; Owner = NodeId 10; Implementation = NodeId 11
          Formal = NodeId 12; ReservationClaim = NodeId 40; AuthorityInputs = [NodeId 900; NodeId 900]
          BindingPath = [NodeId 1; NodeId 8; NodeId 2]; LayoutClaims = [NodeId 42; NodeId 43]
          DeclarationInputs = [NodeId 901; NodeId 902] }
    let original =
        { Empty.storage with
            EnvironmentReservations = reservations
            EnvironmentFactoryResults = factoryResults.Emission.Storage.EnvironmentFactoryResults
            EnvironmentResidences = Map.ofList [residence.Allocation, residence]
            ProgramInitializationOrders = initializationOrders.Emission.Storage.ProgramInitializationOrders }
    let plan = BinaryGenerated.write_Fidelity_PSG_StorageWitnessProjection (BinaryIndexed.initialWrite BinaryTests.limits) original |> BinaryTests.take
    let fragment = BinaryIndexed.fragment plan |> BinaryTests.take
    let bytes = Array.zeroCreate (BinaryIndexed.size fragment)
    BinaryIndexed.writeFragment bytes 0 fragment
    let source = BAREWire.Memory.ByteSource.ofArray bytes
    let initial = BinaryIndexed.initialRead BinaryTests.limits source {Offset = 0UL; Length = uint64 bytes.Length}
    let copy, state = BinaryGenerated.read_Fidelity_PSG_StorageWitnessProjection initial |> BinaryTests.take
    Assert.Equal(original, copy)
    Assert.Equal(0, state.Depth)
    Assert.Equal(1, state.Current.Next)

[<Theory>]
[<InlineData("key")>]
[<InlineData("reservation")>]
let ``residence cannot be filed under a different allocation or invent reservation authority`` change =
    let original = pendingReservations
    let storage = original.Emission.Storage
    let residence : EnvironmentResidenceAccount =
        { Allocation = NodeId 1; Binding = NodeId 2; Owner = NodeId 1; Implementation = NodeId 1
          Formal = NodeId 1; ReservationClaim = NodeId 40; AuthorityInputs = []
          BindingPath = [NodeId 1]; LayoutClaims = []; DeclarationInputs = [] }
    let field, key, row =
        match change with
        | "key" -> "Allocation", NodeId 3, residence
        | "reservation" -> "ReservationClaim", residence.Allocation, {residence with ReservationClaim = NodeId 42}
        | other -> failwithf "Unknown mutation %s" other
    withStorage {storage with EnvironmentResidences = Map.ofList [key, row]} original
    |> hasViolation ("Emission.Storage.EnvironmentResidences." + field)

let private admittedResidence =
    // Contract-only account: each source-authorized row is stated explicitly.
    // The source/consumer suites own actual program compilation and execution.
    let nodes =
        factoryResults.Nodes
        |> Map.add (NodeId 2) (node 2 (SemanticKind.Binding("resident", false, false, None)) [])
        |> Map.add (NodeId 10) (node 10 (SemanticKind.Binding("alias", false, false, None)) [])
    let original = covered {factoryResults with Nodes = nodes}
    let moduleId, spaceId = NodeId 100, NodeId 902
    let space : BAREWire.Platform.MemorySpace =
        {Name = "program"; Kind = "ram"; Capacity = 4096L; Alignment = 8; Granularity = 8; Growth = "fixed"; Access = "rw"
         Base = None; Notes = ""; MapKind = ""; Since = ""; Until = ""}
    let identity = ProgramStorageIdentity.Allocation(NodeId 1)
    let entry : ProgramStorageEntry =
        {Identity = identity; SourceType = unitType; Shape = ProgramStorageShape.Bytes
         Bytes = 8; Alignment = 8; SpaceNode = spaceId; Space = space; Participants = Set.ofList [spaceId; NodeId 900]}
    let storageInventory : ProgramStorageInventory =
        {Entries = Map.ofList [identity, entry]
         Reservations = Map.ofList [spaceId, {Space = space; Requests = [|{Name = "allocation:1"; Length = 8L; Alignment = 8}|]; PayloadSize = 8L}]
         Unresolved = Map.empty}
    let reservationParticipants =
        [ participant ParticipantRole.EnvironmentAllocation 0 1 1
          participant ParticipantRole.EnvironmentBinding 0 1 2
          participant ParticipantRole.EnvironmentInitializer 0 1 4
          participant ParticipantRole.EnvironmentOwner 0 1 1
          participant ParticipantRole.EnvironmentImplementation 0 1 5
          participant ParticipantRole.EnvironmentConstructor 0 1 9
          participant ParticipantRole.EnvironmentFormal 0 1 6
          participant ParticipantRole.EnvironmentSpace 0 1 902
          participant ParticipantRole.EnvironmentAuthorityInput 0 1 900
          participant ParticipantRole.EnvironmentAuthorityInput 1 1 900
          participant ParticipantRole.EnvironmentDeclarationInput 0 1 901
          participant ParticipantRole.EnvironmentDeclarationInput 1 1 901
          participant ParticipantRole.EnvironmentCall 0 4 4
          participant ParticipantRole.EnvironmentFactory 0 4 5
          participant ParticipantRole.EnvironmentConstructor 0 4 9
          participant ParticipantRole.EnvironmentFormal 0 4 7
          participant ParticipantRole.EnvironmentAllocation 0 4 1
          participant ParticipantRole.EnvironmentDestination 0 4 3 ]
    let reservation : EnvironmentReservationAccount =
        {Claim = NodeId 40; Allocation = NodeId 1; Binding = NodeId 2; Initializer = NodeId 4; Participants = reservationParticipants}
    let residence : EnvironmentResidenceAccount =
        {Allocation = NodeId 1; Binding = NodeId 2; Owner = NodeId 1; Implementation = NodeId 5; Formal = NodeId 6
         ReservationClaim = reservation.Claim; AuthorityInputs = [NodeId 900; NodeId 900]; BindingPath = [NodeId 1; NodeId 4; NodeId 2]
         LayoutClaims = []; DeclarationInputs = [NodeId 901; NodeId 901]}
    let parameters = original.Emission.Callable.Calls[NodeId 4].Parameters
    // closure-representation §2.4: "The ordinary calling contract preserves
    // the arguments, result and environment convention"; each alternative
    // conforms to "the slot's one receiving contract or a source-settled adapter."
    // A settled residence therefore publishes a real receiving contract, not
    // the pending convention used by an unused carrier-only fixture.
    let contract : CallableContract =
        {Identity = NodeId 43; Kind = CallableKind.OrdinaryFlatClosure; Convention = CallableConvention.Ordinary
         ParameterTypes = [boolType; boolType]; OmittedParameters = []
         ParameterRepresentations = [0, ValueRepresentation.Scalar SettledSlot.Bool; 1, ValueRepresentation.Scalar SettledSlot.Bool]
         ResultType = original.Emission.Numeric.SourceTypes[NodeId 8]
         ResultRepresentation = ValueRepresentation.Scalar SettledSlot.Bool
         EnvironmentBytes = Some 8; SourcePremises = Map.empty
         Participants = [participant ParticipantRole.CallableContract 0 43 43
                         participant ParticipantRole.CallableImplementation 0 43 5
                         participant ParticipantRole.CalleeParameter 0 43 6
                         participant ParticipantRole.CalleeParameter 1 43 7
                         participant ParticipantRole.CalleeBody 0 43 8]}
    let carrier binding : CallableCarrier =
        {Occurrence = NodeId binding; Kind = CallableKind.OrdinaryFlatClosure; Formation = NodeId binding; EnvironmentValue = Some(NodeId binding)
         Contract = Ok contract.Identity; Lifetime = [participant ParticipantRole.CallableLifetime 0 binding 40]
         SourceType = unitType; Implementation = NodeId 5; Parameters = parameters
         ParameterShapes = [CallableValueShape.Data(NodeId 6); CallableValueShape.Data(NodeId 7)]; OmittedParameters = Set.empty
         Result = NodeId 8; ResultShape = CallableValueShape.Data(NodeId 8); Environment = Some {Owner = NodeId 1; Formal = NodeId 6}}
    let instance binding : CallableProgramInstance =
        {Carrier = carrier binding; Allocation = Some(NodeId 1); Participants = Set.ofList [NodeId binding; NodeId 2; NodeId 1]}
    let port : SourcePortAccount = {Extent = 0; Stamp = "module-declarations"; Positions = Map.empty}
    let startup : StartupWitness =
        {EntryBinding = NodeId 1; EntryLambda = NodeId 1; SourceBinding = NodeId 1; SourceLambda = NodeId 1
         OriginalBody = NodeId 1; Spine = NodeId 1; EntryCall = NodeId 1; Symbol = "main"
         Initializers = [{Module = moduleId; Binding = NodeId 2; Initializer = NodeId 4; Ordinal = 0}
                         {Module = moduleId; Binding = NodeId 10; Initializer = NodeId 2; Ordinal = 1}]
         ValueBindings = Set.ofList [NodeId 2; NodeId 10]}
    let order binding initializer ordinal claim : ProgramInitializationOrderAccount =
        {Binding = NodeId binding; Claim = NodeId claim
         Participants = [participant ParticipantRole.InitializationBinding 0 binding binding
                         participant ParticipantRole.InitializationEntry ordinal binding 1
                         participant ParticipantRole.InitializationSpine ordinal binding 1
                         participant ParticipantRole.InitializationValue ordinal binding initializer
                         participant ParticipantRole.InitializationPhase 0 binding 2
                         participant ParticipantRole.InitializationPhase 1 binding 10
                         participant ParticipantRole.InitializationPhase 2 binding 1
                         participant ParticipantRole.InitializationParent 0 binding 900]}
    let orders = [order 2 4 0 41; order 10 2 1 42]
    let reservationClaim =
        obligation "resident-space" "environment-storage-reservation"
            (ObligationBody.EnvironmentStorageReservation(Some 8, Some 8, Some 4096L, Some 8, Some 8))
    let claims =
        Map.ofList
            [ NodeId 40, reservationClaim
              NodeId 41, obligation "resident-order" "program-initialization-order" (ObligationBody.ProgramInitializationOrder(0, 2, [0; 1; 2]))
              NodeId 42, obligation "alias-order" "program-initialization-order" (ObligationBody.ProgramInitializationOrder(1, 2, [0; 1; 2])) ]
    let sources = (reservation.Claim, reservation.Participants) :: (orders |> List.map (fun row -> row.Claim, row.Participants))
    let layout : EnvironmentLayout =
        {Owner = NodeId 1; Implementation = NodeId 5; Formal = NodeId 6
         Slots = []; Bytes = 8; Alignment = 8; Obligations = []}
    let callable =
        {original.Emission.Callable with
            Contracts = Map.ofList [contract.Identity, contract]
            Carriers = Map.ofList [NodeId 2, carrier 2; NodeId 10, carrier 10]
            SignatureData = Map.ofList [NodeId 2, Set.ofList [NodeId 6; NodeId 7; NodeId 8]
                                        NodeId 10, Set.ofList [NodeId 6; NodeId 7; NodeId 8]]
            ProgramInstances = Map.ofList [NodeId 2, instance 2; NodeId 10, instance 10]}
    {original with
        Codata =
            {original.Codata with
                ProgramStorage = storageInventory
                CallableCarriers = callable.Carriers; CallableContracts = callable.Contracts
                EnvironmentLayouts = Map.ofList [NodeId 1, layout]}
        SourceReadings =
            {original.SourceReadings with
                Ports = original.SourceReadings.Ports.Add((moduleId, OccurrencePort.ModuleDeclaration), port)
                ContextHeaders = Map.ofList [moduleId, {Identity = moduleId; Name = "module"; Ports = Map.ofList [OccurrencePort.ModuleDeclaration, port]}]}
        CurrentClaims = claims; Obligations = claims |> Map.values |> Seq.toList
        ObligationSources = sources |> List.map (fun (claim, participants) -> claim, [participants |> List.map (fun (p: Participant) -> p.Node)]) |> Map.ofList
        Emission =
            {original.Emission with
                Callable = callable
                Storage =
                    {original.Emission.Storage with
                        ProgramStorage = storageInventory; Startup = Some startup
                        EnvironmentReservations = Map.ofList [reservation.Claim, reservation]
                        EnvironmentResidences = Map.ofList [residence.Allocation, residence]
                        ProgramInitializationOrders = orders |> List.map (fun row -> row.Binding, row) |> Map.ofList}}}

[<Fact>]
let ``canonical residence and its immutable alias retain one allocation without demanding premise bodies`` () =
    Assert.Empty(Integrity.check admittedResidence)
    let storage = admittedResidence.Emission.Storage
    Assert.Equal(1, storage.EnvironmentResidences.Count)
    Assert.Equal(2, admittedResidence.Emission.Callable.ProgramInstances.Count)
    Assert.Equal(NodeId 2, storage.EnvironmentResidences[NodeId 1].Binding)
    Assert.False(admittedResidence.Nodes.ContainsKey(NodeId 900))
    Assert.False(admittedResidence.Nodes.ContainsKey(NodeId 901))
    let bytes = Binary.encode BinaryTests.limits admittedResidence |> BinaryTests.take
    let copy = Binary.decode BinaryTests.limits bytes |> BinaryTests.take
    Assert.Equal(admittedResidence.Emission, copy.Emission)
    Assert.Equal(admittedResidence.Codata, copy.Codata)

[<Theory>]
[<InlineData("implementation")>]
[<InlineData("owner")>]
[<InlineData("formal")>]
[<InlineData("canonical-binding")>]
[<InlineData("allocation")>]
let ``sharing an allocation does not waive an alias exact carrier convention and canonical provenance`` change =
    let original = admittedResidence
    let callable = original.Emission.Callable
    let instance = callable.ProgramInstances[NodeId 10]
    let altered =
        match change with
        | "implementation" -> {instance with Carrier = {instance.Carrier with Implementation = NodeId 6}}
        | "owner" -> {instance with Carrier = {instance.Carrier with Environment = Some {Owner = NodeId 3; Formal = NodeId 6}}}
        | "formal" -> {instance with Carrier = {instance.Carrier with Environment = Some {Owner = NodeId 1; Formal = NodeId 7}}}
        | "canonical-binding" -> {instance with Participants = instance.Participants.Remove(NodeId 2)}
        | "allocation" -> {instance with Participants = instance.Participants.Remove(NodeId 1)}
        | other -> failwithf "Unknown mutation %s" other
    {original with Emission = {original.Emission with Callable = {callable with ProgramInstances = callable.ProgramInstances.Add(NodeId 10, altered)}}}
    |> hasViolation "Emission.Storage.EnvironmentResidences.Allocation"

[<Theory>]
[<InlineData("reservation")>]
[<InlineData("layout")>]
[<InlineData("authority")>]
[<InlineData("declaration")>]
[<InlineData("path")>]
[<InlineData("storage")>]
[<InlineData("initializer")>]
let ``admitted residence refuses changed complete source and storage correspondence`` change =
    let original = admittedResidence
    let storage = original.Emission.Storage
    let row = storage.EnvironmentResidences[NodeId 1]
    let update (residence: EnvironmentResidenceAccount) =
        withStorage {storage with EnvironmentResidences = Map.ofList [residence.Allocation, residence]} original
    let field, altered =
        match change with
        | "reservation" -> "ReservationClaim", update {row with ReservationClaim = NodeId 41}
        | "layout" -> "Owner", {original with Codata = {original.Codata with EnvironmentLayouts = original.Codata.EnvironmentLayouts.Add(row.Owner, {original.Codata.EnvironmentLayouts[row.Owner] with Alignment = 4})}}
        | "authority" -> "AuthorityInputs", update {row with AuthorityInputs = [NodeId 900]}
        | "declaration" -> "DeclarationInputs", update {row with DeclarationInputs = [NodeId 901]}
        | "path" -> "BindingPath", update {row with BindingPath = [NodeId 1; NodeId 2]}
        | "storage" -> "ReservationClaim", withStorage {storage with ProgramStorage = {storage.ProgramStorage with Entries = Map.empty}} original
        | "initializer" -> "Initializer", withStorage {storage with Startup = storage.Startup |> Option.map (fun startup -> {startup with Initializers = startup.Initializers |> List.map (fun initializer -> if initializer.Binding = NodeId 2 then {initializer with Initializer = NodeId 3} else initializer)})} original
        | other -> failwithf "Unknown mutation %s" other
    hasViolation ("Emission.Storage.EnvironmentResidences." + field) altered
