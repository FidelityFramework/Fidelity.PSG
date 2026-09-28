module Fidelity.PSG.Tests.IntegrityTests

open Xunit
open Fidelity.PSG
open Fidelity.PSG.Tests.Build

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
let ``a parent that is not held is reported`` () =
    let orphaned = { bindingWithLiteral with Nodes = bindingWithLiteral.Nodes.Remove(NodeId 1) }
    let violation = within "Nodes.Parent" (Integrity.check orphaned)
    Assert.Equal(Some (NodeId 1), violation.Node)

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
let ``an obligation source that is not held is reported`` () =
    let sources = Map.ofList [ NodeId 1, [ [ NodeId 2; NodeId 8 ] ] ]
    let violation = only "ObligationSources (values)" (Integrity.check { bindingWithLiteral with ObligationSources = sources })
    Assert.Equal(Some (NodeId 8), violation.Node)

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
    { bindingWithLiteral with Emission = { bindingWithLiteral.Emission with Storage = storage } }

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
let ``a node that is not reachable needs no numeric row`` () =
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
    Assert.Empty(Integrity.check stated)

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

// A string literal (node 3) and its storage proof (node 4). Node 5 is a call whose
// ordinal 0 is omitted and node 6 the declaration of the pool's space.
let private storageProof : ObligationInfo =
    { Id = "storage_text"; Kind = "storage-reservation"; Logic = "QF_LIA"
      Statement = "the storage of \"text\" reserves 5 bytes"; Source = "contract-test.clef:1:0"; Refs = []
      Body = ObligationBody.StorageReservation(4, 5) }

let private literalWithProof : Revision =
    let literal = node 3 (SemanticKind.Literal(NativeLiteral.String "text")) []
    let proof = node 4 (SemanticKind.Obligation storageProof) []
    let call = node 5 (SemanticKind.Literal(NativeLiteral.Bool true)) []
    let space = node 6 (SemanticKind.Literal(NativeLiteral.Bool false)) []
    { revision [ literal; proof; call; space ] with ObligationSources = Map.ofList [ NodeId 4, [ [ NodeId 3 ] ] ] }

let private pool (listed: int) : StaticStringPool =
    { Symbol = "__clef_static_strings"; Bytes = [ 116uy; 101uy; 120uy; 116uy; 0uy ]; Alignment = 1; Size = 5; UsedSize = 5
      Entries = [ { NodeIds = [ NodeId listed ]; Content = "text"; Offset = 0; Length = 4; StorageLength = 5 } ]
      SpaceName = "rodata"; Capacity = 4096L; SpaceAlignment = 1; Granularity = 1; DeclarationNode = NodeId 6 }

let private omission : OrdinaryOmission = { Site = NodeId 5; Ordinal = 0; Actual = NodeId 3 }

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
let ``a participant that names a node absent from the revision is reported`` () =
    let foreign = borrowed @ [ participant 11 ParticipantRole.Path 0 7 ]
    let violations = Integrity.check (withEdges [ viewEdge (ParticipantEvidence.Established foreign) (nodesOf foreign) ])
    let violation = within "Edges.Role" violations
    Assert.Equal(Some (NodeId 11), violation.Node)
    Assert.DoesNotContain(violations, fun other -> other.Part = "Edges (StringByteView)")

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
    let premise = { Literal = NodeId 5; Early = [ { Site = NodeId 6; Ordinal = 0; Actual = NodeId 8 } ] }
    let literalHistory : Hyperedge =
        { Sources = [ NodeId 6; NodeId 8 ]; Target = NodeId 5; Class = EdgeClass.Provenance; Role = EdgeRole.LiteralStorageHistory premise; Ordinal = 0 }
    Assert.Empty(Integrity.check (withEdges [ viewEdge (ParticipantEvidence.Established borrowed) (nodesOf borrowed); historyEdge early; literalHistory ]))
