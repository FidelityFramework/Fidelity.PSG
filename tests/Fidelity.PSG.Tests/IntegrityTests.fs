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
    let premise = { Literal = NodeId 5; Early = [ { Site = NodeId 6; Ordinal = 0; Actual = NodeId 8 } ] }
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
        { Occurrence = one; SourceType = boolType; Implementation = two; Parameters = []
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
          Fingerprint = "stored-data"; Dependencies = Set.empty }
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
          OwnerSupport = SupportKey.WholeOwningAnalysisRegion "current-source-owner"; Fingerprint = "settled-rows"; Dependencies = Set.empty }
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
        { Occurrence = NodeId 2; SourceType = boolType; Implementation = NodeId 70
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
         MinimumCount = 1I; MaximumCount = 4I; Requirement = requirement; Participants = Set.ofList [NodeId 5; NodeId 64; NodeId 5521; NodeId 8000]}
    let copy : MemoryArrayCopyWitness =
        {Site = NodeId 6; Source = NodeId 1; SourceOffset = NodeId 3; Destination = NodeId 11; DestinationOffset = NodeId 4
         Count = NodeId 5; CountCarrier = numeric.Values[NodeId 5]; Allocation = Some(NodeId 11); Loop = None
         Read = None; Write = None; Requirements = [requirement]; Participants = Set.ofList [NodeId 64; NodeId 404; NodeId 8000]}
    let view : MemoryStringViewWitness =
        {Site = NodeId 1; Source = NodeId 3; Owner = NodeId 8000; Snapshot = NodeId 6; Direction = MemoryStringViewDirection.ToBytes
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
        {Site = NodeId 1; Import = NodeId 72; Callee = NodeId 2
         Arguments = [3;4] |> List.map(fun id -> {Actual = NodeId id; Formal = NodeId id; Abi = BoundaryScalar.Integer(32, true); Adaptation = None})
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
