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
