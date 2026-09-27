namespace Fidelity.PSG

/// One structural defect of a revision.
type IntegrityViolation = {
    /// The part of the revision that holds the defect.
    Part: string
    /// The identity concerned, where the defect concerns one.
    Node: NodeId option
    Reason: string
}

/// The structural rules of a revision. They concern the revision as data: every
/// identity it names is a node it holds, every row that refers to another table
/// finds its row there, two tables that hold the same fact hold the same rows, and
/// its header names this contract. They state nothing about the program. A reader that receives a revision from another
/// process applies them before it reads anything else.
module Integrity =

    let private rows (table: Map<NodeId, 'value>) : Set<NodeId> =
        table |> Map.toList |> List.map fst |> Set.ofList

    /// Every part of a revision that names nodes, with the identities it names. The
    /// list is generated from the contract types (tools/GenerateIntegrity.fsx) and
    /// holds every position of a revision where an identity is stored.
    let named (revision: Revision) : (string * NodeId list) list =
        IntegrityNamed.named revision

    /// Every reference from one part of a revision to the rows of a table: the part
    /// that refers, the identities it names, the table referred to and the rows that
    /// table holds. The compiler service builds each table below for the identities
    /// named, so a published revision satisfies every one of them.
    let related (revision: Revision) : (string * NodeId list * string * Set<NodeId>) list =
        let held = revision.Nodes |> Map.toList
        let every = held |> List.map fst
        let reachable = held |> List.filter (fun (_, node) -> node.IsReachable) |> List.map fst
        let callable = revision.Emission.Callable
        let storage = revision.Emission.Storage
        let numeric = revision.Emission.Numeric
        let memory = revision.Emission.Memory
        let spatial = revision.Emission.Spatial
        let thunks =
            storage.Lazies |> Map.toList |> List.map (fun (_, contract) -> contract.Layout.Thunk) |> Set.ofList
        let lazyDeclarations =
            callable.Declarations
            |> Map.toList
            |> List.filter (fun (_, declaration) -> declaration.Context = LambdaContext.LazyThunk)
            |> List.map (fun (_, declaration) -> declaration.Implementation)
        [ // A row for every node held.
          "Nodes", every, "Emission.Callable.ValueShapes", rows callable.ValueShapes
          "Nodes", every, "Emission.Callable.AliasTargets", rows callable.AliasTargets
          "Nodes", every, "Emission.Callable.Supports", rows callable.Supports
          // A row for every reachable node.
          "Nodes (reachable)", reachable, "Emission.Numeric.SourceTypes", rows numeric.SourceTypes
          "Nodes (reachable)", reachable, "Emission.Numeric.OccurrenceRepresentations", rows numeric.OccurrenceRepresentations
          // A row for every site a projection declares as required.
          "Emission.Numeric.Required", Set.toList numeric.Required,
            "Emission.Numeric.Values or Emission.Numeric.Unresolved", Set.union (rows numeric.Values) (rows numeric.Unresolved)
          "Emission.Numeric.OperationRequired", Set.toList numeric.OperationRequired,
            "Emission.Numeric.Operations", rows numeric.Operations
          "Emission.Numeric.ResultSites", Set.toList numeric.ResultSites,
            "Emission.Numeric.Values", rows numeric.Values
          "Emission.Memory.Required", Set.toList memory.Required,
            "Emission.Memory.Operations or Emission.Memory.Unresolved", Set.union (rows memory.Operations) (rows memory.Unresolved)
          "Emission.Spatial.Required", Set.toList spatial.Required,
            "Emission.Spatial.Hardware or Emission.Spatial.Kernels", Set.union (rows spatial.Hardware) (rows spatial.Kernels)
          // The lazy tables refer to one another.
          "Emission.Callable.Declarations (LazyThunk)", lazyDeclarations,
            "Emission.Storage.Lazies (Layout.Thunk)", thunks
          "Emission.Storage.LazyOccurrences (values)", storage.LazyOccurrences |> Map.toList |> List.map snd,
            "Emission.Storage.Lazies", rows storage.Lazies
          "Emission.Storage.LazyValues", Set.toList storage.LazyValues,
            "Emission.Storage.LazyOccurrences", rows storage.LazyOccurrences
          "Emission.Storage.DefinitionOnlyThunks", Set.toList storage.DefinitionOnlyThunks,
            "Emission.Storage.Lazies (Layout.Thunk)", thunks ]

    let private disagreeing (left: Map<NodeId, 'row>) (right: Map<NodeId, 'row>) : NodeId list =
        Set.union (rows left) (rows right)
        |> Set.toList
        |> List.filter (fun key -> left.TryFind key <> right.TryFind key)

    /// The tables that hold one fact in two places, with the identities whose rows
    /// differ. The emission projection republishes four codata tables unchanged.
    let agreeing (revision: Revision) : (string * string * NodeId list) list =
        let codata = revision.Codata
        let callable = revision.Emission.Callable
        [ "Emission.Callable.Carriers", "Codata.CallableCarriers", disagreeing callable.Carriers codata.CallableCarriers
          "Emission.Callable.Joins", "Codata.CallableJoins", disagreeing callable.Joins codata.CallableJoins
          "Emission.Callable.Flows", "Codata.CallableFlows", disagreeing callable.Flows codata.CallableFlows
          "Emission.Callable.MutableStorage", "Codata.MutableCallableStorage",
            disagreeing callable.MutableStorage codata.MutableCallableStorage ]

    /// Every structural defect of the revision. The list is empty for a well-formed one.
    let check (revision: Revision) : IntegrityViolation list =
        let header =
            if revision.Header.Schema = Revision.Schema then []
            else
                [ { Part = "Header"; Node = None
                    Reason = sprintf "The revision conforms to contract version %d. This reader holds version %d." revision.Header.Schema Revision.Schema } ]
        let misfiled =
            revision.Nodes
            |> Map.toList
            |> List.filter (fun (key, node) -> node.Id <> key)
            |> List.map (fun (key, node) ->
                { Part = "Nodes"; Node = Some key
                  Reason = sprintf "The node filed under %d identifies itself as %d." (NodeId.value key) (NodeId.value node.Id) })
        let absent =
            named revision
            |> List.collect (fun (part, identities) ->
                identities
                |> List.distinct
                |> List.filter (fun identity -> not (revision.Nodes.ContainsKey identity))
                |> List.map (fun identity ->
                    { Part = part; Node = Some identity
                      Reason = sprintf "Node %d is named and is not held by the revision." (NodeId.value identity) }))
        let unrelated =
            related revision
            |> List.collect (fun (part, identities, table, held) ->
                identities
                |> List.distinct
                |> List.filter (fun identity -> not (held.Contains identity))
                |> List.map (fun identity ->
                    { Part = part; Node = Some identity
                      Reason = sprintf "Node %d is named by %s and has no row in %s." (NodeId.value identity) part table }))
        let disagreed =
            agreeing revision
            |> List.collect (fun (part, other, identities) ->
                identities
                |> List.map (fun identity ->
                    { Part = part; Node = Some identity
                      Reason = sprintf "The row of node %d in %s differs from its row in %s." (NodeId.value identity) part other }))
        header @ misfiled @ absent @ unrelated @ disagreed

    /// The first violations as one reason, for a reader that refuses the revision.
    let describe (violations: IntegrityViolation list) : string =
        let shown =
            violations
            |> List.truncate 8
            |> List.map (fun violation -> sprintf "%s: %s" violation.Part violation.Reason)
        let more =
            if violations.Length > shown.Length then [ sprintf "and %d more" (violations.Length - shown.Length) ] else []
        "The revision is not well formed.\n" + String.concat "\n" (shown @ more)
