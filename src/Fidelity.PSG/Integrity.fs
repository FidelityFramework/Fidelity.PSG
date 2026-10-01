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

    /// The literals the storage, view and sentinel proofs of string literals name:
    /// the sources of every obligation node with one of those bodies.
    let private literalsWithProofs (revision: Revision) : NodeId list =
        revision.Nodes
        |> Map.toList
        |> List.filter (fun (_, node) ->
            match node.Kind with
            | SemanticKind.Obligation info ->
                match info.Body with
                | ObligationBody.StorageReservation _ | ObligationBody.ViewContainment _ | ObligationBody.NulSentinel _ -> true
                | _ -> false
            | _ -> false)
        |> List.collect (fun (id, _) -> revision.ObligationSources.TryFind id |> Option.toList |> List.concat |> List.concat)

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
        let branchCalls =
            held |> List.choose (fun (id, node) ->
                match node.Kind with SemanticKind.Application _ when node.IsReachable -> Some id | _ -> None)
            |> Set.ofList
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
          "Emission.Callable.Branches.CarrierUses", Set.toList callable.Branches.CarrierUses,
            "Emission.Callable.Carriers", rows callable.Carriers
          "Emission.Callable.Branches.FlowUses", Set.toList callable.Branches.FlowUses,
            "Emission.Callable.Flows", rows callable.Flows
          "Emission.Callable.Branches.CallUses", Set.toList callable.Branches.CallUses,
            "Nodes (reachable Application)", branchCalls
          // A shared nonempty inventory covers all current carrier/flow rows.
          "Emission.Callable.Carriers (branch authority)",
            (if callable.Branches.Observations.IsEmpty then [] else Set.toList (rows callable.Carriers)),
            "Emission.Callable.Branches.CarrierUses", callable.Branches.CarrierUses
          "Emission.Callable.Flows (branch authority)",
            (if callable.Branches.Observations.IsEmpty then [] else Set.toList (rows callable.Flows)),
            "Emission.Callable.Branches.FlowUses", callable.Branches.FlowUses
          "Nodes (reachable Application, branch authority)",
            (if callable.Branches.Observations.IsEmpty then [] else Set.toList branchCalls),
            "Emission.Callable.Branches.CallUses", callable.Branches.CallUses
          // CallUses refers to source applications, including un-emitted ones.
          // It must not be checked against the narrower emitted Calls table.
          // The lazy tables refer to one another.
          "Emission.Callable.Declarations (LazyThunk)", lazyDeclarations,
            "Emission.Storage.Lazies (Layout.Thunk)", thunks
          "Emission.Storage.LazyOccurrences (values)", storage.LazyOccurrences |> Map.toList |> List.map snd,
            "Emission.Storage.Lazies", rows storage.Lazies
          "Emission.Storage.LazyValues", Set.toList storage.LazyValues,
            "Emission.Storage.LazyOccurrences", rows storage.LazyOccurrences
          "Emission.Storage.DefinitionOnlyThunks", Set.toList storage.DefinitionOnlyThunks,
            "Emission.Storage.Lazies (Layout.Thunk)", thunks
          // Every literal that has proofs has its storage row.
          "ObligationSources (literal proofs)", literalsWithProofs revision, "LiteralStorage", rows revision.LiteralStorage ]

    let private disagreeing (left: Map<NodeId, 'row>) (right: Map<NodeId, 'row>) : NodeId list =
        Set.union (rows left) (rows right)
        |> Set.toList
        |> List.filter (fun key -> left.TryFind key <> right.TryFind key)

    let private differingMembers left right =
        Set.union (Set.difference left right) (Set.difference right left) |> Set.toList

    /// The tables that hold one fact in two places, with the identities whose rows
    /// differ. The callable emission tables and shared authority copy codata unchanged.
    let agreeing (revision: Revision) : (string * string * NodeId list) list =
        let codata = revision.Codata
        let callable = revision.Emission.Callable
        [ "Emission.Callable.Carriers", "Codata.CallableCarriers", disagreeing callable.Carriers codata.CallableCarriers
          "Emission.Callable.Joins", "Codata.CallableJoins", disagreeing callable.Joins codata.CallableJoins
          "Emission.Callable.Flows", "Codata.CallableFlows", disagreeing callable.Flows codata.CallableFlows
          "Emission.Callable.MutableStorage", "Codata.MutableCallableStorage",
            disagreeing callable.MutableStorage codata.MutableCallableStorage
          "Emission.Callable.Branches.Observations", "Codata.CallableBranches.Observations",
            disagreeing callable.Branches.Observations codata.CallableBranches.Observations
          "Emission.Callable.Branches.CarrierUses", "Codata.CallableBranches.CarrierUses",
            differingMembers callable.Branches.CarrierUses codata.CallableBranches.CarrierUses
          "Emission.Callable.Branches.FlowUses", "Codata.CallableBranches.FlowUses",
            differingMembers callable.Branches.FlowUses codata.CallableBranches.FlowUses
          "Emission.Callable.Branches.CallUses", "Codata.CallableBranches.CallUses",
            differingMembers callable.Branches.CallUses codata.CallableBranches.CallUses ]

    /// Cross-table authority and scope consistency only. This validates stored
    /// data, never the source truth of a guard or a constructor alternative.
    let private branchScopes (revision: Revision) : IntegrityViolation list =
        let authority = revision.Emission.Callable.Branches
        let failure part reason = { Part = part; Node = None; Reason = reason }
        let scope =
            if authority.Scope = revision.Codata.CallableBranches.Scope then []
            else [failure "Emission.Callable.Branches.Scope" "The branch authority scope differs from Codata.CallableBranches.Scope."]
        let empty =
            if not authority.Observations.IsEmpty ||
               (authority.CarrierUses.IsEmpty && authority.FlowUses.IsEmpty && authority.CallUses.IsEmpty) then []
            else [failure "Emission.Callable.Branches" "An empty observation inventory has nonempty authority-use sets."]
        let partition =
            if authority.Observations.IsEmpty then [] else
            match authority.Scope, revision.Codata.WitnessSegmentation with
            | CallableBranchScope.WholeRevision, Some segmentation
                when segmentation.Regions |> List.exists (fun region -> region.Flavor = WitnessRegionKind.ScalarCallable) ->
                [failure "Codata.WitnessSegmentation" "Whole-revision callable branch authority cannot coexist with a scalar callable region."]
            | _ -> []
        scope @ empty @ partition

    /// The storage rows against the static string pool. A row that states
    /// materialization names an entry the pool has, and that entry lists the row's
    /// literal. A row that states no materialization states an established premise
    /// with its omissions. Every literal an entry lists has a row that names the entry.
    let stored (revision: Revision) : IntegrityViolation list =
        let entries = revision.StaticStringPool |> Option.map _.Entries |> Option.defaultValue []
        let violation part literal reason = { Part = part; Node = Some literal; Reason = reason }
        let named =
            revision.LiteralStorage
            |> Map.toList
            |> List.choose (fun (literal, row) ->
                match row with
                | LiteralStorage.Materialized entry when entry < 0 || entry >= entries.Length ->
                    Some (violation "LiteralStorage" literal
                            (sprintf "The storage row of node %d names pool entry %d. The pool has %d entries." (NodeId.value literal) entry entries.Length))
                | LiteralStorage.Materialized entry when not (List.contains literal entries[entry].NodeIds) ->
                    Some (violation "LiteralStorage" literal
                            (sprintf "The storage row of node %d names pool entry %d, which does not list the node." (NodeId.value literal) entry))
                | LiteralStorage.NotMaterialized (StoragePremise.Established []) ->
                    Some (violation "LiteralStorage" literal
                            (sprintf "The storage row of node %d states neither a pool entry nor an omission." (NodeId.value literal)))
                | LiteralStorage.NotMaterialized (StoragePremise.Pending _) ->
                    Some (violation "LiteralStorage" literal
                            (sprintf "The storage row of node %d states its omission premise as pending." (NodeId.value literal)))
                | _ -> None)
        let listed =
            entries
            |> List.indexed
            |> List.collect (fun (ordinal, entry) ->
                entry.NodeIds |> List.distinct |> List.choose (fun literal ->
                    match revision.LiteralStorage.TryFind literal with
                    | Some (LiteralStorage.Materialized entry) when entry = ordinal -> None
                    | _ ->
                        Some (violation "StaticStringPool.Entries" literal
                                (sprintf "Pool entry %d lists node %d, whose storage row does not name the entry." ordinal (NodeId.value literal)))))
        named @ listed

    /// The string byte view and string extent rows against their participants. A row
    /// states established participants, one of which names the row's site in the role
    /// Site, and the sources of its edge are the nodes of its participants in order. An
    /// omitted actual is in the group of an omission site with the same ordinal, and an
    /// omission site with one ordinal has exactly one omitted actual. A callee's body is in
    /// the group of a callee; a callee's arguments and parameters are in the group of a call
    /// in whose group a callee occurs, with exactly one argument and exactly one parameter at
    /// each of its ordinals.
    let incidence (revision: Revision) : IntegrityViolation list =
        let violation part site reason = { Part = part; Node = Some site; Reason = reason }
        let paired part site (participants: Participant list) =
            let sites =
                participants
                |> List.filter (fun participant -> participant.Role = ParticipantRole.OmissionSite)
                |> List.map (fun participant -> participant.Node, participant.Ordinal)
                |> List.distinct
            let actuals = participants |> List.filter (fun participant -> participant.Role = ParticipantRole.OmittedActual)
            let unplaced =
                actuals
                |> List.filter (fun actual -> not (List.contains (actual.Group, actual.Ordinal) sites))
                |> List.map (fun actual ->
                    violation part site
                        (sprintf "The omitted actual %d of the string borrow row of node %d is not in the group of an omission site at ordinal %d."
                            (NodeId.value actual.Node) (NodeId.value site) actual.Ordinal))
            let counted =
                sites
                |> List.map (fun (omission, ordinal) ->
                    omission, ordinal, actuals |> List.filter (fun actual -> actual.Group = omission && actual.Ordinal = ordinal) |> List.length)
                |> List.filter (fun (_, _, count) -> count <> 1)
                |> List.map (fun (omission, ordinal, count) ->
                    violation part site
                        (sprintf "The omission site %d at ordinal %d of the string borrow row of node %d has %d omitted actuals, not one."
                            (NodeId.value omission) ordinal (NodeId.value site) count))
            unplaced @ counted
        let owned part site (participants: Participant list) =
            let callees = participants |> List.filter (fun participant -> participant.Role = ParticipantRole.Callee)
            let lambdas = callees |> List.map _.Node |> Set.ofList
            let calls = callees |> List.map _.Group |> Set.ofList
            let placed =
                participants
                |> List.choose (fun participant ->
                    match participant.Role with
                    | ParticipantRole.CalleeBody when not (lambdas.Contains participant.Group) ->
                        Some (violation part site
                                (sprintf "The callee body %d of the string borrow row of node %d is not in the group of a callee."
                                    (NodeId.value participant.Node) (NodeId.value site)))
                    | ParticipantRole.CalleeArgument | ParticipantRole.CalleeParameter when not (calls.Contains participant.Group) ->
                        Some (violation part site
                                (sprintf "The callee argument or parameter %d of the string borrow row of node %d is not in the group of a call in whose group a callee occurs."
                                    (NodeId.value participant.Node) (NodeId.value site)))
                    | _ -> None)
            // The number of occurrences of a role at each ordinal in the group of a call.
            let counts role call =
                participants |> List.filter (fun participant -> participant.Role = role && participant.Group = call) |> List.countBy _.Ordinal |> Map.ofList
            let unmatched =
                calls
                |> Set.toList
                |> List.collect (fun call ->
                    let arguments, parameters = counts ParticipantRole.CalleeArgument call, counts ParticipantRole.CalleeParameter call
                    Set.union (arguments |> Map.keys |> Set.ofSeq) (parameters |> Map.keys |> Set.ofSeq)
                    |> Set.toList
                    |> List.choose (fun ordinal ->
                        match arguments.TryFind ordinal |> Option.defaultValue 0, parameters.TryFind ordinal |> Option.defaultValue 0 with
                        | 1, 1 -> None
                        | argumentCount, parameterCount ->
                            Some (violation part site
                                    (sprintf "The group of call %d of the string borrow row of node %d has %d callee arguments and %d callee parameters at ordinal %d, not one of each."
                                        (NodeId.value call) (NodeId.value site) argumentCount parameterCount ordinal))))
            placed @ unmatched
        let stated part site evidence =
            match evidence with
            | ParticipantEvidence.Pending _ ->
                [ violation part site (sprintf "The string borrow row of node %d states its participants as pending." (NodeId.value site)) ]
            | ParticipantEvidence.Established participants
                when not (participants |> List.exists (fun participant -> participant.Role = ParticipantRole.Site && participant.Node = site)) ->
                violation part site (sprintf "The participants of the string borrow row of node %d do not name the node in the role Site." (NodeId.value site))
                :: (paired part site participants @ owned part site participants)
            | ParticipantEvidence.Established participants -> paired part site participants @ owned part site participants
        // A pending row has no participant list to compare; `stated` reports it.
        let ordered part site (sources: NodeId list) evidence =
            match evidence with
            | ParticipantEvidence.Established participants when sources <> (participants |> List.map _.Node) ->
                [ violation part site (sprintf "The sources of the string borrow edge at node %d are not the nodes of its participants in order." (NodeId.value site)) ]
            | _ -> []
        let edges =
            revision.Edges
            |> List.collect (fun edge ->
                match edge.Role with
                | EdgeRole.StringByteView view ->
                    stated "Edges (StringByteView)" view.Site view.Participants @ ordered "Edges (StringByteView)" view.Site edge.Sources view.Participants
                | EdgeRole.StringExtent extent ->
                    stated "Edges (StringExtent)" extent.Site extent.Participants @ ordered "Edges (StringExtent)" extent.Site edge.Sources extent.Participants
                | _ -> [])
        let boundary = revision.Emission.Boundary
        let views =
            boundary.ByteViews |> Map.toList |> List.collect (fun (_, view) -> stated "Emission.Boundary.ByteViews" view.Site view.Participants)
        let extents =
            boundary.StringExtents |> Map.toList |> List.collect (fun (_, extent) -> stated "Emission.Boundary.StringExtents" extent.Site extent.Participants)
        edges @ views @ extents

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
        header @ misfiled @ absent @ unrelated @ disagreed @ branchScopes revision @ stored revision @ incidence revision

    /// The first violations as one reason, for a reader that refuses the revision.
    let describe (violations: IntegrityViolation list) : string =
        let shown =
            violations
            |> List.truncate 8
            |> List.map (fun violation -> sprintf "%s: %s" violation.Part violation.Reason)
        let more =
            if violations.Length > shown.Length then [ sprintf "and %d more" (violations.Length - shown.Length) ] else []
        "The revision is not well formed.\n" + String.concat "\n" (shown @ more)
