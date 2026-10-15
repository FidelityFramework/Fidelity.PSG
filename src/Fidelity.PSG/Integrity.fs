namespace Fidelity.PSG

/// One structural defect of a revision.
type IntegrityViolation = {
    /// The part of the revision that holds the defect.
    Part: string
    /// The identity concerned, where the defect concerns one.
    Node: NodeId option
    Reason: string
}

/// The structural rules of a revision. They concern the revision as data: each
/// executable reference has its live body, each typed reference has its owning row,
/// every row that refers to another table
/// finds its row there, two tables that hold the same fact hold the same rows, and
/// its header names this contract. They state nothing about the program. A reader that receives a revision from another
/// process applies them before it reads anything else.
module Integrity =

    let private rows (table: Map<NodeId, 'value>) : Set<NodeId> =
        table |> Map.toList |> List.map fst |> Set.ofList

    /// The literals the storage, view and sentinel proofs of string literals name:
    /// the sources of every current claim with one of those bodies. Claim facts
    /// have no executable SemanticNode body in a live publication.
    let private literalsWithProofs (revision: Revision) : NodeId list =
        revision.CurrentClaims
        |> Map.toList
        |> List.filter (fun (_, info) ->
            match info.Body with
            | ObligationBody.StorageReservation _ | ObligationBody.ViewContainment _ | ObligationBody.NulSentinel _ -> true
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
        let spatial = revision.Emission.Spatial
        let hardwareDeclarations =
            held |> List.choose (fun (id, node) ->
                match node.Kind with SemanticKind.Binding(_, _, _, Some DeclRoot.HardwareModule) -> Some id | _ -> None)
        let kernelDeclarations =
            held |> List.choose (fun (id, node) ->
                match node.Kind with SemanticKind.Binding(_, _, _, Some DeclRoot.KernelModule) -> Some id | _ -> None)
        let hardwareSites = spatial.Hardware |> Map.filter (fun id row -> row.Site = id) |> rows
        let kernelSites = spatial.Kernels |> Map.filter (fun id row -> row.Site = id) |> rows
        let specializedDeclaration id (node: SemanticNode) =
            match node.Kind with
            | SemanticKind.Binding(_, _, _, Some DeclRoot.HardwareModule) -> hardwareSites.Contains id
            | SemanticKind.Binding(_, _, _, Some DeclRoot.KernelModule) -> kernelSites.Contains id
            | _ -> false
        let values = held |> List.filter (fun (id, node) -> not (specializedDeclaration id node))
        let every = values |> List.map fst
        let reachable = values |> List.filter (fun (_, node) -> node.IsReachable) |> List.map fst
        let callable = revision.Emission.Callable
        let branchCalls =
            held |> List.choose (fun (id, node) ->
                match node.Kind with SemanticKind.Application _ when node.IsReachable -> Some id | _ -> None)
            |> Set.ofList
        let storage = revision.Emission.Storage
        let numeric = revision.Emission.Numeric
        let memory = revision.Emission.Memory
        let thunks =
            storage.Lazies |> Map.toList |> List.map (fun (_, contract) -> contract.Layout.Thunk) |> Set.ofList
        let lazyDeclarations =
            callable.Declarations
            |> Map.toList
            |> List.filter (fun (_, declaration) -> declaration.Context = LambdaContext.LazyThunk)
            |> List.map (fun (_, declaration) -> declaration.Implementation)
        [ // Ordinary value readings exclude only exact specialized declaration
          // shells. Their matching spatial plan remains mandatory and is
          // validated independently; it grants no operand or signature facts.
          "Nodes", every, "Emission.Callable.ValueShapes", rows callable.ValueShapes
          "Nodes", every, "Emission.Callable.AliasTargets", rows callable.AliasTargets
          "Nodes", every, "Emission.Callable.Supports", rows callable.Supports
          // A row for every reachable node.
          "Nodes (reachable)", reachable, "Emission.Numeric.SourceTypes", rows numeric.SourceTypes
          "Nodes (reachable)", reachable, "Emission.Numeric.OccurrenceRepresentations", rows numeric.OccurrenceRepresentations
          "Nodes (HardwareModule declaration)", hardwareDeclarations, "Emission.Spatial.Hardware (matching Site)", hardwareSites
          "Nodes (KernelModule declaration)", kernelDeclarations, "Emission.Spatial.Kernels (matching Site)", kernelSites
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
          "Emission.Callable.Contracts", "Codata.CallableContracts", disagreeing callable.Contracts codata.CallableContracts
          "Emission.Callable.AggregateSlots", "Codata.CallableAggregateSlots", disagreeing callable.AggregateSlots codata.CallableAggregateSlots
          "Emission.Callable.AggregateValues", "Codata.CallableAggregateValues", disagreeing callable.AggregateValues codata.CallableAggregateValues
          "Emission.Callable.AggregateDependencies", "Codata.CallableAggregateDependencies", disagreeing callable.AggregateDependencies codata.CallableAggregateDependencies
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
        let pairedRoles siteRole actualRole part site (participants: Participant list) =
            let sites =
                participants
                |> List.filter (fun participant -> participant.Role = siteRole)
                |> List.map (fun participant -> participant.Node, participant.Ordinal)
                |> List.distinct
            let actuals = participants |> List.filter (fun participant -> participant.Role = actualRole)
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
        let paired part site (participants: Participant list) =
            let initializerPositions = participants |> List.choose (fun participant ->
                match participant.Role with
                | ParticipantRole.OmissionBinding | ParticipantRole.OmittedInitializer when participant.Ordinal <> 0 ->
                    Some (violation part site "An initializer omission participant has a position although its role is non-positional.")
                | _ -> None)
            pairedRoles ParticipantRole.OmissionSite ParticipantRole.OmittedActual part site participants
            @ pairedRoles ParticipantRole.OmissionBinding ParticipantRole.OmittedInitializer part site participants
            @ initializerPositions
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

    let private defect part node reason = { Part = part; Node = Some node; Reason = reason }

    let private missingBody part node =
        defect part node (sprintf "Node %d is named and is not held by the revision." (NodeId.value node))

    let private missingRow part table node =
        defect part node (sprintf "Node %d is named by %s and has no row in %s." (NodeId.value node) part table)

    /// Compare the producer's stored traversal, rather than interpreting an
    /// unentered child or an ancestor handle as a request for its body.
    let private sourceReadings (revision: Revision) =
        let source = revision.SourceReadings
        let body node = revision.Nodes.ContainsKey node
        let header node = source.ContextHeaders.ContainsKey node
        let need part table node present =
            if present then [] else [missingRow part table node]
        let port parent kind = source.Ports.TryFind(parent, kind)
        let checkContext part focus (path: OccurrenceBreadcrumb list) =
            match RevisionNavigation.checkContext revision focus path with
            | Ok _ -> []
            | Error reason -> [defect part focus reason]
        [ for KeyValue(key, node) in revision.Nodes do
              if not node.IsReachable then yield defect "Nodes" key "An inactive source body is present in the live revision."
              match node.Kind with
              | SemanticKind.Obligation _ -> yield defect "Nodes" key "A claim belongs in CurrentClaims, not in an executable body row."
              | SemanticKind.TypeDef _ -> yield defect "Nodes" key "A type declaration belongs in settled declaration and layout facts, not in an executable body row."
              | _ -> ()
              match source.Children.TryFind key with
              | None -> yield missingRow "Nodes" "SourceReadings.Children" key
              | Some children ->
                  if children.Length <> node.Children.Length then
                      yield defect "SourceReadings.Children" key "The child disposition count differs from the original body child count."
                  for ordinal, child in List.indexed children do
                      let identity =
                          match child.Traversal with
                          | ChildTraversal.EnterLocal identity | ChildTraversal.EnterImported(_, _, identity)
                          | ChildTraversal.SourceOmitted(_, identity) -> identity
                      if child.Ordinal <> ordinal || (node.Children |> List.tryItem ordinal) <> Some identity then
                          yield defect "SourceReadings.Children" key "A child disposition differs from its original identity or ordinal."
                      match child.Traversal with
                      | ChildTraversal.EnterLocal identity when not (body identity) -> yield missingBody "Nodes.Children" identity
                      | ChildTraversal.EnterImported(scope, boundary, _) ->
                          if System.String.IsNullOrWhiteSpace scope.Identity || System.String.IsNullOrWhiteSpace boundary.Identity then
                              yield defect "SourceReadings.Children" key "An imported child has an empty scope or boundary identity."
                      | ChildTraversal.SourceOmitted(support, _) ->
                          match support with
                          | SupportKey.Rule identity | SupportKey.Declaration identity | SupportKey.CollectionMembership identity
                          | SupportKey.Absence identity | SupportKey.WholeOwningAnalysisRegion identity when System.String.IsNullOrWhiteSpace identity ->
                              yield defect "SourceReadings.Children" key "An omitted child has an empty source support identity."
                          | _ -> ()
                      | _ -> ()
              match source.Contexts.TryFind key with
              | Some contexts when not contexts.IsEmpty -> for path in contexts do yield! checkContext "SourceReadings.Contexts" key path
              | _ -> yield missingRow "Nodes" "SourceReadings.Contexts (nonempty occurrence account)" key
          for KeyValue(key, _) in source.Children do yield! need "SourceReadings.Children" "Nodes" key (body key)
          for KeyValue(key, paths) in source.Contexts do
              yield! need "SourceReadings.Contexts" "live body or SourceReadings.ContextHeaders" key (body key || header key)
              if header key && not (body key) then for path in paths do yield! checkContext "SourceReadings.Contexts" key path
          for KeyValue(key, context) in source.ContextHeaders do
              if key <> context.Identity then yield defect "SourceReadings.ContextHeaders.Identity" key "A context header is filed under a different identity."
              for KeyValue(kind, account) in context.Ports do
                  if port key kind <> Some account then yield defect "SourceReadings.ContextHeaders.Ports" key "A context header differs from its source port row."
          for KeyValue((parent, kind), account) in source.Ports do
              yield! need "SourceReadings.Ports" "live body or SourceReadings.ContextHeaders" parent (body parent || header parent)
              if kind = OccurrencePort.ModuleDeclaration then
                  yield! need "SourceReadings.Ports" "SourceReadings.ContextHeaders (module declaration port)" parent
                      (source.ContextHeaders.TryFind parent |> Option.exists (fun row -> row.Identity = parent && row.Ports.TryFind kind = Some account))
              if account.Extent < 0 || System.String.IsNullOrWhiteSpace account.Stamp then yield defect "SourceReadings.Ports" parent "A source port has an invalid extent or an empty stamp."
              for KeyValue(ordinal, child) in account.Positions do
                  if ordinal < 0 || ordinal >= account.Extent then yield defect "SourceReadings.Ports.Positions" parent "A sparse source port position is outside its original extent."
                  yield! need "SourceReadings.Ports.Positions" "live occurrence or SourceReadings.ContextHeaders" child (body child || header child)
          for entry in source.Entries do
              let present = match entry.Reason with SourceEntryReason.BoundaryScope -> body entry.Focus || header entry.Focus | _ -> body entry.Focus
              yield! need "SourceReadings.Entries.Focus" "the entry's live body or boundary context header" entry.Focus present
              if body entry.Focus && not (source.Contexts.TryFind entry.Focus |> Option.exists (List.contains entry.Context)) then
                  yield defect "SourceReadings.Entries.Context" entry.Focus "The entry occurrence is absent from its stored context account."
              yield! checkContext "SourceReadings.Entries.Context" entry.Focus entry.Context
          for KeyValue(site, bindingUse) in source.BindingUses do
              match revision.Nodes.TryFind site with
              | Some { Kind = SemanticKind.VarRef(_, Some binding) } when binding = bindingUse.Binding && not (System.String.IsNullOrWhiteSpace bindingUse.Name) -> ()
              | _ -> yield defect "SourceReadings.BindingUses" site "A resolved use contract differs from its live reference occurrence."
              if bindingUse.HasProgramSlotAuthority && not (revision.Emission.Storage.SlotAuthorities.Contains bindingUse.Binding) then
                  yield missingRow "SourceReadings.BindingUses.Binding" "Emission.Storage.SlotAuthorities" bindingUse.Binding ]

    /// Current claims and their grouped source account are compared as facts.
    /// Source identities in that account are proof premises, not body lookups.
    let private claims (revision: Revision) =
        let claims = rows revision.CurrentClaims
        let groups = rows revision.ObligationSources
        let missing =
            [ for id in Set.difference claims groups do
                  yield missingRow "CurrentClaims" "ObligationSources" id
              for id in Set.difference groups claims do
                  yield missingRow "ObligationSources" "CurrentClaims" id ]
        let current = revision.CurrentClaims |> Map.toList |> List.map snd
        let inventory =
            if List.sort current = List.sort revision.Obligations then []
            else [{ Part = "Obligations"; Node = None; Reason = "The discharge inventory differs from the complete current claim account." }]
        let incidence =
            revision.Edges
            |> List.filter (fun edge -> edge.Role = EdgeRole.Constrains)
            |> List.groupBy _.Target
            |> List.collect (fun (claim, edges) ->
                let sources = edges |> List.map _.Sources
                if revision.ObligationSources.TryFind claim = Some sources then []
                else [defect "Edges (Constrains)" claim "The ordered constraint sources differ from the current claim's grouped source account."])
        missing @ inventory @ incidence

    /// A region names selected body members separately from source-owned proof
    /// supports. The latter are covered by an explicit whole-owner policy and
    /// current source authorization; they never demand inactive body residency.
    let private regions (revision: Revision) =
        revision.Codata.WitnessSegmentation
        |> Option.toList
        |> List.collect (fun segmentation ->
            let identities = segmentation.Regions |> List.map _.Identity |> Set.ofList
            segmentation.Regions |> List.collect (fun region ->
                [ for memberId in region.Members do
                      if not (revision.Nodes.ContainsKey memberId) then yield missingBody "Codata.WitnessSegmentation.Regions.Members" memberId
                  match region.OwnerSupport with
                  | SupportKey.WholeOwningAnalysisRegion identity when not (System.String.IsNullOrWhiteSpace identity) -> ()
                  | _ -> yield { Part = "Codata.WitnessSegmentation.Regions.OwnerSupport"; Node = region.Root
                                 Reason = "A witness region requires a nonempty whole owning analysis region support account." }
                  for dependency in region.Dependencies do
                      if not (identities.Contains dependency) then
                          yield { Part = "Codata.WitnessSegmentation.Regions.Dependencies"; Node = region.Root
                                  Reason = "A witness region names a dependency outside the stored region account." }
                  for id in region.Root |> Option.toList do
                      if not (region.Members.Contains id) then
                          yield missingRow "Codata.WitnessSegmentation.Regions.Root" "the region's Members" id
                  for id in region.Anchor |> Option.toList do
                      if not (revision.Nodes.ContainsKey id || revision.SourceReadings.ContextHeaders.ContainsKey id) then
                          yield missingRow "Codata.WitnessSegmentation.Regions.Anchor" "live body or SourceReadings.ContextHeaders" id ]))

    /// References which a passive callable reader actually dereferences. Proof
    /// Participants and Supports are intentionally not used to justify these.
    let private callableRows (revision: Revision) =
        let callable = revision.Emission.Callable
        let numeric = revision.Emission.Numeric
        let need part table node present = if present then [] else [missingRow part table node]
        let implementation part node =
            need part "Emission.Callable.Declarations" node (callable.Declarations.ContainsKey node) @
            need part "Emission.Callable.Symbols" node (callable.Symbols.ContainsKey node)
        let shape part permitted = function
            | CallableValueShape.Data node ->
                need part "SignatureData or ClosedData" node (Set.contains node permitted || callable.ClosedData.Contains node) @
                need part "Emission.Numeric.OccurrenceRepresentations" node (numeric.OccurrenceRepresentations.ContainsKey node)
            | CallableValueShape.Callable node ->
                match callable.Carriers.ContainsKey node, callable.Joins.ContainsKey node, callable.Flows.ContainsKey node with
                | true, false, false | false, true, false | false, false, true -> []
                | false, false, false -> [missingRow part "Emission.Callable.Carriers, Joins or Flows" node]
                | _ -> [defect part node "Callable component has conflicting carrier, join or flow rows."]
            | CallableValueShape.Sequence node -> need part "Emission.Storage.Sequences" node (revision.Emission.Storage.Sequences.ContainsKey node)
            | CallableValueShape.Lazy node -> need part "Emission.Storage.Lazies" node (revision.Emission.Storage.Lazies.ContainsKey node)
        [ for KeyValue(site, carrier) in callable.Carriers do
              if site <> carrier.Occurrence then yield defect "Emission.Callable.Carriers.Occurrence" site "A carrier is filed under a different occurrence."
              yield! implementation "Emission.Callable.Carriers.Implementation" carrier.Implementation
              let permitted = callable.SignatureData.TryFind site |> Option.defaultValue Set.empty
              if carrier.Parameters.Length <> carrier.ParameterShapes.Length then
                  yield defect "Emission.Callable.Carriers.ParameterShapes" site "Logical formals and parameter shapes have different lengths."
              for (_, _, formal), expected in List.zip (carrier.Parameters |> List.truncate carrier.ParameterShapes.Length) (carrier.ParameterShapes |> List.truncate carrier.Parameters.Length) do
                  yield! need "Emission.Callable.Carriers.Parameters" "Emission.Callable.ValueShapes" formal (callable.ValueShapes.TryFind formal = Some expected)
                  yield! shape "Emission.Callable.Carriers.ParameterShapes" permitted expected
              yield! need "Emission.Callable.Carriers.Result" "Emission.Callable.ValueShapes" carrier.Result (callable.ValueShapes.TryFind carrier.Result = Some carrier.ResultShape)
              yield! shape "Emission.Callable.Carriers.ResultShape" permitted carrier.ResultShape
              for omitted in carrier.OmittedParameters do
                  if not (carrier.Parameters |> List.exists (fun (_, _, formal) -> formal = omitted)) then
                      yield defect "Emission.Callable.Carriers.OmittedParameters" omitted "An omitted formal is absent from the carrier's logical parameter account."
              match callable.Declarations.TryFind carrier.Implementation with
              | Some declaration when declaration.Parameters <> carrier.Parameters || declaration.Result <> carrier.Result ->
                  yield defect "Emission.Callable.Carriers.Implementation" carrier.Implementation "The carrier signature differs from its stored declaration."
              | _ -> ()
          // The embedded row has mixed executable, signature, contract and
          // lifetime identities. Its exact canonical row owns those roles;
          // flattening them into executable references loses that distinction.
          for KeyValue(_, instance) in callable.ProgramInstances do
              let carrier = instance.Carrier
              yield! need "Emission.Callable.ProgramInstances.Carrier"
                  "Emission.Callable.Carriers with the exact callable carrier" carrier.Occurrence
                  (callable.Carriers.TryFind carrier.Occurrence = Some carrier)
              match carrier.Contract with
              | Ok identity ->
                  yield! need "Emission.Callable.ProgramInstances.Carrier.Contract"
                      "Emission.Callable.Contracts" identity (callable.Contracts.ContainsKey identity)
              | Error _ ->
                  yield defect "Emission.Callable.ProgramInstances.Carrier.Contract" carrier.Occurrence
                      "An initialized program instance has no settled receiving contract."
          for KeyValue(site, call) in callable.Calls do
              if site <> call.Site then yield defect "Emission.Callable.Calls.Site" site "A call is filed under a different site."
              yield! implementation "Emission.Callable.Calls.Implementation" call.Implementation
              for _, _, formal in call.Parameters do
                  match callable.ValueShapes.TryFind formal with
                  | Some expected -> yield! shape "Emission.Callable.Calls.Parameters" call.SignatureData expected
                  | None -> yield missingRow "Emission.Callable.Calls.Parameters" "Emission.Callable.ValueShapes" formal
              match callable.ValueShapes.TryFind call.Result with
              | Some expected -> yield! shape "Emission.Callable.Calls.Result" call.SignatureData expected
              | None -> yield missingRow "Emission.Callable.Calls.Result" "Emission.Callable.ValueShapes" call.Result
          for KeyValue(owner, contract) in revision.Emission.Storage.Lazies do
              // A lazy thunk's code identity is read through Symbols, not its body.
              yield! need "Emission.Storage.Lazies.Layout.Thunk" "Emission.Callable.Symbols" contract.Layout.Thunk (callable.Symbols.ContainsKey contract.Layout.Thunk)
              for claim in contract.Layout.Obligations do
                  yield! need "Emission.Storage.Lazies.Layout.Obligations" "CurrentClaims" claim (revision.CurrentClaims.ContainsKey claim)
              if contract.Layout.Owner <> owner then yield defect "Emission.Storage.Lazies.Layout.Owner" owner "A lazy layout is filed under a different owner." ]

    /// Duplicate carrier rows must match their current scalar account exactly.
    /// Declaration and participant identities are provenance; obligations are
    /// references to the current grouped claim account.
    let private scalarRow (revision: Revision) part expected (row: ScalarCarrier) =
        [ if row.Site <> expected then
              yield defect part expected "The embedded scalar carrier identifies a different site."
          if revision.Emission.Numeric.Values.TryFind expected <> Some row then
              yield missingRow part "Emission.Numeric.Values with the exact scalar carrier" expected
          for claim in row.Obligations do
              if not (revision.CurrentClaims.ContainsKey claim) then
                  yield missingRow part "CurrentClaims" claim ]

    let private adaptationRow part consumer operand (row: Meet) =
        [ if row.Consumer <> consumer then
              yield defect part consumer "The adaptation identifies a different consuming operation."
          if row.Operand <> operand then
              yield defect part operand "The adaptation identifies a different operand." ]

    let private numericOperationRow (revision: Revision) part (operation: NumericOperationWitness) =
        [ if not (revision.Nodes.ContainsKey operation.Site) then
              yield missingBody (part + ".Site") operation.Site
          if not (revision.Nodes.ContainsKey operation.Callee) then
              yield missingBody (part + ".Callee") operation.Callee
          for operand in operation.Operands do
              if not (revision.Nodes.ContainsKey operand.Actual) then
                  yield missingBody (part + ".Operands.Actual") operand.Actual
              for row in operand.Carrier |> Option.toList do
                  yield! scalarRow revision (part + ".Operands.Carrier") operand.Actual row
              for row in operand.Adaptation |> Option.toList do
                  yield! adaptationRow (part + ".Operands.Adaptation") operation.Site operand.Actual row
          yield! scalarRow revision (part + ".Result") operation.Site operation.Result
          for row in operation.ResultAdaptation |> Option.toList do
              yield! adaptationRow (part + ".ResultAdaptation") operation.Site operation.Site row
          for claim in operation.Obligations do
              if not (revision.CurrentClaims.ContainsKey claim) then yield missingRow (part + ".Obligations") "CurrentClaims" claim ]

    /// A numeric operation copies its ordered operands and exact scalar rows.
    /// The operand is executable; a carrier's declaration and participants are
    /// source provenance, while its obligations name current claim accounts.
    let private numericRows (revision: Revision) =
        let numeric = revision.Emission.Numeric
        [ for KeyValue(key, operation) in numeric.Operations do
              if key <> operation.Site then
                  yield defect "Emission.Numeric.Operations.Site" key "An operation is filed under a different site."
              yield! numericOperationRow revision "Emission.Numeric.Operations" operation ]

    /// Memory operations separate their executable operands from declaration
    /// provenance and complete source proof participants. Shared rows are exact
    /// stored copies, including the ordered requirement and snapshot accounts.
    let private memoryRows (revision: Revision) =
        let memory = revision.Emission.Memory
        let body part id = if revision.Nodes.ContainsKey id then [] else [missingBody part id]
        let requirement part (row: RequirementWitness) =
            [ if revision.Emission.Storage.Requirements.TryFind row.Site <> Some row then
                  yield missingRow part "Emission.Storage.Requirements with the exact requirement" row.Site
              for id in [row.Site; row.Condition; row.Frontier; row.Continuation] @ Option.toList row.PatternTest do
                  yield! body (part + ".Operand") id ]
        let residence part = function
            | MemoryResidence.Stack(scope, _) -> body (part + ".Scope") scope
            | MemoryResidence.ImmutableProgram _ -> []
            | MemoryResidence.Program identity ->
                if revision.Emission.Storage.ProgramStorage.Entries.ContainsKey identity then []
                else
                    let id = match identity with ProgramStorageIdentity.Allocation id | ProgramStorageIdentity.BindingSlot id -> id
                    [missingRow part "Emission.Storage.ProgramStorage.Entries" id]
        let bounds part (row: MemoryBoundsWitness) =
            [ for id in [row.Buffer; row.Index; row.Length; row.Lower; row.Upper] do yield! body (part + ".Operand") id
              yield! scalarRow revision (part + ".IndexCarrier") row.Index row.IndexCarrier
              yield! scalarRow revision (part + ".ExtentCarrier") row.Length row.ExtentCarrier
              yield! requirement (part + ".Requirement") row.Requirement ]
        let access part (row: MemoryArrayAccessWitness) =
            [ for id in [row.Site; row.Buffer; row.Index] @ Option.toList row.Value do yield! body (part + ".Operand") id
              if row.Bounds.Buffer <> row.Buffer || row.Bounds.Index <> row.Index then
                  yield defect (part + ".Bounds") row.Site "The bounds account identifies different array operands."
              yield! bounds (part + ".Bounds") row.Bounds
              for adaptation in Option.toList row.Adaptation do
                  yield! adaptationRow (part + ".Adaptation") row.Site (row.Value |> Option.defaultValue row.Site) adaptation ]
        let copyAccess part (row: MemoryArrayAccessWitness) =
            [ if memory.Operations.TryFind row.Site <> Some(MemoryWitnessOperation.ArrayAccess row) then
                  yield missingRow part "Emission.Memory.Operations with the exact array access" row.Site
              yield! access part row ]
        let representation part site expected =
            if revision.Emission.Numeric.OccurrenceRepresentations.TryFind site = Some(Ok expected) then []
            else [missingRow part "Emission.Numeric.OccurrenceRepresentations with the exact physical carrier" site]
        [ for KeyValue(key, operation) in memory.Operations do
              let site =
                  match operation with
                  | MemoryWitnessOperation.BufferExtent row -> row.Site
                  | MemoryWitnessOperation.ArrayExtent row -> row.Site
                  | MemoryWitnessOperation.ArrayAccess row -> row.Site
                  | MemoryWitnessOperation.ArrayLiteral row -> row.Site
                  | MemoryWitnessOperation.ArrayAllocation row -> row.Site
                  | MemoryWitnessOperation.Address row -> row.Site
                  | MemoryWitnessOperation.StringView row -> row.Site
              if key <> site then yield defect "Emission.Memory.Operations.Site" key "A memory operation is filed under a different site."
              yield! body "Emission.Memory.Operations.Site" site
              match operation with
              | MemoryWitnessOperation.BufferExtent row ->
                  yield! body "Emission.Memory.Operations.BufferExtent.Source" row.Source
                  yield! scalarRow revision "Emission.Memory.Operations.BufferExtent.Result" row.Site row.Result
                  if revision.Emission.Boundary.StringExtents.TryFind row.Extent.Site <> Some row.Extent then
                      yield missingRow "Emission.Memory.Operations.BufferExtent.Extent" "Emission.Boundary.StringExtents with the exact extent" row.Extent.Site
              | MemoryWitnessOperation.ArrayExtent row ->
                  yield! body "Emission.Memory.Operations.ArrayExtent.Source" row.Source
                  yield! scalarRow revision "Emission.Memory.Operations.ArrayExtent.Result" row.Site row.Result
              | MemoryWitnessOperation.ArrayAccess row -> yield! access "Emission.Memory.Operations.ArrayAccess" row
              | MemoryWitnessOperation.ArrayLiteral row ->
                  for element, adaptation in row.Elements do
                      yield! body "Emission.Memory.Operations.ArrayLiteral.Elements" element
                      for adaptation in Option.toList adaptation do
                          yield! adaptationRow "Emission.Memory.Operations.ArrayLiteral.Adaptation" row.Site element adaptation
                  yield! residence "Emission.Memory.Operations.ArrayLiteral.Residence" row.Residence
              | MemoryWitnessOperation.ArrayAllocation row ->
                  yield! body "Emission.Memory.Operations.ArrayAllocation.Count" row.Count
                  yield! scalarRow revision "Emission.Memory.Operations.ArrayAllocation.CountCarrier" row.Count row.CountCarrier
                  yield! requirement "Emission.Memory.Operations.ArrayAllocation.Requirement" row.Requirement
                  yield! residence "Emission.Memory.Operations.ArrayAllocation.Residence" row.Residence
              | MemoryWitnessOperation.Address row ->
                  match row.Place with
                  | MemoryPlace.MutableCell binding -> yield! body "Emission.Memory.Operations.Address.Binding" binding
                  | MemoryPlace.ExistingReference source -> yield! body "Emission.Memory.Operations.Address.Source" source
                  | MemoryPlace.RecordField(receiver, _, _) -> yield! body "Emission.Memory.Operations.Address.Receiver" receiver
                  | MemoryPlace.ArrayElement(buffer, index, account) ->
                      if account.Buffer <> buffer || account.Index <> index then
                          yield defect "Emission.Memory.Operations.Address.Bounds" row.Site "The address bounds identify different array operands."
                      yield! bounds "Emission.Memory.Operations.Address.Bounds" account
              | MemoryWitnessOperation.StringView row ->
                  yield! body "Emission.Memory.Operations.StringView.Source" row.Source
                  yield! representation "Emission.Memory.Operations.StringView.SourceCarrier" row.Source row.SourceCarrier
                  yield! representation "Emission.Memory.Operations.StringView.ResultCarrier" row.Site row.ResultCarrier
                  yield! scalarRow revision "Emission.Memory.Operations.StringView.Extent" row.Extent.Site row.Extent
                  match memory.ArrayCopies.TryFind row.Snapshot with
                  | Some copy when copy.Site = row.Snapshot && copy.CountCarrier = row.Extent ->
                      match row.Direction with
                      | MemoryStringViewDirection.FromBytes when row.Source <> row.Snapshot ->
                          yield defect "Emission.Memory.Operations.StringView.Snapshot" row.Site "The constructed string source differs from its snapshot."
                      | MemoryStringViewDirection.ToBytes when copy.Source <> row.Site ->
                          yield defect "Emission.Memory.Operations.StringView.Snapshot" row.Site "The snapshot copy reads a different internal string view."
                      | _ -> ()
                  | _ -> yield missingRow "Emission.Memory.Operations.StringView.Snapshot" "Emission.Memory.ArrayCopies with the exact snapshot and count carrier" row.Snapshot
          for KeyValue(key, row) in memory.ArrayCopies do
              if key <> row.Site then yield defect "Emission.Memory.ArrayCopies.Site" key "An array copy is filed under a different site."
              for id in [row.Site; row.Source; row.SourceOffset; row.Destination; row.DestinationOffset; row.Count] @ Option.toList row.Loop do
                  yield! body "Emission.Memory.ArrayCopies.Operand" id
              yield! scalarRow revision "Emission.Memory.ArrayCopies.CountCarrier" row.Count row.CountCarrier
              for allocation in Option.toList row.Allocation do
                  match memory.Operations.TryFind allocation with
                  | Some(MemoryWitnessOperation.ArrayAllocation row) when row.Site = allocation -> ()
                  | _ -> yield missingRow "Emission.Memory.ArrayCopies.Allocation" "Emission.Memory.Operations (array allocation)" allocation
              for row in Option.toList row.Read do yield! copyAccess "Emission.Memory.ArrayCopies.Read" row
              for row in Option.toList row.Write do yield! copyAccess "Emission.Memory.ArrayCopies.Write" row
              for row in row.Requirements do yield! requirement "Emission.Memory.ArrayCopies.Requirements" row ]

    /// A source storage reservation and its selected entries name the same
    /// immutable space and ordered objects. No source declaration body or
    /// capacity calculation is needed to compare these stored accounts.
    let private programStorageRows (revision: Revision) =
        let check part (storage: ProgramStorageInventory) =
            let identityName =
                function
                | ProgramStorageIdentity.Allocation id -> sprintf "allocation:%d" (NodeId.value id)
                | ProgramStorageIdentity.BindingSlot id -> sprintf "binding:%d" (NodeId.value id)

            [
                for KeyValue(identity, entry) in storage.Entries do
                    let id =
                        match identity with
                        | ProgramStorageIdentity.Allocation id
                        | ProgramStorageIdentity.BindingSlot id -> id

                    if identity <> entry.Identity then
                        yield defect (part + ".Entries.Identity") id "A storage entry is filed under a different identity."

                    match storage.Reservations.TryFind entry.SpaceNode with
                    | Some reservation when reservation.Space = entry.Space -> ()
                    | _ -> yield missingRow (part + ".Entries.SpaceNode") "Reservations with the exact declared space" entry.SpaceNode

                    match entry.Shape with
                    | ProgramStorageShape.NativeEntry formation ->
                        let source = revision.Nodes.TryFind id

                        let initializer =
                            revision.Emission.Storage.Startup
                            |> Option.bind (fun startup ->
                                if not (startup.ValueBindings.Contains id) then
                                    None
                                else
                                    startup.Initializers |> List.tryFind (fun row -> row.Binding = id))

                        let correspondence =
                            match identity, source, initializer, revision.Emission.Boundary.Entries.TryFind formation with
                            | ProgramStorageIdentity.BindingSlot binding,
                              Some {
                                       Kind = SemanticKind.Binding(_, false, false, None)
                                       Children = [ actual ]
                                       Type = ty
                                   },
                              Some startup,
                              Some native ->
                                binding = id
                                && actual = startup.Initializer
                                && ty = entry.SourceType
                                && ty = native.SourceType
                                && native.Formation = formation
                                && native.Transport.Contains binding
                                && native.Transport.Contains actual
                                && Set.isSubset
                                    (Set.ofList [ binding; actual; formation; native.Operand; native.Declaration ])
                                    entry.Participants
                                && (revision.Emission.Boundary.Loading
                                    |> Option.exists (fun loading -> loading.Identity = native.Loading))
                                && revision.Emission.Boundary.Imports.ContainsKey native.Import
                            | _ -> false

                        if not correspondence then
                            yield
                                defect
                                    (part + ".Entries.NativeEntry")
                                    id
                                    "The native entry slot lacks its exact immutable startup initializer and current imported-entry loading correspondence."

                        let layout =
                            match revision.Platform.Pointer with
                            | Ok bits when bits > 0 && bits % 8 = 0 ->
                                entry.Bytes = bits / 8
                                && entry.Alignment > 0
                                && (entry.Alignment &&& (entry.Alignment - 1)) = 0
                            | _ -> false

                        if not layout then
                            yield
                                defect
                                    (part + ".Entries.NativeEntry.Layout")
                                    id
                                    "The native entry slot differs from its declared positive Pointer extent and power-of-two alignment."

                        for KeyValue(read, node) in revision.Nodes do
                            match node.Kind with
                            | SemanticKind.VarRef(_, Some binding) when binding = id ->
                                match
                                    revision.SourceReadings.BindingUses.TryFind read, revision.Emission.Boundary.Entries.TryFind formation
                                with
                                | Some bindingUse, Some native when
                                    bindingUse.Binding = id
                                    && bindingUse.Class = SourceBindingClass.ImmutableValue
                                    && bindingUse.IsProgramSlotIntent
                                    && bindingUse.HasProgramSlotAuthority
                                    && native.Transport.Contains read
                                    ->
                                    ()
                                | _ ->
                                    yield
                                        defect
                                            (part + ".Entries.NativeEntry.Read")
                                            read
                                            "The native entry slot read lacks its exact immutable binding, storage and entry transport account."
                            | _ -> ()
                    | _ -> ()
                for KeyValue(space, reservation) in storage.Reservations do
                    let entries =
                        storage.Entries
                        |> Map.toList
                        |> List.filter (fun (_, entry) -> entry.SpaceNode = space)

                    let expected: BAREWire.Platform.StorageRequest list =
                        entries
                        |> List.map (fun (identity, entry) ->
                            {
                                Name = identityName identity
                                Length = int64 entry.Bytes
                                Alignment = entry.Alignment
                            })

                    if entries.IsEmpty || Array.toList reservation.Requests <> expected then
                        yield
                            defect (part + ".Reservations") space "The ordered reserved objects differ from the storage entries for this space."
            ]

        check "Codata.ProgramStorage" revision.Codata.ProgramStorage
        @ check "Emission.Storage.ProgramStorage" revision.Emission.Storage.ProgramStorage
        @ (if revision.Codata.ProgramStorage = revision.Emission.Storage.ProgramStorage then
               []
           else
               [
                   {
                       Part = "Emission.Storage.ProgramStorage"
                       Node = None
                       Reason = "The program storage account differs from Codata.ProgramStorage."
                   }
               ])

    /// A kernel's ordered scalar steps repeat the numeric owner's settled rows.
    /// Topology declarations, copied ingress premises and metadata omissions are
    /// separate source accounts; none can authorize an executable step.
    let private spatialRows (revision: Revision) =
        let spatial = revision.Emission.Spatial
        let need part table id present = if present then [] else [missingRow part table id]
        let body part id = need part "Nodes (executable occurrence)" id (revision.Nodes.ContainsKey id)
        let context part id = need part "live body or SourceReadings.ContextHeaders" id
                                 (revision.Nodes.ContainsKey id || revision.SourceReadings.ContextHeaders.ContainsKey id)
        let obligations part ids =
            ids |> List.collect (fun id -> need part "CurrentClaims" id (revision.CurrentClaims.ContainsKey id))
        [ for KeyValue(key, kernel) in spatial.Kernels do
              let part = "Emission.Spatial.Kernels"
              if key <> kernel.Site then yield defect (part + ".Site") key "A kernel is filed under a different site."
              yield! context (part + ".Scope") kernel.Scope
              yield! obligations (part + ".Obligations") kernel.Obligations
              let ingress = kernel.Ingress
              if ingress.Site <> kernel.Site || ingress.Scope <> kernel.Scope || ingress.ComputeBinding <> kernel.ComputeBinding ||
                 ingress.Implementation <> kernel.Implementation || ingress.Parameters <> kernel.Parameters || ingress.Result <> kernel.Result then
                  yield defect (part + ".Ingress") kernel.Site "The ingress signature differs from its kernel account."
              if kernel.Target.Declaration <> ingress.Target then
                  yield defect (part + ".Target") kernel.Site "The selected target declaration differs from its ingress account."
              for id in [ingress.Target; ingress.Core] do
                  yield! need (part + ".Ingress.Declaration") "the ingress's Premises" id (ingress.Premises.ContainsKey id)
              for transport in ingress.Inputs @ [ingress.Output] do
                  yield! need (part + ".Ingress.Transport") "the ingress's Premises" transport.Declaration (ingress.Premises.ContainsKey transport.Declaration)
              for id in ingress.ComputePath do
                  yield! need (part + ".Ingress.ComputePath") "live code or the ingress's Uses" id
                      (revision.Nodes.ContainsKey id || ingress.Uses.ContainsKey id)
              for KeyValue(id, fact) in ingress.Uses do
                  if System.String.IsNullOrWhiteSpace fact.Form then yield defect (part + ".Ingress.Uses") id "A copied declaration fact has no form."
              for KeyValue(id, fact) in ingress.Premises do
                  if System.String.IsNullOrWhiteSpace fact.Form then yield defect (part + ".Ingress.Premises") id "A copied premise fact has no form."
              for step in kernel.Steps do
                  let stepPart = part + ".Steps"
                  match step with
                  | KernelScalarStep.Parameter(site, ordinal, carrier) ->
                      yield! body (stepPart + ".Site") site
                      if kernel.Parameters |> List.tryItem ordinal |> Option.map snd <> Some site then
                          yield defect stepPart site "A scalar parameter differs from the kernel's ordered formal account."
                      yield! scalarRow revision (stepPart + ".Carrier") site carrier
                  | KernelScalarStep.Literal(site, _, carrier) ->
                      yield! body (stepPart + ".Site") site
                      yield! scalarRow revision (stepPart + ".Carrier") site carrier
                  | KernelScalarStep.Alias(site, source, carrier, adaptation) ->
                      yield! body (stepPart + ".Site") site
                      yield! body (stepPart + ".Source") source
                      yield! scalarRow revision (stepPart + ".Carrier") site carrier
                      for row in Option.toList adaptation do yield! adaptationRow (stepPart + ".Adaptation") site source row
                  | KernelScalarStep.Operation operation ->
                      if revision.Emission.Numeric.Operations.TryFind operation.Site <> Some operation then
                          yield missingRow (stepPart + ".Operation") "Emission.Numeric.Operations with the exact scalar operation" operation.Site
                      yield! numericOperationRow revision (stepPart + ".Operation") operation
          for KeyValue(key, hardware) in spatial.Hardware do
              let part = "Emission.Spatial.Hardware"
              if key <> hardware.Site then yield defect (part + ".Site") key "A hardware module is filed under a different site."
              yield! context (part + ".Scope") hardware.Scope
              yield! obligations (part + ".Obligations") hardware.Obligations
              // Clock identities are source declaration provenance. This exact
              // path account does not grant executable or general table roles.
              for field, id in ["ClockReference", hardware.ClockReference; "ClockDeclaration", hardware.ClockDeclaration] do
                  yield! need (part + "." + field) "the hardware module's ClockPath" id (hardware.ClockPath.Contains id) ]

    /// Startup ordering names a module context and live initialization actions.
    /// The module header does not stand in for either executable identity.
    let private startupRows (revision: Revision) =
        [ for startup in Option.toList revision.Emission.Storage.Startup do
              for row in startup.Initializers do
                  match revision.SourceReadings.ContextHeaders.TryFind row.Module with
                  | Some header when header.Identity = row.Module && header.Ports.ContainsKey OccurrencePort.ModuleDeclaration -> ()
                  | _ -> yield missingRow "Emission.Storage.Startup.Initializers.Module" "SourceReadings.ContextHeaders (module declaration account)" row.Module
                  for id in [row.Binding; row.Initializer] do
                      if not (revision.Nodes.ContainsKey id) then yield missingBody "Emission.Storage.Startup.Initializers.Action" id ]

    /// Agreement of stored foreign hypotheses, invocation incidence and current
    /// ledger citizens. This performs no inference or conditional discharge.
    let private foreignHypothesisFact (revision: Revision) (hypothesis: ForeignResultHypothesis) id =
        hypothesis.Quote = id
        && List.contains hypothesis revision.Emission.Boundary.ResultHypotheses

    let private foreignApplicationFact (revision: Revision) (application: ForeignResultApplication) id =
        let boundary = revision.Emission.Boundary

        revision.Nodes.ContainsKey id
        || (application.Declaration = id
            && (boundary.Imports
                |> Map.exists (fun _ imported ->
                    imported.DeclarationFacts.ContainsKey id || imported.SourceTypes.ContainsKey id)))
        || (List.contains id application.Context
            && revision.SourceReadings.ContextHeaders.ContainsKey id)
        || (application.Hypothesis
            |> Option.exists (fun hypothesis -> foreignHypothesisFact revision hypothesis id))

    let private foreignAbiFact (revision: Revision) (model: ForeignResultCoverageModel) id =
        revision.Emission.Boundary.Calls.TryFind model.Application.Call
        |> Option.exists (fun call ->
            revision.Emission.Boundary.Imports.TryFind call.Import
            |> Option.exists (fun imported ->
                imported.Binding = model.Application.Declaration
                && imported.DeclarationFacts.ContainsKey id))

    let private foreignDestinationFact (revision: Revision) (model: ForeignResultCoverageModel) id =
        revision.Emission.Numeric.Values.TryFind model.Application.Call
        |> Option.exists (fun carrier -> carrier.Declaration = Some id)

    let private foreignClaimFact revision (model: ForeignResultCoverageModel) id =
        foreignApplicationFact revision model.Application id
        || (model.Abi = Some id && foreignAbiFact revision model id)
        || (model.DestinationDeclaration = Some id
            && foreignDestinationFact revision model id)

    let private foreignResultRows (revision: Revision) =
        let hypotheses = revision.Emission.Boundary.ResultHypotheses
        let uses = revision.Emission.Numeric.ForeignResultUses
        let fail site suffix reason = defect ("Emission.Numeric.ForeignResultUses." + suffix) site reason
        let roles = [ForeignResultProofRole.LogicalCoverage; ForeignResultProofRole.AbiNarrowing]
        let ordinal role = if role = ForeignResultProofRole.LogicalCoverage then 0 else 1
        let participant call role index node : Participant = {Node = node; Role = role; Ordinal = index; Group = call}
        [ for hypothesis in hypotheses do
              if System.String.IsNullOrWhiteSpace hypothesis.Identity || System.String.IsNullOrWhiteSpace hypothesis.Version ||
                 System.String.IsNullOrWhiteSpace hypothesis.Source then
                  yield defect "Emission.Boundary.ResultHypotheses.Provenance" hypothesis.Declaration "An external execution hypothesis has incomplete identity, version or source."
              if hypotheses |> List.filter (fun row -> row.Declaration = hypothesis.Declaration) |> List.length <> 1 then
                  yield defect "Emission.Boundary.ResultHypotheses.Declaration" hypothesis.Declaration "A declaration has duplicate external result hypotheses."
              for bound in [hypothesis.Lower; hypothesis.Upper] do
                  match bound with
                  | ForeignResultBound.Argument index when index < 0 ->
                      yield defect "Emission.Boundary.ResultHypotheses.Argument" hypothesis.Declaration "A result bound has a negative argument ordinal."
                  | _ -> ()
          for account in uses do
              let application = account.Application
              let call = application.Call
              if uses |> List.filter (fun row -> row.Application.Call = call && row.Application.Context = application.Context) |> List.length <> 1 then
                  yield fail call "Application" "The exact call/context account is duplicated."
              match application.Hypothesis, hypotheses |> List.filter (fun row -> row.Declaration = application.Declaration) with
              | None, [] -> ()
              | Some hypothesis, [current] when hypothesis = current && hypothesis.Declaration = application.Declaration -> ()
              | _ -> yield fail call "Hypothesis" "The invocation hypothesis or its absence differs from the exact current declaration census."
              if (application.Arguments |> List.map _.Index) <> [0 .. application.Arguments.Length - 1] then
                  yield fail call "Arguments" "The actual arguments lack exact consecutive source ordinals."
              for hypothesis in Option.toList application.Hypothesis do
                  for bound in [hypothesis.Lower; hypothesis.Upper] do
                      match bound with
                      | ForeignResultBound.Argument index when index < 0 || index >= application.Arguments.Length ->
                          yield fail call "Arguments" "A result endpoint names an absent actual argument."
                      | _ -> ()
              if List.map fst account.Claims <> roles || (account.Claims |> List.map snd |> List.distinct).Length <> 2 then
                  yield fail call "Claims" "Logical coverage and ABI narrowing must retain two distinct ordered claim citizens."
              let expected =
                  [participant call ParticipantRole.ForeignResultDeclaration 0 application.Declaration
                   participant call ParticipantRole.ForeignResultCall 0 call] @
                  (application.Context |> List.mapi (participant call ParticipantRole.ForeignResultContext)) @
                  (application.Hypothesis |> Option.map (fun hypothesis -> participant call ParticipantRole.ForeignResultHypothesis 0 hypothesis.Quote) |> Option.toList) @
                  (application.Arguments |> List.map (fun argument -> participant call ParticipantRole.ForeignResultActual argument.Index argument.Node))
              let models =
                  account.Claims |> List.choose (fun (role, citizen) ->
                      match revision.CurrentClaims.TryFind citizen with
                      | Some claim ->
                          match claim.Body with
                          | ObligationBody.ForeignResultCoverage model when model.Application = application && model.Role = role -> Some(role, citizen, model)
                          | _ -> None
                      | None -> None)
              if models.Length <> account.Claims.Length then
                  yield fail call "Claims" "A claim citizen lacks its exact current conditional model, role or invocation."
              for _, _, model in models do
                  for abi in Option.toList model.Abi do
                      if not (foreignAbiFact revision model abi) then
                          yield
                              fail
                                  abi
                                  "Abi"
                                  "A conditional ABI premise lacks its own call's imported declaration fact."

                  for destination in Option.toList model.DestinationDeclaration do
                      if not (foreignDestinationFact revision model destination) then
                          yield
                              fail
                                  destination
                                  "Destination"
                                  "A conditional destination premise differs from its own call's selected numeric carrier."

                  for identity, carrier in
                      [
                          model.AbiIdentity, model.Abi
                          model.DestinationIdentity, model.DestinationDeclaration
                      ] do
                      match identity with
                      | Some value when System.String.IsNullOrWhiteSpace value || carrier.IsNone ->
                          yield
                              fail
                                  call
                                  "Provenance"
                                  "A stated foreign-result premise anchor is blank or lacks its current premise node."
                      | _ -> ()

              let complete = expected @ (models |> List.collect (fun (role, _, model) ->
                  (model.Abi |> Option.map (participant call ParticipantRole.ForeignResultAbi (ordinal role)) |> Option.toList) @
                  (model.DestinationDeclaration |> Option.map (participant call ParticipantRole.ForeignResultDestination (ordinal role)) |> Option.toList)))
              let actual = match account.Participants with ParticipantEvidence.Pending early -> early.Derived | ParticipantEvidence.Established rows -> rows
              if actual <> complete then
                  yield fail call "Participants" "The ordered declaration, call, context, hypothesis, actual, ABI or destination roles differ from their current model."
              for _, citizen in account.Claims do
                  if (uses |> List.collect _.Claims |> List.filter (fun (_, id) -> id = citizen)).Length <> 1 then
                      yield fail call "Claims" "A conditional claim citizen belongs to more than one invocation or role."
                  if revision.ObligationSources.TryFind citizen <> Some [actual |> List.map _.Node] then
                      yield fail call "Sources" "A claim has a different complete ordered source vector."
          for KeyValue(citizen, claim) in revision.CurrentClaims do
              match claim.Body with
              | ObligationBody.ForeignResultCoverage model ->
                  let matches = uses |> List.filter (fun account ->
                      account.Application = model.Application && List.contains (model.Role, citizen) account.Claims)
                  if matches.Length <> 1 then
                      yield fail model.Application.Call "Claims" "A current conditional claim lacks its exact invocation account."
              | _ -> ()
          for edge in revision.Edges do
              match edge.Role with
              | EdgeRole.BoundaryDomain domain when domain.ResultHypotheses <> hypotheses ->
                  yield defect "Emission.Boundary.ResultHypotheses.Domain" edge.Target "The published hypothesis census differs from its stored boundary domain."
              | EdgeRole.NumericDomain domain when domain.ForeignResultUses <> uses ->
                  yield fail edge.Target "Domain" "The published result uses differ from their stored numeric domain."
              | _ -> () ]

    /// Boundary references resolve inside their owning imported declaration.
    /// Import membership is not executable residency or general ID authority.
    let private boundaryRows (revision: Revision) =
        let boundary = revision.Emission.Boundary
        let memory = revision.Emission.Memory

        let need part table node present =
            if present then [] else [ missingRow part table node ]

        let loadingFields (row: BoundaryLoading) =
            let contract = row.Contract

            [
                "Identity", contract.Identity
                "Version", contract.Version
                "Source", contract.Source
                "Library", contract.Library
                "Runtime", contract.Runtime
                "Os", contract.Os
                "Arch", contract.Arch
                "LoadAt", contract.LoadAt
                "LiveUntil", contract.LiveUntil
                "Unloading", contract.Unloading
                "ExportedLibrary", contract.ExportedLibrary
            ]

        let immutableRead (entry: BoundaryEntry) id =
            match revision.Nodes.TryFind id, revision.SourceReadings.BindingUses.TryFind id with
            | Some {
                       Kind = SemanticKind.VarRef(_, Some binding)
                   },
              Some useRow ->
                useRow.Binding = binding
                && useRow.Class = SourceBindingClass.ImmutableValue
                && (not useRow.IsProgramSlotIntent
                    || (useRow.HasProgramSlotAuthority
                        && (let identity = ProgramStorageIdentity.BindingSlot binding
                            match revision.Codata.ProgramStorage.Entries.TryFind identity,
                                  revision.Emission.Storage.ProgramStorage.Entries.TryFind identity with
                            | Some stored, Some emitted ->
                                stored = emitted
                                && stored.Shape = ProgramStorageShape.NativeEntry entry.Formation
                                && stored.SourceType = entry.SourceType
                            | _ -> false)))
                && not useRow.IsPartialApplication
                && entry.Transport.Contains binding
            | _ -> false

        let transportMember (entry: BoundaryEntry) id =
            if id = entry.Declaration then
                true
            else
                match revision.Nodes.TryFind id with
                | Some { Kind = SemanticKind.VarRef _ } -> immutableRead entry id
                | Some {
                           Kind = SemanticKind.Binding(_, false, false, None)
                           Children = [ child ]
                       } -> entry.Transport.Contains child
                | Some {
                           Kind = SemanticKind.Intrinsic {
                                                             Module = IntrinsicModule.FnPtr
                                                             Operation = "ofExtern"
                                                         }
                       } -> true
                | Some {
                           Kind = SemanticKind.Application(callee, [ operand ])
                           Children = children
                       } when id = entry.Formation ->
                    operand = entry.Operand
                    && children = [ callee; operand ]
                    && entry.Transport.Contains callee
                | Some {
                           Kind = SemanticKind.TypeAnnotation(inner, _)
                           Children = [ child ]
                       } -> inner = child && entry.Transport.Contains child
                | _ -> false

        [
            for KeyValue(key, invocation) in boundary.CallbackInvocations do
                let part = "Emission.Boundary.CallbackInvocations"
                if key <> invocation.Identity then
                    yield defect (part + ".Identity") key "A callback invocation is filed under a different quotation."
                match boundary.Imports.TryFind invocation.Import with
                | Some imported when
                    (imported.Parameters |> List.tryItem invocation.Parameter) = Some(invocation.Formal, BoundaryScalar.Entry invocation.Identity) ->
                    for id in [invocation.Identity; invocation.Scope] do
                        yield! need (part + ".Declaration") "the receiving import's exact quotation facts" id
                            (imported.DeclarationFacts.ContainsKey id)
                    if not (Set.isSubset (Set.ofList [invocation.Identity; invocation.Scope; invocation.Import; invocation.Formal]) invocation.Participants) then
                        yield defect (part + ".Participants") key "The callback invocation omits its quotation, receiving import, formal or scope."
                | _ -> yield defect (part + ".Formal") key "The callback invocation differs from its receiving import's original native ordinal and Entry formal."
                let contract = invocation.Contract
                let scalar = function
                    | BAREWire.Descriptors.TypeRef.Integer(sign, bits) when bits > 0 -> Some(BoundaryScalar.Integer(bits, sign = BAREWire.Descriptors.Signedness.Signed))
                    | BAREWire.Descriptors.TypeRef.Bool -> Some BoundaryScalar.Boolean
                    | _ -> None
                let parameters = contract.Signature.Parameters |> Array.map (fun parameter ->
                    if parameter.PassBy = BAREWire.Descriptors.PassBy.Value then scalar parameter.Type else None) |> Array.toList
                let result = scalar contract.Signature.ReturnType
                if contract.Parameter <> invocation.Parameter ||
                   contract.Signature.CallingConvention <> BAREWire.Descriptors.CallConv.CDecl ||
                   invocation.Signature.CallingConvention <> "CDecl" ||
                   parameters.Length <> 1 || (parameters |> List.exists Option.isNone) || result.IsNone ||
                   List.choose id parameters <> invocation.Signature.Parameters || result <> invocation.Signature.Result then
                    yield defect (part + ".Signature") key "The callback signature differs from its complete nonnested scalar CDecl receiving quotation."
                if [contract.Binding; contract.Scope; contract.Hypothesis.Identity; contract.Hypothesis.Version; contract.Hypothesis.Source]
                   |> List.exists System.String.IsNullOrWhiteSpace then
                    yield defect (part + ".Provenance") key "The callback invocation has missing receiver, scope or trusted hypothesis provenance."
            for KeyValue(key, entry) in boundary.ClosedEntries do
                let part = "Emission.Boundary.ClosedEntries"
                if key <> entry.Formation then
                    yield defect (part + ".Formation") key "A closed native entry is filed under a different formation."
                match boundary.CallbackInvocations.TryFind entry.Invocation,
                      revision.Emission.Callable.Declarations.TryFind entry.Implementation,
                      revision.Emission.Callable.Carriers.TryFind entry.Formation with
                | Some invocation, Some declaration, Some carrier ->
                    let lifetime = carrier.Contract |> Result.toOption |> Option.bind revision.Emission.Callable.Contracts.TryFind
                    let lifetimeMatches =
                        match lifetime with
                        | Some { Kind = CallableKind.NativeEntry; Convention = CallableConvention.CompilerOwnedPortable convention } ->
                            convention.CodeLifetime = entry.Lifetime && entry.Lifetime.Binding = entry.Declaration &&
                            entry.Lifetime.Implementation = entry.Implementation
                        | _ -> false
                    if not lifetimeMatches then
                        yield defect (part + ".Lifetime") key "The closed entry differs from its original ProgramImage code lifetime contract."
                    match carrier.Contract with
                    | Ok identity when entry.Participants.Contains identity &&
                         (entry.Participants |> Set.forall (fun id ->
                             not (revision.Emission.Callable.Contracts.ContainsKey id) || id = identity)) -> ()
                    | _ -> yield defect (part + ".Participants") key "The closed entry omits its own original callable contract or names another contract as support."
                    if carrier.Kind <> CallableKind.NativeEntry || carrier.Formation <> key || carrier.Implementation <> entry.Implementation ||
                       Option.isSome carrier.Environment || carrier.EnvironmentValue.IsSome || not carrier.OmittedParameters.IsEmpty ||
                       not declaration.Captures.IsEmpty || declaration.Result <> entry.Body ||
                       (declaration.Parameters |> List.map (fun (_, _, id) -> id)) <> entry.Formals ||
                       entry.Formals.Length <> invocation.Signature.Parameters.Length || entry.ParameterAdaptations.Length <> entry.Formals.Length then
                        yield defect (part + ".Declaration") key "The closed entry differs from its original capture-free implementation, body or complete ordered native formals."
                    let addressMatches =
                        match revision.Codata.FunctionPointers.TryFind key, revision.Emission.Callable.NativeEntries.TryFind entry.Implementation with
                        | Some(FunctionPointerPlan.Address(symbol, implementation)), Some native ->
                            implementation = entry.Implementation && native = symbol
                        | _ -> false
                    if not addressMatches then
                        yield defect (part + ".Plan") key "The closed entry lacks its exact original typed address and native symbol plan."
                    let formationMatches =
                        match revision.Nodes.TryFind key with
                        | Some { Kind = SemanticKind.Application(callee, [operand]); Children = children } when
                            operand = entry.Operand && children = [callee; operand] ->
                            revision.Nodes.TryFind callee |> Option.exists (fun node ->
                                match node.Kind with
                                | SemanticKind.Intrinsic {Module = IntrinsicModule.FnPtr; Operation = "ofFunction"} -> true
                                | _ -> false)
                        | _ -> false
                    if not formationMatches then
                        yield defect (part + ".Formation") key "The closed entry differs from its original typed ofFunction formation and operand."
                    if entry.ResultAdaptation <> revision.Codata.ReturnMeets.TryFind entry.Implementation then
                        yield defect (part + ".ResultAdaptation") key "The closed entry result adaptation differs from its exact original return meet."
                    if entry.Formals.Length = entry.ParameterAdaptations.Length then
                        for formal, adaptation in List.zip entry.Formals entry.ParameterAdaptations do
                            for meet in Option.toList adaptation do
                                yield! adaptationRow (part + ".ParameterAdaptations") entry.Implementation formal meet
                    if not (Set.isSubset (Set.ofList ([entry.Formation; entry.Operand; entry.Declaration; entry.Implementation; entry.Body; entry.Invocation;
                                                       entry.Lifetime.Module; entry.Lifetime.Binding; entry.Lifetime.Implementation] @ entry.Formals)) entry.Participants) ||
                       not (Set.isSubset entry.Transport entry.Participants) || not (entry.Transport.Contains key) || not (entry.Transport.Contains entry.Operand) then
                        yield defect (part + ".Participants") key "The closed entry omits original code, lifetime, signature or immutable transport support."
                | _ -> yield defect (part + ".Account") key "The closed entry lacks its exact invocation, original callable declaration or native carrier."
            for KeyValue(_, call) in boundary.Calls do
                for operand in call.Arguments do
                    match operand.Abi with
                    | BoundaryScalar.Entry invocation ->
                        let entries = boundary.ClosedEntries.Values |> Seq.filter (fun entry -> entry.Invocation = invocation && entry.Transport.Contains operand.Actual) |> Seq.toList
                        match boundary.CallbackInvocations.TryFind invocation, entries with
                        | Some receiving, [entry] when receiving.Import = call.Import && receiving.Formal = operand.Formal && operand.Adaptation.IsNone ->
                            let projection =
                                match revision.Nodes.TryFind operand.Actual with
                                | Some { Kind = SemanticKind.FieldGet _ } ->
                                    let rows =
                                        revision.Emission.Callable.AggregateValues.TryFind operand.Actual
                                        |> Option.defaultValue []
                                        |> List.filter (fun row -> row.Operation = CallableAggregateOperation.Project)
                                    match rows, revision.Emission.Callable.Carriers.TryFind entry.Formation with
                                    | [row], Some carrier ->
                                        match row.FormationInputs, row.Alternatives with
                                        | [_; formation], [alternative] ->
                                            row.Occurrence = operand.Actual && formation = entry.Formation &&
                                            alternative.Carrier = entry.Formation && alternative.Formation = entry.Formation &&
                                            carrier.Contract = Ok alternative.Contract &&
                                            revision.Emission.Callable.AggregateDependencies.ContainsKey operand.Actual
                                        | _ -> false
                                    | _ -> false
                                | Some { Kind = (SemanticKind.TupleGet _ | SemanticKind.DUEliminate _) } -> false
                                | Some _ -> true
                                | None -> false
                            if not projection then
                                yield defect "Emission.Boundary.Calls.CallbackProjection" call.Site "The projected callback argument lacks its exact original closed-entry aggregate account."
                        | _ -> yield defect "Emission.Boundary.Calls.CallbackEntry" call.Site "The callback argument lacks its exact receiving invocation and original closed-entry transport."
                    | _ -> ()
            for KeyValue(key, imported) in boundary.Imports do
                if key <> imported.Identity then
                    yield defect "Emission.Boundary.Imports.Identity" key "An import is filed under a different identity."

                yield!
                    need
                        "Emission.Boundary.Imports.Scope"
                        "SourceReadings.ContextHeaders"
                        imported.Scope
                        (revision.SourceReadings.ContextHeaders.ContainsKey imported.Scope)

                yield!
                    need
                        "Emission.Boundary.Imports.Binding"
                        "the import's DeclarationFacts"
                        imported.Binding
                        (revision.Nodes.ContainsKey imported.Binding
                         || imported.DeclarationFacts.ContainsKey imported.Binding)

                for formal, _ in imported.Parameters do
                    yield!
                        need
                            "Emission.Boundary.Imports.Parameters"
                            "the import's SourceTypes"
                            formal
                            (imported.SourceTypes.ContainsKey formal)

                for id in imported.DeclarationPath do
                    yield!
                        need
                            "Emission.Boundary.Imports.DeclarationPath"
                            "the import's DeclarationFacts or its context header"
                            id
                            (revision.Nodes.ContainsKey id
                             || imported.DeclarationFacts.ContainsKey id
                             || revision.SourceReadings.ContextHeaders.ContainsKey id)
            for KeyValue(scope, imports) in boundary.ByScope do
                for id in imports do
                    match boundary.Imports.TryFind id with
                    | Some imported when imported.Scope = scope -> ()
                    | _ -> yield missingRow "Emission.Boundary.ByScope (values)" "Imports with the declared Scope" id
            for loading in Option.toList boundary.Loading do
                let facts = loading.DeclarationFacts
                let fields = loadingFields loading

                if
                    fields |> List.exists (snd >> System.String.IsNullOrWhiteSpace)
                    || System.String.IsNullOrWhiteSpace loading.Selector
                then
                    yield
                        defect
                            "Emission.Boundary.Loading.Provenance"
                            loading.Identity
                            "The selected loading assumption has a blank selector, provenance or policy field."

                let recordMatches =
                    match facts.TryFind loading.Identity, facts.TryFind loading.Binding with
                    | Some record, Some binding when
                        record.Form = "record"
                        && binding.Form = "binding"
                        && binding.Numbers = [ 0I; 0I ]
                        && (if binding.References = [ loading.Identity ] && binding.Children = [ loading.Identity ] then
                                record.Parent = Some loading.Binding
                            else
                                match binding.References, binding.Children with
                                | [ annotation ], [ child ] when annotation = child ->
                                    match facts.TryFind annotation with
                                    | Some value ->
                                        value.Form = "annotation"
                                        && value.Text.IsEmpty
                                        && value.Numbers.IsEmpty
                                        && value.References = [ loading.Identity ]
                                        && value.Children = [ loading.Identity ]
                                        && value.Parent = Some loading.Binding
                                        && record.Parent = Some annotation
                                        && value.SourceType = record.SourceType
                                    | None -> false
                                | _ -> false)
                        && record.Text.Length = fields.Length
                        && record.References = record.Children
                        && record.References.Length = fields.Length
                        && record.Numbers.IsEmpty
                        && (Set.ofList record.Text).Count = fields.Length
                        && record.SourceType = binding.SourceType
                        ->
                        List.zip record.Text record.References
                        |> List.forall (fun (label, node) ->
                            match List.tryFind (fst >> (=) label) fields, facts.TryFind node with
                            | Some(_, value), Some fact ->
                                fact.Form = "string"
                                && fact.Text = [ value ]
                                && fact.Numbers.IsEmpty
                                && fact.References.IsEmpty
                                && fact.Children.IsEmpty
                                && fact.Parent = Some loading.Identity
                            | _ -> false)
                    | _ -> false

                if not recordMatches then
                    yield
                        defect
                            "Emission.Boundary.Loading.Contract"
                            loading.Identity
                            "The selected loading contract differs from its immutable declaration and exact eleven literal fields."

                for id in [ loading.Identity; loading.Binding; loading.Platform; loading.Core ] do
                    yield!
                        need
                            "Emission.Boundary.Loading.DeclarationFacts"
                            "the selected loading/platform/core source declaration facts"
                            id
                            (facts.ContainsKey id)

                if not (Set.isSubset (facts.Keys |> Set.ofSeq) loading.Participants) then
                    yield
                        defect
                            "Emission.Boundary.Loading.Participants"
                            loading.Identity
                            "The loading support omits a current declaration fact."
            for KeyValue(key, entry) in boundary.Entries do
                if key <> entry.Formation then
                    yield defect "Emission.Boundary.Entries.Formation" key "An imported entry is filed under a different actual formation."

                match boundary.Loading, boundary.Imports.TryFind entry.Import with
                | Some loading, Some imported when
                    entry.Loading = loading.Identity
                    && entry.Declaration = imported.Binding
                    && imported.Library = loading.Contract.Library
                    ->
                    let sourceSignature =
                        revision.Nodes.TryFind imported.Binding |> Option.map _.Type

                    let formation = revision.Nodes.TryFind entry.Formation

                    let signatureMatches =
                        match formation, entry.SourceType with
                        | Some node, TypeIdentity.Application(constructor, [ signature ]) ->
                            node.Type = entry.SourceType
                            && constructor.NativeKind = Some NTUKind.NTUfnptr
                            && sourceSignature = Some signature
                        | _ -> false

                    if not signatureMatches then
                        yield
                            defect
                                "Emission.Boundary.Entries.Signature"
                                entry.Formation
                                "The imported function pointer differs from its exact source declaration signature."

                    if
                        not (
                            entry.Transport.Contains entry.Formation
                            && entry.Transport.Contains entry.Operand
                            && entry.Transport.Contains entry.Declaration
                            && (entry.Transport |> Set.forall (transportMember entry))
                        )
                    then
                        yield
                            defect
                                "Emission.Boundary.Entries.Transport"
                                entry.Formation
                                "The imported entry lacks its exact immutable source operand transport."

                    if
                        not (
                            Set.isSubset entry.Transport entry.Participants
                            && Set.isSubset imported.Participants entry.Participants
                            && Set.isSubset loading.Participants entry.Participants
                        )
                    then
                        yield
                            defect
                                "Emission.Boundary.Entries.Participants"
                                entry.Formation
                                "The imported entry omits current import, loading or transport support."
                | _ ->
                    yield
                        defect
                            "Emission.Boundary.Entries.Account"
                            entry.Formation
                            "The imported entry differs from its exact import, original declaration or selected loading account."

                if
                    revision.Codata.FunctionPointers.TryFind entry.Formation
                    <> Some(FunctionPointerPlan.ExternAddress entry.Formation)
                then
                    yield
                        defect
                            "Emission.Boundary.Entries.Plan"
                            entry.Formation
                            "The imported entry lacks its formation-only ExternAddress plan."
            for KeyValue(site, plan) in revision.Codata.FunctionPointers do
                match plan with
                | FunctionPointerPlan.ExternAddress formation when site <> formation || not (boundary.Entries.ContainsKey formation) ->
                    yield
                        defect "Codata.FunctionPointers.ExternAddress" site "An ExternAddress plan lacks its exact actual formation entry."
                | _ -> ()
            for KeyValue(key, call) in boundary.Calls do
                if key <> call.Site then
                    yield defect "Emission.Boundary.Calls.Site" key "A boundary call is filed under a different site."

                match boundary.Imports.TryFind call.Import with
                | None -> yield missingRow "Emission.Boundary.Calls.Import" "Emission.Boundary.Imports" call.Import
                | Some imported ->
                    match call.Entry with
                    | None ->
                        match revision.Nodes.TryFind call.Site with
                        | Some {
                                   Kind = SemanticKind.Application(callee, _)
                               } when callee = call.Callee -> ()
                        | _ ->
                            yield
                                defect
                                    "Emission.Boundary.Calls.Callee"
                                    call.Callee
                                    "The call's callee differs from its live source application's callee."
                    | Some formation ->
                        let actuals = call.Arguments |> List.map _.Actual

                        let sourceCall =
                            match revision.Nodes.TryFind call.Site with
                            | Some {
                                       Kind = SemanticKind.Application(intrinsic, pointer :: arguments)
                                       Children = children
                                   } ->
                                pointer = call.Callee
                                && arguments = actuals @ call.ErasedUnitArguments
                                && children = intrinsic :: pointer :: arguments
                                && (revision.Nodes.TryFind intrinsic
                                    |> Option.exists (fun node ->
                                        match node.Kind with
                                        | SemanticKind.Intrinsic {
                                                                     Module = IntrinsicModule.FnPtr
                                                                     Operation = "invoke"
                                                                 } -> true
                                        | _ -> false))
                            | _ -> false

                        match boundary.Entries.TryFind formation with
                        | Some entry when
                            entry.Formation = formation
                            && entry.Import = call.Import
                            && entry.Transport.Contains call.Callee
                            && (call.Callee = entry.Formation || immutableRead entry call.Callee)
                            && sourceCall
                            && (call.Arguments |> List.map (fun operand -> operand.Formal, operand.Abi)) = imported.Parameters
                            && call.Result = imported.Result
                            ->
                            ()
                        | _ ->
                            yield
                                defect
                                    "Emission.Boundary.Calls.Entry"
                                    call.Site
                                    "The indirect call differs from its exact imported entry, source pointer transport or ordered native ABI."

                    yield!
                        need
                            "Emission.Boundary.Calls.Callee"
                            "Nodes (actual callee occurrence)"
                            call.Callee
                            (revision.Nodes.ContainsKey call.Callee)

                    for operand in call.Arguments do
                        if not (imported.Parameters |> List.contains (operand.Formal, operand.Abi)) then
                            yield
                                defect
                                    "Emission.Boundary.Calls.Arguments"
                                    operand.Formal
                                    "A boundary operand differs from its imported formal/ABI account."

                        yield!
                            need
                                "Emission.Boundary.Calls.Arguments"
                                "Nodes (actual operand)"
                                operand.Actual
                                (revision.Nodes.ContainsKey operand.Actual)
            // A runtime borrow requires the source-published snapshot account.
            // The memory owner already checks the exact copy and allocation rows.
            for KeyValue(_, call) in boundary.IntrinsicWrites do
                match boundary.ByteViews.TryFind call.Buffer with
                | Some view when view.StaticOrigins.IsEmpty ->
                    match memory.Operations.TryFind view.ExtentSource with
                    | Some(MemoryWitnessOperation.StringView snapshot) when
                        snapshot.Site = view.ExtentSource
                        && snapshot.Direction = MemoryStringViewDirection.FromBytes
                        ->
                        match memory.ArrayCopies.TryFind snapshot.Snapshot with
                        | Some copy when copy.Allocation.IsNone ->
                            yield
                                missingRow
                                    "Emission.Boundary.ByteViews.SnapshotAllocation"
                                    "the snapshot copy with a stated allocation"
                                    copy.Site
                        | _ -> ()
                    | _ ->
                        yield
                            missingRow
                                "Emission.Boundary.ByteViews.Snapshot"
                                "Emission.Memory.Operations with the exact FromBytes StringView"
                                view.ExtentSource
                | Some _ -> ()
                | None ->
                    yield
                        missingRow
                            "Emission.Boundary.IntrinsicWrites.Buffer"
                            "Emission.Boundary.ByteViews with the exact buffer"
                            call.Buffer
            for KeyValue(_, proofs) in boundary.IntrinsicWriteProofs do
                for proof in proofs do
                    match revision.CurrentClaims.TryFind proof.Obligation with
                    | Some claim when claim.Body = proof.Body -> ()
                    | _ ->
                        yield
                            missingRow
                                "Emission.Boundary.IntrinsicWriteProofs (values)"
                                "CurrentClaims with the exact proof body"
                                proof.Obligation
            for KeyValue(key, imported) in boundary.IntrinsicWriteImports do
                if key <> imported.Identity then
                    yield
                        defect
                            "Emission.Boundary.IntrinsicWriteImports.Identity"
                            key
                            "An intrinsic import is filed under a different identity."

                yield!
                    need
                        "Emission.Boundary.IntrinsicWriteImports.Scope"
                        "SourceReadings.ContextHeaders"
                        imported.Scope
                        (revision.SourceReadings.ContextHeaders.ContainsKey imported.Scope)
        ]

    /// Source-authored artifact correspondence is data. These comparisons do
    /// not infer scope, admit residence, or establish an arithmetic proposition.
    let private artifactAccounts (revision: Revision) : IntegrityViolation list =
        let storage = revision.Emission.Storage
        let callable = revision.Emission.Callable
        let prefix = "Emission.Storage."
        let fail table field id reason = defect (prefix + table + "." + field) id reason
        let need table field id present reason = if present then [] else [fail table field id reason]
        let vector table claim (participants: Participant list) =
            need table "Participants" claim
                (revision.ObligationSources.TryFind claim = Some [List.map (fun (p: Participant) -> p.Node) participants])
                "The current claim's grouped sources differ from its complete ordered participant vector."
        let group role owner (participants: Participant list) =
            participants |> List.filter (fun p -> p.Group = owner && p.Role = role)
        let exactAt table field owner role ordinal expected participants =
            need table field owner
                (group role owner participants = [{Node = expected; Role = role; Ordinal = ordinal; Group = owner}])
                "The participant role differs from its exact source identity, group or ordinal."
        let exact table field owner role expected participants = exactAt table field owner role 0 expected participants
        let indexed table field owner role expected participants =
            let stated = group role owner participants
            let current = expected |> List.mapi (fun ordinal node -> {Node = node; Role = role; Ordinal = ordinal; Group = owner})
            need table field owner (stated = current)
                "The ordered participant role differs from its source vector, including multiplicity."
        let body table field id predicate =
            need table field id (revision.Nodes.TryFind id |> Option.exists (fun node -> predicate node.Kind))
                "The account lacks its exact current executable operation."
        let resultParticipants (row: EnvironmentFactoryResultAccount) : Participant list =
            [ParticipantRole.EnvironmentCall, row.Call; ParticipantRole.EnvironmentFactory, row.Factory
             ParticipantRole.EnvironmentConstructor, row.Constructor; ParticipantRole.EnvironmentFormal, row.Formal
             ParticipantRole.EnvironmentAllocation, row.Allocation; ParticipantRole.EnvironmentDestination, row.Destination]
            |> List.map (fun (role, node) -> {Node = node; Role = role; Ordinal = row.Ordinal; Group = row.Call})
        let initialization table binding initializer =
            match storage.Startup with
            | Some startup when startup.ValueBindings.Contains binding ->
                startup.Initializers |> List.filter (fun row -> row.Binding = binding && row.Initializer = initializer)
                |> function
                   | [_] -> []
                   | _ -> [fail table "Initializer" binding "The account has no unique matching current startup initializer."]
            | _ -> [fail table "Binding" binding "The account's binding lacks current startup value authority."]
        [ for KeyValue(key, row) in storage.EnvironmentReservations do
              let table = "EnvironmentReservations"
              if key <> row.Claim then yield fail table "Claim" key "The reservation is filed under a different claim identity."
              match revision.CurrentClaims.TryFind row.Claim with
              | Some claim when claim.Kind = "environment-storage-reservation" ->
                  match claim.Body with
                  | ObligationBody.EnvironmentStorageReservation _ -> ()
                  | _ -> yield fail table "Claim" row.Claim "The current claim has a different obligation body family."
              | _ -> yield fail table "Claim" row.Claim "The reservation has no matching current claim family."
              yield! vector table row.Claim row.Participants
              yield! exact table "Allocation" row.Allocation ParticipantRole.EnvironmentAllocation row.Allocation row.Participants
              yield! exact table "Binding" row.Allocation ParticipantRole.EnvironmentBinding row.Binding row.Participants
              yield! exact table "Initializer" row.Allocation ParticipantRole.EnvironmentInitializer row.Initializer row.Participants
              yield! body table "Allocation" row.Allocation (function SemanticKind.EnvironmentAllocate _ | SemanticKind.EnvironmentCreate _ -> true | _ -> false)
              yield! need table "Initializer" row.Initializer (revision.Nodes.ContainsKey row.Initializer)
                  "The reservation initializer has no current executable body."
              let baseParticipants = row.Participants |> List.filter (fun p -> p.Group = row.Allocation)
              let allowed =
                  Set.ofList [ParticipantRole.EnvironmentAllocation; ParticipantRole.EnvironmentBinding; ParticipantRole.EnvironmentInitializer
                              ParticipantRole.EnvironmentOwner; ParticipantRole.EnvironmentImplementation; ParticipantRole.EnvironmentConstructor
                              ParticipantRole.EnvironmentFormal; ParticipantRole.EnvironmentLayoutProof; ParticipantRole.EnvironmentSpace
                              ParticipantRole.EnvironmentAuthorityInput; ParticipantRole.EnvironmentDeclarationInput]
              for p in baseParticipants do
                  if p.Ordinal < 0 || not (allowed.Contains p.Role) then
                      yield fail table "Participants" row.Claim "A reservation participant has an invalid source role or negative ordinal."
              let roles = baseParticipants |> List.map _.Role
              let orderedRoles = allowed |> Set.toList
              let rank role =
                  [ParticipantRole.EnvironmentAllocation; ParticipantRole.EnvironmentBinding; ParticipantRole.EnvironmentInitializer
                   ParticipantRole.EnvironmentOwner; ParticipantRole.EnvironmentImplementation; ParticipantRole.EnvironmentConstructor
                   ParticipantRole.EnvironmentFormal; ParticipantRole.EnvironmentLayoutProof; ParticipantRole.EnvironmentSpace
                   ParticipantRole.EnvironmentAuthorityInput; ParticipantRole.EnvironmentDeclarationInput]
                  |> List.tryFindIndex ((=) role) |> Option.defaultValue orderedRoles.Length
              if roles <> (roles |> List.sortBy rank) then
                  yield fail table "Participants" row.Claim "The reservation's source roles are not in their authored order."
              for role in [ParticipantRole.EnvironmentOwner; ParticipantRole.EnvironmentImplementation; ParticipantRole.EnvironmentConstructor
                           ParticipantRole.EnvironmentFormal; ParticipantRole.EnvironmentSpace] do
                  match group role row.Allocation row.Participants with
                  | [] | [{Ordinal = 0}] -> ()
                  | _ -> yield fail table "Participants" row.Claim "A singleton allocation role has repeated occurrences or a nonzero ordinal."
              for role in [ParticipantRole.EnvironmentLayoutProof; ParticipantRole.EnvironmentAuthorityInput; ParticipantRole.EnvironmentDeclarationInput] do
                  let stated = group role row.Allocation row.Participants
                  if List.map (fun (p: Participant) -> p.Ordinal) stated <> [0 .. stated.Length - 1] then
                      yield fail table "Participants" row.Claim "An ordered allocation role has noncontiguous or reordered source ordinals."
              let calls = row.Participants |> List.filter (fun p -> p.Group <> row.Allocation) |> List.groupBy _.Group
              for call, participants in calls do
                  match storage.EnvironmentFactoryResults.TryFind call with
                  | Some result when result.Allocation = row.Allocation && participants = resultParticipants result -> ()
                  | _ -> yield fail table "Participants" row.Claim "A factory-call participant group differs from its exact current result account."
              let expectedCalls = storage.EnvironmentFactoryResults |> Map.toList |> List.filter (fun (_, result) -> result.Allocation = row.Allocation) |> List.map fst |> Set.ofList
              if (calls |> List.map fst |> Set.ofList) <> expectedCalls then
                  yield fail table "Participants" row.Claim "The reservation omits or adds a current factory-result call group."
          for KeyValue(key, row) in storage.EnvironmentFactoryResults do
              let table = "EnvironmentFactoryResults"
              if key <> row.Call then yield fail table "Call" key "The factory result is filed under a different actual call identity."
              if row.Ordinal < 0 then yield fail table "Ordinal" row.Call "The source result occurrence ordinal is negative."
              yield! body table "Call" row.Call (function SemanticKind.Application _ -> true | _ -> false)
              yield! body table "Allocation" row.Allocation (function SemanticKind.EnvironmentAllocate _ -> true | _ -> false)
              yield! need table "Destination" row.Destination (revision.Nodes.ContainsKey row.Destination)
                  "The realized destination lacks its current executable occurrence."
              match callable.Calls.TryFind row.Call with
              | Some call when call.Site = row.Call && call.Implementation = row.Factory ->
                  let parameters = call.Parameters |> List.map (fun (_, _, formal) -> formal)
                  let pairs = List.zip (parameters |> List.truncate call.Arguments.Length) (call.Arguments |> List.truncate parameters.Length)
                  if parameters.Length <> call.Arguments.Length || (pairs |> List.filter (fun (formal, _) -> formal = row.Formal)) <> [row.Formal, row.Destination] then
                      yield fail table "Formal" row.Call "The factory's exact formal/actual pair differs from the realized destination."
              | _ -> yield fail table "Factory" row.Call "The actual call lacks the exact realized factory implementation."
              yield! need table "Formal" row.Constructor
                  (revision.Codata.EnvironmentDestinations.TryFind row.Constructor = Some row.Formal)
                  "The constructor destination differs from the factory-result formal."
          for KeyValue(key, row) in storage.EnvironmentResidences do
              let table = "EnvironmentResidences"
              if key <> row.Allocation then yield fail table "Allocation" key "The residence is filed under a different allocation identity."
              match storage.EnvironmentReservations.TryFind row.ReservationClaim with
              | Some reservation when reservation.Claim = row.ReservationClaim && reservation.Allocation = row.Allocation && reservation.Binding = row.Binding ->
                  yield! exact table "Owner" row.Allocation ParticipantRole.EnvironmentOwner row.Owner reservation.Participants
                  yield! exact table "Implementation" row.Allocation ParticipantRole.EnvironmentImplementation row.Implementation reservation.Participants
                  yield! exact table "Formal" row.Allocation ParticipantRole.EnvironmentFormal row.Formal reservation.Participants
                  yield! indexed table "LayoutClaims" row.Allocation ParticipantRole.EnvironmentLayoutProof row.LayoutClaims reservation.Participants
                  yield! indexed table "AuthorityInputs" row.Allocation ParticipantRole.EnvironmentAuthorityInput row.AuthorityInputs reservation.Participants
                  yield! indexed table "DeclarationInputs" row.Allocation ParticipantRole.EnvironmentDeclarationInput row.DeclarationInputs reservation.Participants
                  yield! initialization table row.Binding reservation.Initializer
                  match storage.ProgramStorage.Entries.TryFind(ProgramStorageIdentity.Allocation row.Allocation), revision.CurrentClaims.TryFind row.ReservationClaim with
                  | Some entry, Some claim ->
                      if entry.Identity <> ProgramStorageIdentity.Allocation row.Allocation || entry.Shape <> ProgramStorageShape.Bytes then
                          yield fail table "Allocation" row.Allocation "The admitted allocation lacks its exact byte storage entry."
                      yield! exact table "Space" row.Allocation ParticipantRole.EnvironmentSpace entry.SpaceNode reservation.Participants
                      if claim.Body <> ObligationBody.EnvironmentStorageReservation(Some entry.Bytes, Some entry.Alignment, Some entry.Space.Capacity, Some entry.Space.Alignment, Some entry.Space.Granularity) then
                          yield fail table "ReservationClaim" row.ReservationClaim "The admitted reservation formula differs from its exact storage extent, alignment or declared space."
                      match revision.Codata.EnvironmentLayouts.TryFind row.Owner with
                      | Some layout when layout.Owner = row.Owner && layout.Implementation = row.Implementation && layout.Formal = row.Formal && layout.Obligations = row.LayoutClaims && layout.Bytes = entry.Bytes && layout.Alignment = entry.Alignment -> ()
                      | _ -> yield fail table "Owner" row.Owner "The admitted residence differs from its exact current environment layout."
                  | _ -> yield fail table "ReservationClaim" row.ReservationClaim "The admitted residence lacks its exact current storage entry and claim."
              | _ -> yield fail table "ReservationClaim" row.ReservationClaim "The admitted residence lacks its exact reservation account."
              match callable.ProgramInstances.TryFind row.Binding with
              | Some instance when instance.Allocation = Some row.Allocation && instance.Carrier.Implementation = row.Implementation &&
                                   instance.Carrier.Environment = Some {Owner = row.Owner; Formal = row.Formal} && instance.Participants.Contains row.Allocation -> ()
              | _ -> yield fail table "Binding" row.Binding "The residence differs from its exact initialized program instance."
              yield! body table "Allocation" row.Allocation (function SemanticKind.EnvironmentAllocate owner | SemanticKind.EnvironmentCreate(owner, _) -> owner = row.Owner | _ -> false)
              yield! need table "ProgramInitializationOrders" row.Binding (storage.ProgramInitializationOrders.ContainsKey row.Binding)
                  "The admitted residence lacks a current initialization order account."
              match storage.EnvironmentReservations.TryFind row.ReservationClaim with
              | Some reservation when List.tryHead row.BindingPath = Some row.Allocation && List.contains reservation.Initializer row.BindingPath -> ()
              | _ -> yield fail table "BindingPath" row.Binding "The source residence path omits its allocation or exact initializer."
          for KeyValue(key, row) in storage.ProgramInitializationOrders do
              let table = "ProgramInitializationOrders"
              if key <> row.Binding then yield fail table "Binding" key "The order account is filed under a different binding identity."
              yield! vector table row.Claim row.Participants
              yield! exact table "Binding" row.Binding ParticipantRole.InitializationBinding row.Binding row.Participants
              match revision.CurrentClaims.TryFind row.Claim, storage.Startup with
              | Some claim, Some startup when claim.Kind = "program-initialization-order" && startup.ValueBindings.Contains row.Binding ->
                  match startup.Initializers |> List.filter (fun initializer -> initializer.Binding = row.Binding) with
                  | [initializer] ->
                      yield! exactAt table "Initializer" row.Binding ParticipantRole.InitializationValue initializer.Ordinal initializer.Initializer row.Participants
                      yield! exactAt table "Spine" row.Binding ParticipantRole.InitializationSpine initializer.Ordinal startup.Spine row.Participants
                      yield! exactAt table "Entry" row.Binding ParticipantRole.InitializationEntry initializer.Ordinal startup.EntryLambda row.Participants
                      let initial =
                          [{Node = row.Binding; Role = ParticipantRole.InitializationBinding; Ordinal = 0; Group = row.Binding}
                           {Node = startup.EntryLambda; Role = ParticipantRole.InitializationEntry; Ordinal = initializer.Ordinal; Group = row.Binding}
                           {Node = startup.Spine; Role = ParticipantRole.InitializationSpine; Ordinal = initializer.Ordinal; Group = row.Binding}
                           {Node = initializer.Initializer; Role = ParticipantRole.InitializationValue; Ordinal = initializer.Ordinal; Group = row.Binding}]
                      if List.truncate 4 row.Participants <> initial then
                          yield fail table "Participants" row.Claim "The initial source reading roles are not in their authored order."
                      let phases = row.Participants |> List.filter (fun p -> p.Role = ParticipantRole.InitializationPhase)
                      if claim.Body <> ObligationBody.ProgramInitializationOrder(initializer.Ordinal, startup.Initializers.Length, List.map (fun (p: Participant) -> p.Ordinal) phases) then
                          yield fail table "Claim" row.Claim "The current order formula differs from its exact startup ordinal, count or complete ordered phases."
                      for phase in phases do
                          let root = if phase.Ordinal = startup.Initializers.Length then Some startup.EntryCall else startup.Initializers |> List.tryFind (fun i -> i.Ordinal = phase.Ordinal) |> Option.map _.Binding
                          if root <> Some phase.Node then yield fail table "Participants" row.Claim "An initialization phase names a different current startup root."
                  | _ -> yield fail table "Binding" row.Binding "The order account lacks one exact current startup initializer."
              | _ -> yield fail table "Claim" row.Claim "The order account lacks its current claim family or startup value authority."
              for p in row.Participants do
                  if p.Ordinal < 0 then yield fail table "Participants" row.Claim "An initialization participant has a negative source ordinal."
                  match p.Role with
                  | ParticipantRole.InitializationBinding | ParticipantRole.InitializationValue | ParticipantRole.InitializationSpine
                  | ParticipantRole.InitializationEntry | ParticipantRole.InitializationUse | ParticipantRole.InitializationScope
                  | ParticipantRole.InitializationParent | ParticipantRole.InitializationPhase | ParticipantRole.InitializationCaller
                  | ParticipantRole.InitializationCallee | ParticipantRole.InitializationPremise -> ()
                  | _ -> yield fail table "Participants" row.Claim "The initialization account contains a participant of a different source family."
                  if p.Role = ParticipantRole.InitializationUse then
                      yield! need table "Participants" p.Node (revision.Nodes.ContainsKey p.Node)
                          "An actual initialization use has no current executable occurrence."
                      match revision.SourceReadings.BindingUses.TryFind p.Node with
                      | Some bindingUse when bindingUse.Binding <> row.Binding -> yield fail table "Participants" p.Node "An initialization read names a different current binding."
                      | _ -> ()
          for KeyValue(binding, instance) in callable.ProgramInstances do
              yield! need "ProgramInitializationOrders" "Binding" binding (storage.ProgramInitializationOrders.ContainsKey binding)
                  "An initialized callable instance lacks its current order account."
              for allocation in Option.toList instance.Allocation do
                  yield! need "EnvironmentResidences" "Allocation" allocation
                      (storage.EnvironmentResidences.TryFind allocation |> Option.exists (fun residence ->
                          residence.Allocation = allocation && residence.Implementation = instance.Carrier.Implementation &&
                          instance.Carrier.Environment = Some {Owner = residence.Owner; Formal = residence.Formal} &&
                          instance.Participants.Contains residence.Binding && instance.Participants.Contains allocation))
                      "An initialized callable instance lacks the exact source-admitted residence for its allocation." ]

    /// Exhaustive generated positions retain an explicit role. A typed fact can
    /// justify only the role it declares; it is never added to a universal set of
    /// resident identities. Mixed nested rows are checked separately above.
    let private roleAbsent (revision: Revision) =
        let source = revision.SourceReadings
        let callable = revision.Emission.Callable
        let body id = revision.Nodes.ContainsKey id
        let binding id = source.BindingUses |> Map.exists (fun _ bindingUse -> bindingUse.Binding = id)
        let signature id =
            callable.SignatureData |> Map.exists (fun _ ids -> ids.Contains id) ||
            callable.Declarations |> Map.exists (fun _ row -> row.Result = id || row.Parameters |> List.exists (fun (_, _, formal) -> formal = id))
        let moduleUnit id =
            source.ContextHeaders.TryFind id |> Option.exists (fun header -> header.Identity = id && header.Ports.ContainsKey OccurrencePort.ModuleDeclaration) &&
            callable.UnitNodes.Contains id && callable.ClosedData.Contains id &&
            callable.ValueShapes.TryFind id = Some(CallableValueShape.Data id) && callable.AliasTargets.TryFind id = Some id &&
            revision.Emission.Numeric.OccurrenceRepresentations.TryFind id = Some(Ok(ValueRepresentation.Scalar SettledSlot.Unit)) &&
            (match revision.Emission.Numeric.SourceTypes.TryFind id with
             | Some(TypeIdentity.Application(constructor, [])) -> constructor.NativeKind = Some NTUKind.NTUunit
             | _ -> false)
        let boundary = revision.Emission.Boundary
        let declarationFact id = boundary.Imports |> Map.exists (fun _ imported -> imported.DeclarationFacts.ContainsKey id)
        let boundaryType id = boundary.Imports |> Map.exists (fun _ imported -> imported.SourceTypes.ContainsKey id)
        let loadingFact id = boundary.Loading |> Option.exists (fun loading -> loading.DeclarationFacts.ContainsKey id)
        let loadingSupport id = body id || loadingFact id || source.ContextHeaders.ContainsKey id
        let entryDeclaration id = boundary.Entries |> Map.exists (fun _ entry ->
            entry.Declaration = id && (boundary.Imports.TryFind entry.Import |> Option.exists (fun imported ->
                imported.Binding = id && (body id || imported.DeclarationFacts.ContainsKey id))))
        let entryLoading id = boundary.Entries |> Map.exists (fun _ entry ->
            entry.Loading = id && (boundary.Loading |> Option.exists (fun loading -> loading.Identity = id && loadingFact id)))
        let entrySupport id = body id || loadingFact id || declarationFact id || boundaryType id
        let foreignBodyFact id =
            revision.CurrentClaims
            |> Map.exists (fun _ claim ->
                match claim.Body with
                | ObligationBody.ForeignResultCoverage model -> foreignClaimFact revision model id
                | _ -> false)

        let declarationType id =
            boundary.Imports |> Map.exists(fun _ imported ->
                imported.DeclarationFacts.TryFind id |> Option.exists(fun fact ->
                    revision.Emission.Numeric.SourceTypes.TryFind id = Some fact.SourceType &&
                    revision.Emission.Numeric.OccurrenceRepresentations.ContainsKey id &&
                    callable.ValueShapes.TryFind id = Some(CallableValueShape.Data id) &&
                    callable.AliasTargets.TryFind id = Some id && callable.ClosedData.Contains id))
        let referencedData id =
            let reader owner = body owner || binding owner || signature owner
            let referenced =
                callable.ValueShapes |> Map.exists(fun owner shape -> owner <> id && reader owner && shape = CallableValueShape.Data id) ||
                callable.AliasTargets |> Map.exists(fun owner target -> owner <> id && reader owner && target = id)
            referenced && callable.ValueShapes.TryFind id = Some(CallableValueShape.Data id) &&
            callable.AliasTargets.TryFind id = Some id && callable.ClosedData.Contains id &&
            revision.Emission.Numeric.SourceTypes.ContainsKey id &&
            (match revision.Emission.Numeric.OccurrenceRepresentations.TryFind id with Some(Ok _) -> true | _ -> false)
        let typeFact id =
            body id || binding id || signature id || moduleUnit id || declarationType id || referencedData id
        let implementation id = callable.Symbols.ContainsKey id
        let explicitParts =
            Set.ofList [ "Nodes.Kind"; "Nodes.Children"; "Nodes.Parent"; "Codata.WitnessSegmentation.Regions"
                         "CurrentClaims"; "ObligationSources"; "ObligationSources (values)"
                         "Emission.Storage.Lazies.Layout"; "Edges.Sources"; "Edges.Target"; "Edges.Role"
                         "Emission.Numeric.Operations.Operands"; "Emission.Numeric.Operations.Result"
                         "Emission.Numeric.Operations.ResultAdaptation"
                         "Emission.Memory.Operations (values)"; "Emission.Memory.ArrayCopies.CountCarrier"
                         "Emission.Memory.ArrayCopies.Read"; "Emission.Memory.ArrayCopies.Write"; "Emission.Memory.ArrayCopies.Requirements"
                         "Codata.ProgramStorage.Entries.SpaceNode"; "Codata.ProgramStorage.Reservations"
                         "Emission.Storage.ProgramStorage.Entries.SpaceNode"; "Emission.Storage.ProgramStorage.Reservations"
                         "Emission.Spatial.Kernels.Steps"; "Emission.Spatial.Kernels.Ingress"; "Emission.Spatial.Kernels.Target"
                         "Emission.Spatial.Kernels.MetadataOnly"; "Emission.Spatial.Hardware.MetadataOnly"; "Emission.Spatial.MetadataOnly"
                         "Emission.Spatial.Hardware.InputPorts"; "Emission.Spatial.Hardware.OutputPorts"
                         "Emission.Spatial.Hardware.ResetFields"; "Emission.Spatial.Hardware.ClockDeclaration"
                         "Emission.Spatial.Hardware.ClockReference"
                         "Emission.Spatial.Hardware.ResetDeclaration"; "Emission.Spatial.Hardware.ClockPath"
                         "Emission.Storage.Startup.Initializers"
                         // callableRows checks the complete embedded row
                         // against its canonical carrier and exact contract.
                         "Emission.Callable.ProgramInstances.Carrier"
                         "Emission.Boundary.IntrinsicWriteImports.Scope"
                         "Emission.Boundary.Calls.Arguments"; "Emission.Boundary.IntrinsicWriteProofs (values)"
                         "Emission.Numeric.ForeignResultUses.Claims"
                         "Emission.Boundary.Imports.DeclarationFacts"
                         "Emission.Boundary.Loading.DeclarationFacts" ]
        let supportParts =
            Set.ofList [ "Emission.Callable.Supports (values)"; "Emission.Callable.Declarations.Participants"
                         "Emission.Callable.Calls.Participants"; "Emission.Callable.ProgramInstances.Participants"
                         "Codata.SequenceFamilies.Participants"; "Codata.ProgramStorage.Entries.Participants"
                         "Emission.Storage.ProgramStorage.Entries.Participants"; "Emission.Storage.SequencePrograms.Participants"
                         "Emission.Storage.Requirements.Participants"; "Emission.Boundary.Imports.Participants"
                         "Emission.Boundary.Calls.Participants"; "Emission.Boundary.ByteViews.Participants"
                         "Emission.Boundary.StringExtents.Participants"; "Emission.Boundary.IntrinsicWriteImports.Participants"
                         "Emission.Boundary.IntrinsicWrites.Participants"; "Emission.Numeric.Values.Participants"
                         "Emission.Numeric.Operations.Participants"; "Emission.Numeric.IndexTransports.Participants"
                         "Emission.Numeric.ForeignResultUses.Participants"
                         "Emission.Memory.ArrayCopies.Participants"; "Emission.Spatial.Hardware.Participants"
                         "Emission.Spatial.Kernels.Participants"; "Codata.CallableBranches.Observations.Participants"
                         "Emission.Callable.Branches.Observations.Participants"
                         "Emission.Storage.EnvironmentReservations.Participants"
                         "Emission.Storage.ProgramInitializationOrders.Participants"
                         "Emission.Storage.EnvironmentResidences.AuthorityInputs"
                         "Emission.Storage.EnvironmentResidences.BindingPath"
                         "Emission.Storage.EnvironmentResidences.DeclarationInputs"
                         "Emission.Boundary.Loading.Participants"; "Emission.Boundary.Entries.Participants" ]
        let role (part: string) (id: NodeId) =
            // These mixed row/source identities are checked with their typed
            // roles by callableAggregates. Row identity is not a runtime body.
            let aggregatePart =
                ["Emission.Callable.Aggregate"; "Codata.CallableAggregate";
                 "Emission.Callable.Contracts"; "Codata.CallableContracts"]
                |> List.exists (fun prefix -> part.StartsWith(prefix, System.StringComparison.Ordinal))
            let inactivityPart = part.StartsWith("Emission.Ordinary.Inactivity", System.StringComparison.Ordinal)
            if explicitParts.Contains part || supportParts.Contains part || aggregatePart || inactivityPart || part.StartsWith("SourceReadings.", System.StringComparison.Ordinal) then true
            else
                match part with
                | "Emission.Boundary.CallbackInvocations" | "Emission.Boundary.CallbackInvocations.Identity"
                | "Emission.Boundary.ClosedEntries.Invocation" -> boundary.CallbackInvocations.ContainsKey id
                | "Emission.Boundary.CallbackInvocations.Import" -> boundary.Imports.ContainsKey id
                | "Emission.Boundary.CallbackInvocations.Formal" -> boundaryType id
                | "Emission.Boundary.CallbackInvocations.Scope" ->
                    boundary.CallbackInvocations.Values |> Seq.exists (fun invocation ->
                        invocation.Scope = id && (boundary.Imports.TryFind invocation.Import |> Option.exists (fun imported -> imported.DeclarationFacts.ContainsKey id)))
                | "Emission.Boundary.ClosedEntries" | "Emission.Boundary.ClosedEntries.Formation"
                | "Emission.Boundary.ClosedEntries.Operand" -> body id
                | "Emission.Boundary.ClosedEntries.Declaration" -> binding id || implementation id
                | "Emission.Boundary.ClosedEntries.Implementation" -> implementation id
                | "Emission.Boundary.ClosedEntries.Formals" | "Emission.Boundary.ClosedEntries.Body" -> typeFact id
                | "Emission.Boundary.ClosedEntries.Transport" -> body id || binding id || implementation id
                | "Emission.Boundary.ClosedEntries.Lifetime" ->
                    callable.Contracts.Values |> Seq.exists (fun contract ->
                        match contract.Convention with
                        | CallableConvention.CompilerOwnedPortable convention ->
                            List.contains id [convention.CodeLifetime.Module; convention.CodeLifetime.Binding; convention.CodeLifetime.Implementation]
                        | _ -> false)
                | "Emission.Boundary.ClosedEntries.Participants" when
                    boundary.ClosedEntries.Values |> Seq.exists (fun entry ->
                        entry.Participants.Contains id &&
                        (callable.Carriers.TryFind entry.Formation |> Option.exists (fun carrier -> carrier.Contract = Ok id)) &&
                        callable.Contracts.ContainsKey id) -> true
                | "Emission.Boundary.CallbackInvocations.Participants" | "Emission.Boundary.ClosedEntries.Participants" ->
                    body id || typeFact id || implementation id || source.ContextHeaders.ContainsKey id || declarationFact id || boundary.Imports.ContainsKey id
                | "Emission.Boundary.Loading.Identity" | "Emission.Boundary.Loading.Binding"
                | "Emission.Boundary.Loading.Platform" | "Emission.Boundary.Loading.Core" -> loadingFact id
                | "Emission.Boundary.Loading.DeclarationFacts" | "Emission.Boundary.Loading.Participants" -> loadingSupport id
                | "Emission.Boundary.Entries" | "Emission.Boundary.Entries.Formation"
                | "Emission.Boundary.Entries.Operand" -> body id
                | "Emission.Boundary.Entries.Import" -> boundary.Imports.ContainsKey id
                | "Emission.Boundary.Entries.Declaration" -> entryDeclaration id
                | "Emission.Boundary.Entries.Loading" -> entryLoading id
                | "Emission.Boundary.Entries.Transport" | "Emission.Boundary.Entries.Participants" -> entrySupport id
                | "Emission.Boundary.Calls.Entry" -> boundary.Entries.ContainsKey id
                | "Emission.Callable.Carriers.Contract" | "Codata.CallableCarriers.Contract" -> callable.Contracts.ContainsKey id
                | "Emission.Callable.Carriers.Lifetime" | "Codata.CallableCarriers.Lifetime" -> true
                | "Emission.Numeric.OccurrenceRepresentations (values)" | "Emission.Numeric.TypeRepresentations (values)" -> callable.AggregateSlots.ContainsKey id
                | "Emission.Numeric.SourceTypes" | "Emission.Numeric.OccurrenceRepresentations"
                | "Emission.Callable.ValueShapes" | "Emission.Callable.ValueShapes (values)"
                | "Emission.Callable.AliasTargets" | "Emission.Callable.AliasTargets (values)"
                | "Emission.Callable.Supports" | "Emission.Callable.UnitNodes" | "Emission.Callable.ClosedData" -> typeFact id || boundaryType id
                | "ModuleClassifications" | "Emission.Boundary.ByScope"
                | "Emission.Spatial.ByScope" -> body id || source.ContextHeaders.ContainsKey id
                | "Emission.Callable.SignatureData" -> body id || callable.Declarations.ContainsKey id || callable.Carriers.ContainsKey id
                | "Emission.Callable.SignatureData (values)" | "Emission.Callable.Calls.SignatureData"
                | "Emission.Callable.Calls.Parameters" | "Emission.Callable.Calls.Result"
                | "Emission.Callable.Declarations.Parameters" | "Emission.Callable.Declarations.Result"
                | "Emission.Callable.Carriers.Parameters" | "Emission.Callable.Carriers.Result"
                | "Emission.Callable.Carriers.ParameterShapes" | "Emission.Callable.Carriers.ResultShape"
                | "Codata.CallableCarriers.Parameters" | "Codata.CallableCarriers.Result"
                | "Codata.CallableCarriers.ParameterShapes" | "Codata.CallableCarriers.ResultShape"
                | "Emission.Callable.Carriers.OmittedParameters" | "Codata.CallableCarriers.OmittedParameters"
                | "Emission.Callable.Arguments (values)" -> typeFact id
                | "Emission.Callable.Declarations" | "Emission.Callable.Declarations.Lookup"
                | "Emission.Callable.Declarations.Implementation"
                | "Emission.Callable.Symbols"
                | "Emission.Callable.Carriers.Implementation" | "Codata.CallableCarriers.Implementation"
                | "Codata.KnownCallables.Implementation" | "Emission.Callable.DirectCallees (values)"
                | "Emission.Storage.DefinitionOnlyThunks" | "Emission.Callable.DefinitionOnlyLambdas" -> body id || implementation id
                | "Emission.Callable.FunctionBindings" | "Emission.Callable.DefinitionOnlyBindings"
                | "Emission.Callable.Symbols (values)" | "Emission.Callable.Declarations.Name"
                    -> body id || binding id || implementation id
                | "Codata.Curry.PartialApplications.TargetBindingId" | "Codata.Curry.SaturatedCalls.TargetBindingId" -> body id || binding id
                | "Emission.Callable.Declarations.Parent" -> body id || source.ContextHeaders.ContainsKey id
                | "Emission.Boundary.Imports" | "Emission.Boundary.Imports.Identity" -> boundary.Imports.ContainsKey id
                | "Emission.Boundary.Imports.Binding" | "Emission.Boundary.Imports.DeclarationPath"
                | "Emission.Boundary.ResultHypotheses.Declaration"
                | "Emission.Boundary.DeclarationLeaves" | "Emission.Boundary.DeclarationOnly" -> body id || declarationFact id || boundaryType id || source.ContextHeaders.ContainsKey id
                | "Emission.Boundary.Imports.Scope" -> source.ContextHeaders.ContainsKey id
                | "Emission.Boundary.ResultHypotheses.Quote" ->
                    boundary.ResultHypotheses
                    |> List.exists (fun hypothesis -> foreignHypothesisFact revision hypothesis id)
                | "Emission.Numeric.ForeignResultUses.Application" ->
                    revision.Emission.Numeric.ForeignResultUses
                    |> List.exists (fun account -> foreignApplicationFact revision account.Application id)
                | "Obligations.Body.ForeignResultCoverage"
                | "CurrentClaims.Body.ForeignResultCoverage" -> body id || foreignBodyFact id
                | "Obligations.Body"
                | "CurrentClaims.Body" -> body id
                | "Emission.Boundary.IntrinsicWriteImports.Scope" -> source.ContextHeaders.ContainsKey id
                | "Emission.Boundary.Imports.Parameters" -> boundaryType id || boundary.CallbackInvocations.ContainsKey id
                | "Emission.Boundary.Imports.SourceTypes" -> boundaryType id
                | "Emission.Boundary.ByScope (values)" | "Emission.Boundary.Calls.Import" -> boundary.Imports.ContainsKey id
                | "Emission.Spatial.Kernels.Scope" | "Emission.Spatial.Hardware.Scope" -> body id || source.ContextHeaders.ContainsKey id
                | "Emission.Boundary.Calls.Callee" -> body id
                | "Emission.Boundary.Calls.SourceTypes" -> body id || boundaryType id
                // These declaration handles accompany the selected numeric or
                // byte-pool fact; no consumer dereferences their source body.
                | "Emission.Numeric.Values.Declaration" | "Emission.Numeric.Operations.Declaration"
                | "Emission.Numeric.IndexTransports.PointerDeclaration" | "StaticStringPool.DeclarationNode"
                | "Emission.Boundary.ByteViews.RepresentationDeclaration"
                | "Emission.Boundary.IntrinsicWriteImports.Core" | "Emission.Boundary.IntrinsicWriteImports.ReturnContract"
                | "Emission.Boundary.IntrinsicWriteImports.Endpoint" | "Emission.Boundary.IntrinsicWriteImports.Surface" -> true
                | "Codata.EnvironmentLayouts.Obligations" | "Codata.LazyLayouts.Obligations"
                | "Codata.ContinuationFrames.Obligations" | "Emission.Numeric.Values.Obligations"
                | "Emission.Numeric.Operations.Obligations" | "Emission.Numeric.IndexTransports.Obligation"
                | "Emission.Spatial.Hardware.Obligations" | "Emission.Spatial.Kernels.Obligations" -> revision.CurrentClaims.ContainsKey id
                | "Emission.Storage.EnvironmentReservations" | "Emission.Storage.EnvironmentReservations.Claim"
                | "Emission.Storage.ProgramInitializationOrders.Claim"
                | "Emission.Storage.EnvironmentResidences.ReservationClaim"
                | "Emission.Storage.EnvironmentResidences.LayoutClaims" -> revision.CurrentClaims.ContainsKey id
                | "Emission.Storage.EnvironmentReservations.Binding" | "Emission.Storage.EnvironmentResidences.Binding"
                | "Emission.Storage.ProgramInitializationOrders" | "Emission.Storage.ProgramInitializationOrders.Binding" -> body id || binding id
                | "Emission.Storage.EnvironmentFactoryResults.Factory"
                | "Emission.Storage.EnvironmentResidences.Implementation" -> implementation id
                | "Emission.Storage.EnvironmentFactoryResults.Formal"
                | "Emission.Storage.EnvironmentResidences.Formal" -> typeFact id
                | "Emission.Storage.EnvironmentResidences.Owner" -> revision.Codata.EnvironmentLayouts.ContainsKey id
                | "Emission.Storage.EnvironmentFactoryResults.Constructor" -> revision.Codata.EnvironmentDestinations.ContainsKey id && body id
                | _ -> body id
        let stored =
            named revision
            |> List.collect (fun (part, ids) ->
                ids |> List.distinct |> List.filter (fun id -> not (role part id)) |> List.map (missingBody part))
        let kinds =
            revision.Nodes |> Map.toList |> List.collect (fun (site, node) ->
                let kindIds =
                    IntegrityNamed.named { Revision.empty revision.Header.Producer with Nodes = Map.ofList [site, node] }
                    |> List.find (fun (part, _) -> part = "Nodes.Kind") |> snd |> List.distinct
                let bindingUse id =
                    match node.Kind with
                    | SemanticKind.VarRef(_, Some target) when id = target ->
                        source.BindingUses.TryFind site |> Option.exists (fun bindingUse -> bindingUse.Binding = target && not (System.String.IsNullOrWhiteSpace bindingUse.Name))
                    | _ -> false
                let omittedChild id =
                    source.Children.TryFind site |> Option.defaultValue []
                    |> List.exists (fun child ->
                        match child.Traversal with
                        | ChildTraversal.SourceOmitted(_, target) | ChildTraversal.EnterImported(_, _, target) -> target = id
                        | _ -> false)
                kindIds |> List.choose (fun id ->
                    match node.Kind with
                    | SemanticKind.VarRef(_, Some target) when id = target ->
                        if bindingUse id then None else Some(missingRow "Nodes.Kind" "SourceReadings.BindingUses (matching reference)" target)
                    | _ when body id || omittedChild id -> None
                    | _ -> Some(missingBody "Nodes.Kind" id)))
        let edges =
            revision.Edges |> List.collect (fun edge ->
                let exactRows =
                    match edge.Role with
                    | EdgeRole.Constrains ->
                        if revision.CurrentClaims.ContainsKey edge.Target then [] else [missingRow "Edges.Target" "CurrentClaims" edge.Target]
                    | EdgeRole.OrdinaryInactiveImplementation ->
                        match revision.Emission.Ordinary.Inactivity.TryFind edge.Target with
                        | Some proof ->
                            let expected = [proof.Entry; proof.Body] @ proof.Parameters @ (proof.Uses |> Map.keys |> Seq.toList) @ Set.toList proof.Excluded @ Set.toList proof.Calls
                            if edge.Class = EdgeClass.Demand && edge.Ordinal = proof.Parameters.Length && edge.Sources = expected then []
                            else [defect "Edges" edge.Target "The inactive execution relation differs from its typed source row."]
                        | None -> [missingRow "Edges.Target" "Emission.Ordinary.Inactivity" edge.Target]
                    | EdgeRole.StringByteView view ->
                        [if edge.Target <> view.Site then yield defect "Edges.Target" edge.Target "The byte-view edge target differs from its typed site."
                         if not (body view.Site) then yield missingBody "Edges.Target" view.Site
                         for id in [view.Source; view.ExtentSource] do
                             if not (typeFact id) then yield missingRow "Edges.Role" "live operand or callable signature data" id]
                    | EdgeRole.StringExtent extent ->
                        [if edge.Target <> extent.Site then yield defect "Edges.Target" edge.Target "The extent edge target differs from its typed site."
                         if not (body extent.Site) then yield missingBody "Edges.Target" extent.Site
                         for id in [extent.Source; extent.ExtentSource] do
                             if not (typeFact id) then yield missingRow "Edges.Role" "live operand or callable signature data" id]
                    | _ ->
                        let edgeNames = IntegrityNamed.named { Revision.empty revision.Header.Producer with Edges = [edge] }
                        edgeNames |> List.collect (fun (part, ids) ->
                            ids |> List.distinct |> List.filter (fun id -> not (body id)) |> List.map (missingBody part))
                exactRows)
            |> List.distinct
        stored @ kinds @ edges

    /// Source-authored callable component integrity, independent of witnessing.
    let callableAggregates revision : IntegrityViolation list =
        CallableAggregateIntegrity.check revision
        |> List.map (fun (part, site, reason) -> { Part = part; Node = Some site; Reason = reason })

    /// Stored agreement only. Source premises can describe dormant declarations
    /// absent from executable Nodes; this reader never repeats their use census.
    let ordinaryDemand (revision: Revision) : IntegrityViolation list =
        let part = "Emission.Ordinary.Inactivity"
        let defect site reason = { Part = part; Node = Some site; Reason = reason }
        [ for KeyValue(site, proof) in revision.Emission.Ordinary.Inactivity do
              let support =
                  [proof.Implementation; proof.Entry; proof.Body] @ proof.Parameters @
                  Set.toList proof.Roots @ Set.toList proof.Excluded @ Set.toList proof.Calls @
                  (proof.Uses |> Map.toList |> List.collect (fun (source, uses) ->
                      source :: (uses |> List.collect (fun (_, _, _, sources, target) -> target :: sources))))
                  |> Set.ofList
              if site <> proof.Implementation || site = proof.Entry || proof.Roots.Contains site ||
                 proof.Excluded.Contains site || proof.Excluded.Contains proof.Entry ||
                 List.contains proof.Body proof.Parameters ||
                 (List.distinct proof.Parameters).Length <> proof.Parameters.Length ||
                 not (Set.isSubset (Set.ofList proof.Parameters) proof.Excluded) ||
                 not (Set.isSubset proof.Calls proof.Excluded) then
                  yield defect site "The inactive implementation, entry, ordered formals or excluded execution sites disagree."
              if (proof.SourcePremises |> Map.keys |> Set.ofSeq) <> support then
                  yield defect site "The inactive use inventory lacks its exact immutable source premises."
              match proof.SourcePremises.TryFind site with
              | Some premise when premise.Shape.Form = "lambda" && not premise.HasExtern &&
                                  List.tryHead premise.Shape.Text = Some "RegularClosure" &&
                                  List.tryHead premise.Shape.Numbers = Some(bigint proof.Parameters.Length) ->
                  let head = proof.Parameters @ [proof.Body]
                  let captures =
                      match premise.Shape.Numbers with
                      | _ :: count :: copiedCount :: flags when count >= 0I && count = copiedCount &&
                                                               count <= bigint System.Int32.MaxValue &&
                                                               bigint flags.Length = count * 2I &&
                                                               (flags |> List.forall (fun flag -> flag = 0I || flag = 1I)) ->
                          flags |> List.chunkBySize 2 |> List.sumBy (fun pair -> int pair[1]) |> Some
                      | _ -> None
                  let referencesAgree =
                      match captures with
                      | Some count -> premise.Shape.References.Length = head.Length + count &&
                                      List.take head.Length premise.Shape.References = head
                      | None -> false
                  if not referencesAgree then
                      yield defect site "The inactive source premise differs from its ordered formal/body and capture incidence."
                  match revision.Nodes.TryFind site with
                  | Some { Kind = SemanticKind.Lambda(parameters, body, captures, _, context) } ->
                      let actualParameters = parameters |> List.map (fun (_, _, id) -> id)
                      let references = actualParameters @ [body] @ (captures |> List.choose _.SourceNodeId)
                      let numbers =
                          [bigint parameters.Length; bigint captures.Length; bigint captures.Length] @
                          (captures |> List.collect (fun capture ->
                              [if capture.IsMutable then 1I else 0I; if capture.SourceNodeId.IsSome then 1I else 0I]))
                      let text = string context :: (parameters |> List.map (fun (name, _, _) -> name)) @ (captures |> List.map _.Name)
                      let types = (parameters |> List.map (fun (_, ty, _) -> ty)) @ (captures |> List.map _.Type)
                      if context <> LambdaContext.RegularClosure || actualParameters <> proof.Parameters || body <> proof.Body ||
                         premise.Shape.References <> references || premise.Shape.Numbers <> numbers ||
                         premise.Shape.Text <> text || premise.EmbeddedTypes <> types then
                          yield defect site "The inactive premise differs from its live ordinary implementation and ordered signature."
                  | Some _ -> yield defect site "The inactive implementation no longer has a live lambda shape."
                  | None -> ()
              | _ -> yield defect site "An inactive row lacks an ordinary source implementation premise."
              for formal in proof.Parameters do
                  match proof.SourcePremises.TryFind formal with
                  | Some premise when premise.Shape.Form = "pattern-binding" -> ()
                  | _ -> yield defect site "An inactive formal lacks its typed source binding premise."
              for call in proof.Calls do
                  match proof.SourcePremises.TryFind call with
                  | Some premise when premise.Shape.Form = "application" -> ()
                  | _ -> yield defect site "An excluded invocation lacks its exact source application premise."
              for KeyValue(source, uses) in proof.Uses do
                  if uses <> (uses |> List.distinct |> List.sort) ||
                     (uses |> List.exists (fun (cls, _, ordinal, sources, _) ->
                         (cls <> EdgeClass.Structural && cls <> EdgeClass.Reference) || ordinal < 0 || not (List.contains source sources))) then
                      yield defect site "The inactive use census has malformed or repeated typed incidence."
              for KeyValue(id, premise) in proof.SourcePremises do
                  match revision.Nodes.TryFind id with
                  | Some node when node.Type <> premise.Shape.SourceType || node.Children <> premise.Shape.Children || node.Parent <> premise.Shape.Parent ->
                      yield defect site "The inactive source premise differs from its live type or structural incidence."
                  | _ -> () ]

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
        let absent = roleAbsent revision
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
        header @ misfiled @ absent @ unrelated @ disagreed @ sourceReadings revision @ claims revision @ regions revision @
        callableRows revision @ numericRows revision @ memoryRows revision @ programStorageRows revision @ spatialRows revision @ startupRows revision @
        boundaryRows revision @ foreignResultRows revision @ artifactAccounts revision @ branchScopes revision @ stored revision @ incidence revision @ callableAggregates revision @ ordinaryDemand revision

    /// The first violations as one reason, for a reader that refuses the revision.
    let describe (violations: IntegrityViolation list) : string =
        let shown =
            violations
            |> List.truncate 8
            |> List.map (fun violation -> sprintf "%s: %s" violation.Part violation.Reason)
        let more =
            if violations.Length > shown.Length then [ sprintf "and %d more" (violations.Length - shown.Length) ] else []
        "The revision is not well formed.\n" + String.concat "\n" (shown @ more)
