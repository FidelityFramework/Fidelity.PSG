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
            | CallableValueShape.Callable node -> need part "Emission.Callable.Carriers" node (callable.Carriers.ContainsKey node)
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
            let identityName = function
                | ProgramStorageIdentity.Allocation id -> sprintf "allocation:%d" (NodeId.value id)
                | ProgramStorageIdentity.BindingSlot id -> sprintf "binding:%d" (NodeId.value id)
            [ for KeyValue(identity, entry) in storage.Entries do
                  let id = match identity with ProgramStorageIdentity.Allocation id | ProgramStorageIdentity.BindingSlot id -> id
                  if identity <> entry.Identity then yield defect (part + ".Entries.Identity") id "A storage entry is filed under a different identity."
                  match storage.Reservations.TryFind entry.SpaceNode with
                  | Some reservation when reservation.Space = entry.Space -> ()
                  | _ -> yield missingRow (part + ".Entries.SpaceNode") "Reservations with the exact declared space" entry.SpaceNode
              for KeyValue(space, reservation) in storage.Reservations do
                  let entries = storage.Entries |> Map.toList |> List.filter(fun (_, entry) -> entry.SpaceNode = space)
                  let expected : BAREWire.Platform.StorageRequest list =
                      entries |> List.map(fun (identity, entry) -> {Name = identityName identity; Length = int64 entry.Bytes; Alignment = entry.Alignment})
                  if entries.IsEmpty || Array.toList reservation.Requests <> expected then
                      yield defect (part + ".Reservations") space "The ordered reserved objects differ from the storage entries for this space." ]
        check "Codata.ProgramStorage" revision.Codata.ProgramStorage @
        check "Emission.Storage.ProgramStorage" revision.Emission.Storage.ProgramStorage @
        (if revision.Codata.ProgramStorage = revision.Emission.Storage.ProgramStorage then []
         else [{Part = "Emission.Storage.ProgramStorage"; Node = None; Reason = "The program storage account differs from Codata.ProgramStorage."}])

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

    /// Boundary references resolve inside their owning imported declaration.
    /// Import membership is not executable residency or general ID authority.
    let private boundaryRows (revision: Revision) =
        let boundary = revision.Emission.Boundary
        let need part table node present = if present then [] else [missingRow part table node]
        [ for KeyValue(key, imported) in boundary.Imports do
              if key <> imported.Identity then yield defect "Emission.Boundary.Imports.Identity" key "An import is filed under a different identity."
              yield! need "Emission.Boundary.Imports.Scope" "SourceReadings.ContextHeaders" imported.Scope
                  (revision.SourceReadings.ContextHeaders.ContainsKey imported.Scope)
              yield! need "Emission.Boundary.Imports.Binding" "the import's DeclarationFacts" imported.Binding
                  (revision.Nodes.ContainsKey imported.Binding || imported.DeclarationFacts.ContainsKey imported.Binding)
              for formal, _ in imported.Parameters do
                  yield! need "Emission.Boundary.Imports.Parameters" "the import's SourceTypes" formal (imported.SourceTypes.ContainsKey formal)
              for id in imported.DeclarationPath do
                  yield! need "Emission.Boundary.Imports.DeclarationPath" "the import's DeclarationFacts or its context header" id
                      (revision.Nodes.ContainsKey id || imported.DeclarationFacts.ContainsKey id || revision.SourceReadings.ContextHeaders.ContainsKey id)
          for KeyValue(scope, imports) in boundary.ByScope do
              for id in imports do
                  match boundary.Imports.TryFind id with
                  | Some imported when imported.Scope = scope -> ()
                  | _ -> yield missingRow "Emission.Boundary.ByScope (values)" "Imports with the declared Scope" id
          for KeyValue(key, call) in boundary.Calls do
              if key <> call.Site then yield defect "Emission.Boundary.Calls.Site" key "A boundary call is filed under a different site."
              match boundary.Imports.TryFind call.Import with
              | None -> yield missingRow "Emission.Boundary.Calls.Import" "Emission.Boundary.Imports" call.Import
              | Some imported ->
                  match revision.Nodes.TryFind call.Site with
                  | Some {Kind = SemanticKind.Application(callee, _)} when callee = call.Callee -> ()
                  | _ -> yield defect "Emission.Boundary.Calls.Callee" call.Callee "The call's callee differs from its live source application's callee."
                  yield! need "Emission.Boundary.Calls.Callee" "Nodes (actual callee occurrence)" call.Callee (revision.Nodes.ContainsKey call.Callee)
                  for operand in call.Arguments do
                      if not (imported.Parameters |> List.contains (operand.Formal, operand.Abi)) then
                          yield defect "Emission.Boundary.Calls.Arguments" operand.Formal "A boundary operand differs from its imported formal/ABI account."
                      yield! need "Emission.Boundary.Calls.Arguments" "Nodes (actual operand)" operand.Actual (revision.Nodes.ContainsKey operand.Actual)
          for KeyValue(_, proofs) in boundary.IntrinsicWriteProofs do
              for proof in proofs do
                  match revision.CurrentClaims.TryFind proof.Obligation with
                  | Some claim when claim.Body = proof.Body -> ()
                  | _ -> yield missingRow "Emission.Boundary.IntrinsicWriteProofs (values)" "CurrentClaims with the exact proof body" proof.Obligation
          for KeyValue(key, imported) in boundary.IntrinsicWriteImports do
              if key <> imported.Identity then yield defect "Emission.Boundary.IntrinsicWriteImports.Identity" key "An intrinsic import is filed under a different identity."
              yield! need "Emission.Boundary.IntrinsicWriteImports.Scope" "SourceReadings.ContextHeaders" imported.Scope
                  (revision.SourceReadings.ContextHeaders.ContainsKey imported.Scope) ]

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
                         "Emission.Boundary.IntrinsicWriteImports.Scope"
                         "Emission.Boundary.Calls.Arguments"; "Emission.Boundary.IntrinsicWriteProofs (values)"
                         "Emission.Boundary.Imports.DeclarationFacts" ]
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
                         "Emission.Memory.ArrayCopies.Participants"; "Emission.Spatial.Hardware.Participants"
                         "Emission.Spatial.Kernels.Participants"; "Codata.CallableBranches.Observations.Participants"
                         "Emission.Callable.Branches.Observations.Participants" ]
        let role part id =
            if explicitParts.Contains part || supportParts.Contains part || part.StartsWith("SourceReadings.", System.StringComparison.Ordinal) then true
            else
                match part with
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
                | "Emission.Boundary.DeclarationLeaves" | "Emission.Boundary.DeclarationOnly" -> body id || declarationFact id || boundaryType id || source.ContextHeaders.ContainsKey id
                | "Emission.Boundary.Imports.Scope" -> source.ContextHeaders.ContainsKey id
                | "Emission.Boundary.IntrinsicWriteImports.Scope" -> source.ContextHeaders.ContainsKey id
                | "Emission.Boundary.Imports.Parameters" | "Emission.Boundary.Imports.SourceTypes" -> boundaryType id
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
        boundaryRows revision @ branchScopes revision @ stored revision @ incidence revision

    /// The first violations as one reason, for a reader that refuses the revision.
    let describe (violations: IntegrityViolation list) : string =
        let shown =
            violations
            |> List.truncate 8
            |> List.map (fun violation -> sprintf "%s: %s" violation.Part violation.Reason)
        let more =
            if violations.Length > shown.Length then [ sprintf "and %d more" (violations.Length - shown.Length) ] else []
        "The revision is not well formed.\n" + String.concat "\n" (shown @ more)
