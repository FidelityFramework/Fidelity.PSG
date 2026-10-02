namespace Fidelity.PSG

/// Baker's stored decision for one original child position. The receiver never
/// fetches an absent body to decide whether that child should be entered.
[<RequireQualifiedAccess>]
type ChildTraversal =
    | EnterLocal of NodeId
    | EnterImported of scope: ScopeContentStamp * boundary: BoundaryContractStamp * node: NodeId
    | SourceOmitted of support: SupportKey * node: NodeId

/// One declaration per child position, in the original node's child order.
/// Equal child identities at different ordinals remain separate occurrences.
type ChildDisposition = { Ordinal: int; Traversal: ChildTraversal }

/// A selected live body with its complete stored child account and all actual
/// occurrence contexts. Original Kind, Children and parent identities remain
/// intact. An ancestor or sibling handle does not request its body.
type LiveOccurrence = {
    Body: SemanticNode
    Children: ChildDisposition list
    OccurrenceContexts: OccurrenceBreadcrumb list list
}

/// The live-occurrence portion of a source-authored scope. This is not a
/// complete executable semantic payload: settled emission facts, imported
/// boundary contracts and proof acceptance have separate contracts. No field
/// contains hyperedges, a Revision or a census of retained source premises.
type LiveOccurrenceSection = {
    Descriptor: ScopeDescriptor
    Occurrences: Map<NodeId, LiveOccurrence>
}

[<RequireQualifiedAccess>]
type LiveOccurrenceViolation =
    | OccurrenceAccountMismatch
    | ContextAccountMismatch
    | MisfiledBody of key: NodeId * body: NodeId
    | InactiveBody of NodeId
    | MissingOccurrenceContexts of NodeId
    | OccurrenceContextMismatch of NodeId
    | InvalidContextPosition of occurrence: NodeId * parent: NodeId * ordinal: int * extent: int
    | MissingContextPortStamp of occurrence: NodeId * parent: NodeId
    | ChildCountMismatch of parent: NodeId
    | ChildOrdinalMismatch of parent: NodeId * expected: int * actual: int
    | ChildIdentityMismatch of parent: NodeId * ordinal: int * expected: NodeId * actual: NodeId
    | MissingLocalChild of parent: NodeId * ordinal: int * child: NodeId
    | InvalidImportIdentity of parent: NodeId * ordinal: int
    | SelfImport of parent: NodeId * ordinal: int
    | UndeclaredImportBoundary of parent: NodeId * ordinal: int * boundary: BoundaryContractStamp
    | UndeclaredOmissionSupport of parent: NodeId * ordinal: int * support: SupportKey

/// Structural comparison of stored occurrence declarations only. An omission
/// support is a source judgment; this validator establishes neither its truth
/// nor the completeness of the source's semantic dependency closure.
[<RequireQualifiedAccess>]
module LiveOccurrenceSection =
    let private childIdentity = function
        | ChildTraversal.EnterLocal node
        | ChildTraversal.EnterImported(_, _, node)
        | ChildTraversal.SourceOmitted(_, node) -> node

    let check (section: LiveOccurrenceSection) =
        let descriptor = section.Descriptor
        let bodies = section.Occurrences |> Map.toSeq |> Seq.map fst |> Set.ofSeq
        let contexts = descriptor.ContextBreadcrumbs |> Map.toSeq |> Seq.map fst |> Set.ofSeq
        let account =
            [ if bodies <> descriptor.LiveOccurrences then LiveOccurrenceViolation.OccurrenceAccountMismatch
              if contexts <> descriptor.LiveOccurrences then LiveOccurrenceViolation.ContextAccountMismatch ]
        let checkOccurrence key (occurrence: LiveOccurrence) =
            let body = occurrence.Body
            let identity =
                [ if body.Id <> key then LiveOccurrenceViolation.MisfiledBody(key, body.Id)
                  if not body.IsReachable then LiveOccurrenceViolation.InactiveBody key
                  if occurrence.OccurrenceContexts.IsEmpty then LiveOccurrenceViolation.MissingOccurrenceContexts key
                  if descriptor.ContextBreadcrumbs.TryFind key <> Some occurrence.OccurrenceContexts then
                      LiveOccurrenceViolation.OccurrenceContextMismatch key ]
            let count =
                if occurrence.Children.Length <> body.Children.Length then [LiveOccurrenceViolation.ChildCountMismatch key]
                else []
            let checkChild expectedOrdinal disposition =
                let actual = childIdentity disposition.Traversal
                let ordering =
                    [ if disposition.Ordinal <> expectedOrdinal then
                          LiveOccurrenceViolation.ChildOrdinalMismatch(key, expectedOrdinal, disposition.Ordinal)
                      match body.Children |> List.tryItem expectedOrdinal with
                      | Some expected when expected <> actual ->
                          LiveOccurrenceViolation.ChildIdentityMismatch(key, expectedOrdinal, expected, actual)
                      | _ -> () ]
                let declaration =
                    match disposition.Traversal with
                    | ChildTraversal.EnterLocal child when not (section.Occurrences.ContainsKey child) ->
                        [LiveOccurrenceViolation.MissingLocalChild(key, expectedOrdinal, child)]
                    | ChildTraversal.EnterLocal _ -> []
                    | ChildTraversal.EnterImported(scope, boundary, _) ->
                        [ if System.String.IsNullOrWhiteSpace scope.Identity || System.String.IsNullOrWhiteSpace boundary.Identity then
                              LiveOccurrenceViolation.InvalidImportIdentity(key, expectedOrdinal)
                          if scope.Identity = descriptor.Content.Identity then LiveOccurrenceViolation.SelfImport(key, expectedOrdinal)
                          if not (descriptor.RequiredBoundaries.Contains boundary) then
                              LiveOccurrenceViolation.UndeclaredImportBoundary(key, expectedOrdinal, boundary) ]
                    | ChildTraversal.SourceOmitted(support, _) when not (descriptor.RequiredSupports.Contains support) ->
                        [LiveOccurrenceViolation.UndeclaredOmissionSupport(key, expectedOrdinal, support)]
                    | ChildTraversal.SourceOmitted _ -> []
                ordering @ declaration
            let contextOrdinals =
                occurrence.OccurrenceContexts
                |> List.concat
                |> List.collect (fun frame ->
                    [ if frame.Ordinal < 0 || frame.Ordinal >= frame.Extent then
                          LiveOccurrenceViolation.InvalidContextPosition(key, frame.Parent, frame.Ordinal, frame.Extent)
                      if System.String.IsNullOrWhiteSpace frame.Stamp then
                          LiveOccurrenceViolation.MissingContextPortStamp(key, frame.Parent) ])
            identity @ contextOrdinals @ count @ (occurrence.Children |> List.mapi checkChild |> List.concat)
        account @ (section.Occurrences |> Map.toList |> List.collect (fun (key, occurrence) -> checkOccurrence key occurrence))

/// Delivery of occurrence bodies for only the explicitly added or replaced
/// scopes. This is not a complete executable payload and conveys no proof or
/// artifact acceptance. Unchanged authorizations carry no occurrence section.
type OccurrenceDelivery = {
    Transaction: SourceScopeTransaction
    Sections: LiveOccurrenceSection list
}

[<RequireQualifiedAccess>]
type OccurrenceDeliveryViolation =
    | DuplicateChangeDescriptor of identity: string
    | MissingSection of ScopeContentStamp
    | DuplicateSection of identity: string
    | UnexpectedSection of ScopeContentStamp
    | DescriptorMismatch of expected: ScopeContentStamp * actual: ScopeContentStamp
    | InvalidSection of ScopeContentStamp * LiveOccurrenceViolation list

[<RequireQualifiedAccess>]
module OccurrenceDelivery =
    /// Compare explicitly declared sections and changes. Full transaction
    /// acceptance against a resident base is a separate catalog operation.
    let check (delivery: OccurrenceDelivery) =
        let expected =
            delivery.Transaction.Changes
            |> List.choose (function
                | ScopeChange.Add descriptor | ScopeChange.Replace(_, descriptor) -> Some descriptor
                | ScopeChange.Retire _ -> None)
        let duplicates =
            (expected |> List.countBy (fun descriptor -> descriptor.Content.Identity)
                      |> List.choose (fun (identity, count) ->
                          if count > 1 then Some(OccurrenceDeliveryViolation.DuplicateChangeDescriptor identity) else None))
            @ (delivery.Sections |> List.countBy (fun section -> section.Descriptor.Content.Identity)
                                 |> List.choose (fun (identity, count) ->
                                     if count > 1 then Some(OccurrenceDeliveryViolation.DuplicateSection identity) else None))
        let missing =
            expected |> List.choose (fun descriptor ->
                if delivery.Sections |> List.exists (fun section -> section.Descriptor.Content.Identity = descriptor.Content.Identity) then None
                else Some(OccurrenceDeliveryViolation.MissingSection descriptor.Content))
        let supplied =
            delivery.Sections |> List.collect (fun section ->
                let declaration =
                    match expected |> List.tryFind (fun descriptor -> descriptor.Content.Identity = section.Descriptor.Content.Identity) with
                    | None -> [OccurrenceDeliveryViolation.UnexpectedSection section.Descriptor.Content]
                    | Some descriptor when descriptor <> section.Descriptor ->
                        [OccurrenceDeliveryViolation.DescriptorMismatch(descriptor.Content, section.Descriptor.Content)]
                    | Some _ -> []
                let violations = LiveOccurrenceSection.check section
                let structural =
                    if violations.IsEmpty then []
                    else [OccurrenceDeliveryViolation.InvalidSection(section.Descriptor.Content, violations)]
                declaration @ structural)
        duplicates @ missing @ supplied
