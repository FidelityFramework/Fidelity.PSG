namespace Fidelity.PSG

/// Acceptance identity assigned by the compiler authority, within one workspace session.
[<Struct>]
type CheckedRevisionId = { Session: string; Ordinal: uint64 }

/// Delivery position for one subscription. It is independent of content identity.
[<Struct>]
type DeliveryCursor = { Subscription: string; Ordinal: uint64 }

[<Struct>]
type ScopeContentStamp = { Identity: string; Version: uint64 }

[<Struct>]
type BoundaryContractStamp = { Identity: string; Version: uint64 }

/// A retained correspondence for diagnostics; it carries no node body or current authority.
type HistoricalNodeIdentity = { CheckedRevision: CheckedRevisionId; Node: NodeId }

[<RequireQualifiedAccess>]
type OccurrencePort = StructuralChild | ModuleDeclaration

/// One source-authored Huet frame. Declaration membership is distinct from an
/// executable structural child position; the receiver cannot invent either.
type OccurrenceBreadcrumb = {
    Parent: NodeId
    Port: OccurrencePort
    Ordinal: int
    /// Original source port extent, including unentered positions.
    Extent: int
    /// Baker's identity for this exact ordered source port. It establishes
    /// correspondence, never current revision or proof authority.
    Stamp: string
}

/// Dependency categories declared by the source authority. Membership and absence
/// are explicit dependencies, rather than an inference made by a receiver.
[<RequireQualifiedAccess>]
type SupportKey =
    | Node of NodeId
    | Rule of string
    | Declaration of string
    | CollectionMembership of string
    | Absence of string
    | WholeOwningAnalysisRegion of string

type SupportStamp = { Key: SupportKey; Version: uint64 }

[<RequireQualifiedAccess>]
type ArtifactHandle =
    | Definition of identity: string * version: uint64
    | Storage of identity: string * version: uint64
    | Activation of identity: string * version: uint64

/// Metadata about a source-selected live scope, not its semantic payload. The
/// producer declares the actual occurrences and their structural breadcrumbs.
/// This type cannot contain a retained graph or a soft-deleted node body.
type ScopeDescriptor = {
    Content: ScopeContentStamp
    LiveOccurrences: Set<NodeId>
    /// All actual structural occurrence paths per body, nearest parent first,
    /// as stored by Baker. A root occurrence has the path []; the inventory for
    /// that root is [[]]. Shared bodies can have several distinct paths.
    ContextBreadcrumbs: Map<NodeId, OccurrenceBreadcrumb list list>
    RequiredBoundaries: Set<BoundaryContractStamp>
    RequiredSupports: Set<SupportKey>
    OwnedArtifacts: Set<ArtifactHandle>
}

/// Current source authorization for one exact content stamp. These stored stamps
/// declare the support account; structural acceptance establishes no proof truth.
type ScopeAuthorization = {
    Content: ScopeContentStamp
    CheckedRevision: CheckedRevisionId
    Boundaries: BoundaryContractStamp list
    Supports: SupportStamp list
}

[<RequireQualifiedAccess>]
type ScopeChange =
    | Add of ScopeDescriptor
    | Replace of previous: ScopeContentStamp * current: ScopeDescriptor
    | Retire of ScopeContentStamp

type ArtifactOwner = { Scope: ScopeContentStamp; Artifact: ArtifactHandle }

/// Explicit source accounting for replaced, split, merged or retired ownership.
/// Empty Current means retirement. The receiver compares the declared ownership
/// sets; it does not discover artifact ownership from code or graph structure.
type ArtifactOwnershipTransition = {
    Previous: Set<ArtifactOwner>
    Current: Set<ArtifactOwner>
}

/// One atomic metadata transaction, against an exact accepted subscription base.
/// Every surviving scope is explicitly authorized for TargetRevision or withdrawn.
/// A semantic payload protocol must separately establish availability of its facts.
type SourceScopeTransaction = {
    BaseCursor: DeliveryCursor
    BaseRevision: CheckedRevisionId
    TargetCursor: DeliveryCursor
    TargetRevision: CheckedRevisionId
    Changes: ScopeChange list
    Authorizations: ScopeAuthorization list
    Withdrawals: ScopeContentStamp list
    ArtifactTransitions: ArtifactOwnershipTransition list
}

/// A subscription's resident metadata and current source authorizations. Content
/// may remain resident after withdrawal, but residence alone permits no execution.
type ScopedCatalog = {
    Cursor: DeliveryCursor
    CheckedRevision: CheckedRevisionId
    Scopes: Map<string, ScopeDescriptor>
    Authorizations: Map<string, ScopeAuthorization>
}

[<RequireQualifiedAccess>]
type ScopedPublicationError =
    | InvalidIdentity of field: string
    | InvalidCatalog of detail: string
    | BaseCursorMismatch
    | BaseRevisionMismatch
    | TargetSubscriptionMismatch
    | TargetCursorNotNext
    | TargetSessionMismatch
    | TargetRevisionOlder
    | DuplicateScopeChange of identity: string
    | ExistingScope of identity: string
    | MissingScope of identity: string
    | PreviousContentMismatch of identity: string
    | ReplacementIdentityMismatch of identity: string
    | ReplacementVersionNotLater of identity: string
    | IncompleteOccurrenceContext of identity: string
    | InvalidContextPosition of occurrence: NodeId * parent: NodeId * ordinal: int * extent: int
    | MissingContextPortStamp of occurrence: NodeId * parent: NodeId
    | DuplicateDisposition of identity: string
    | MissingDisposition of identity: string
    | ContentMismatch of identity: string
    | AuthorizationRevisionMismatch of identity: string
    | DuplicateSupport of identity: string * key: SupportKey
    | SupportAccountMismatch of identity: string
    | DuplicateBoundary of identity: string * stamp: BoundaryContractStamp
    | BoundaryAccountMismatch of identity: string
    | EmptyArtifactTransition
    | DuplicatePreviousArtifactOwner of ArtifactOwner
    | DuplicateCurrentArtifactOwner of ArtifactOwner
    | ArtifactAccountMismatch

/// Structural readings and atomic catalog application only. Scope selection,
/// dependency closure, invalidation decisions and proof acceptance remain owned
/// by the compiler authority; this module computes none of them.
[<RequireQualifiedAccess>]
module ScopedPublication =
    let private identityValid (identity: string) =
        not (System.String.IsNullOrWhiteSpace identity)

    let private checkIdentity field identity (errors: ResizeArray<ScopedPublicationError>) =
        if not (identityValid identity) then errors.Add(ScopedPublicationError.InvalidIdentity field)

    let private checkRevision field (revision: CheckedRevisionId) errors =
        checkIdentity (field + ".Session") revision.Session errors

    let private checkContent field (stamp: ScopeContentStamp) errors =
        checkIdentity (field + ".Identity") stamp.Identity errors

    let private checkBoundary (stamp: BoundaryContractStamp) errors =
        checkIdentity "Boundary.Identity" stamp.Identity errors

    let private checkSupport key errors =
        match key with
        | SupportKey.Node _ -> ()
        | SupportKey.Rule identity
        | SupportKey.Declaration identity
        | SupportKey.CollectionMembership identity
        | SupportKey.Absence identity
        | SupportKey.WholeOwningAnalysisRegion identity -> checkIdentity "Support.Identity" identity errors

    let private checkArtifact artifact errors =
        match artifact with
        | ArtifactHandle.Definition (identity, _)
        | ArtifactHandle.Storage (identity, _)
        | ArtifactHandle.Activation (identity, _) ->
            checkIdentity "Artifact.Identity" identity errors

    let private checkDescriptor (scope: ScopeDescriptor) (errors: ResizeArray<ScopedPublicationError>) =
        checkContent "Scope.Content" scope.Content errors
        let contextual = scope.ContextBreadcrumbs |> Map.toSeq |> Seq.map fst |> Set.ofSeq
        if contextual <> scope.LiveOccurrences || (scope.ContextBreadcrumbs |> Map.exists (fun _ paths -> paths.IsEmpty)) then
            errors.Add(ScopedPublicationError.IncompleteOccurrenceContext scope.Content.Identity)
        for KeyValue(occurrence, paths) in scope.ContextBreadcrumbs do
            for frame in List.concat paths do
                if frame.Ordinal < 0 || frame.Ordinal >= frame.Extent then
                    errors.Add(ScopedPublicationError.InvalidContextPosition(occurrence, frame.Parent, frame.Ordinal, frame.Extent))
                if System.String.IsNullOrWhiteSpace frame.Stamp then
                    errors.Add(ScopedPublicationError.MissingContextPortStamp(occurrence, frame.Parent))
        scope.RequiredBoundaries |> Set.iter (fun stamp -> checkBoundary stamp errors)
        scope.RequiredSupports |> Set.iter (fun key -> checkSupport key errors)
        scope.OwnedArtifacts |> Set.iter (fun artifact -> checkArtifact artifact errors)

    let private checkAuthorization revision (scope: ScopeDescriptor) (authorization: ScopeAuthorization)
                                   (errors: ResizeArray<ScopedPublicationError>) =
        let identity = scope.Content.Identity
        if authorization.Content <> scope.Content then errors.Add(ScopedPublicationError.ContentMismatch identity)
        if authorization.CheckedRevision <> revision then
            errors.Add(ScopedPublicationError.AuthorizationRevisionMismatch identity)
        let keys = authorization.Supports |> List.map (fun support -> support.Key) |> Set.ofList
        authorization.Supports
        |> List.groupBy (fun support -> support.Key)
        |> List.iter (fun (key, stamps) ->
            if stamps.Length > 1 then errors.Add(ScopedPublicationError.DuplicateSupport(identity, key)))
        for support in authorization.Supports do
            checkSupport support.Key errors
        if keys <> scope.RequiredSupports then errors.Add(ScopedPublicationError.SupportAccountMismatch identity)
        let boundaries = Set.ofList authorization.Boundaries
        authorization.Boundaries
        |> List.countBy id
        |> List.iter (fun (boundary, count) ->
            if count > 1 then errors.Add(ScopedPublicationError.DuplicateBoundary(identity, boundary)))
        for boundary in authorization.Boundaries do
            checkBoundary boundary errors
        if boundaries <> scope.RequiredBoundaries then errors.Add(ScopedPublicationError.BoundaryAccountMismatch identity)

    let private artifactOwners scopes =
        scopes
        |> Map.toSeq
        |> Seq.collect (fun (_, scope: ScopeDescriptor) ->
            scope.OwnedArtifacts |> Seq.map (fun artifact -> { Scope = scope.Content; Artifact = artifact }))
        |> Set.ofSeq

    /// Start one empty subscription at an already accepted revision. No graph is
    /// copied to establish this catalog. The first transaction explicitly adds scopes.
    let start subscription revision =
        let errors = ResizeArray()
        checkIdentity "Subscription" subscription errors
        checkRevision "CheckedRevision" revision errors
        if errors.Count <> 0 then Error(List.ofSeq errors)
        else
            Ok { Cursor = { Subscription = subscription; Ordinal = 0UL }
                 CheckedRevision = revision; Scopes = Map.empty; Authorizations = Map.empty }

    /// Apply all declarations or return errors without advancing the catalog.
    /// Equal content never carries authorization into a new checked revision.
    let apply (transaction: SourceScopeTransaction) (catalog: ScopedCatalog) =
        let errors = ResizeArray()
        checkIdentity "Catalog.Subscription" catalog.Cursor.Subscription errors
        checkRevision "Catalog.CheckedRevision" catalog.CheckedRevision errors
        for KeyValue(identity, scope) in catalog.Scopes do
            if identity <> scope.Content.Identity then errors.Add(ScopedPublicationError.InvalidCatalog "scope map key")
            checkDescriptor scope errors
        for KeyValue(identity, authorization) in catalog.Authorizations do
            match catalog.Scopes.TryFind identity with
            | None -> errors.Add(ScopedPublicationError.InvalidCatalog "authorization without resident scope")
            | Some scope -> checkAuthorization catalog.CheckedRevision scope authorization errors
        if transaction.BaseCursor <> catalog.Cursor then errors.Add ScopedPublicationError.BaseCursorMismatch
        if transaction.BaseRevision <> catalog.CheckedRevision then errors.Add ScopedPublicationError.BaseRevisionMismatch
        if transaction.TargetCursor.Subscription <> catalog.Cursor.Subscription then
            errors.Add ScopedPublicationError.TargetSubscriptionMismatch
        if catalog.Cursor.Ordinal = System.UInt64.MaxValue
           || transaction.TargetCursor.Ordinal <> catalog.Cursor.Ordinal + 1UL then
            errors.Add ScopedPublicationError.TargetCursorNotNext
        checkRevision "TargetRevision" transaction.TargetRevision errors
        if transaction.TargetRevision.Session <> catalog.CheckedRevision.Session then
            errors.Add ScopedPublicationError.TargetSessionMismatch
        if transaction.TargetRevision.Ordinal < catalog.CheckedRevision.Ordinal then
            errors.Add ScopedPublicationError.TargetRevisionOlder

        let changeIdentity = function
            | ScopeChange.Add scope -> scope.Content.Identity
            | ScopeChange.Replace(previous, _) | ScopeChange.Retire previous -> previous.Identity
        transaction.Changes
        |> List.countBy changeIdentity
        |> List.iter (fun (identity, count) ->
            if count > 1 then errors.Add(ScopedPublicationError.DuplicateScopeChange identity))
        let changeScope scopes change =
            let identity = changeIdentity change
            match change with
            | ScopeChange.Add scope ->
                checkDescriptor scope errors
                if catalog.Scopes.ContainsKey identity then errors.Add(ScopedPublicationError.ExistingScope identity)
                Map.add identity scope scopes
            | ScopeChange.Replace(previous, scope) ->
                checkContent "PreviousContent" previous errors
                checkDescriptor scope errors
                match catalog.Scopes.TryFind identity with
                | None -> errors.Add(ScopedPublicationError.MissingScope identity)
                | Some held when held.Content <> previous -> errors.Add(ScopedPublicationError.PreviousContentMismatch identity)
                | Some _ -> ()
                if scope.Content.Identity <> identity then errors.Add(ScopedPublicationError.ReplacementIdentityMismatch identity)
                if scope.Content.Version <= previous.Version then errors.Add(ScopedPublicationError.ReplacementVersionNotLater identity)
                Map.add identity scope scopes
            | ScopeChange.Retire previous ->
                checkContent "PreviousContent" previous errors
                match catalog.Scopes.TryFind identity with
                | None -> errors.Add(ScopedPublicationError.MissingScope identity)
                | Some held when held.Content <> previous -> errors.Add(ScopedPublicationError.PreviousContentMismatch identity)
                | Some _ -> ()
                Map.remove identity scopes
        let scopes = List.fold changeScope catalog.Scopes transaction.Changes

        let dispositions =
            (transaction.Authorizations |> List.map (fun authorization -> authorization.Content.Identity))
            @ (transaction.Withdrawals |> List.map (fun stamp -> stamp.Identity))
        dispositions
        |> List.countBy id
        |> List.iter (fun (identity, count) ->
            if count > 1 then errors.Add(ScopedPublicationError.DuplicateDisposition identity))
        let disposed = Set.ofList dispositions
        for authorization in transaction.Authorizations do
            let identity = authorization.Content.Identity
            match scopes.TryFind identity with
            | None -> errors.Add(ScopedPublicationError.MissingScope identity)
            | Some scope ->
                checkAuthorization transaction.TargetRevision scope authorization errors
        for withdrawal in transaction.Withdrawals do
            checkContent "Withdrawal" withdrawal errors
            match scopes.TryFind withdrawal.Identity with
            | None -> errors.Add(ScopedPublicationError.MissingScope withdrawal.Identity)
            | Some scope when scope.Content <> withdrawal -> errors.Add(ScopedPublicationError.ContentMismatch withdrawal.Identity)
            | Some _ -> ()
        for KeyValue(identity, _) in scopes do
            if not (disposed.Contains identity) then errors.Add(ScopedPublicationError.MissingDisposition identity)

        let previousOwners = artifactOwners catalog.Scopes
        let currentOwners = artifactOwners scopes
        let retiredOwners = Set.difference previousOwners currentOwners
        let establishedOwners = Set.difference currentOwners previousOwners
        for transition in transaction.ArtifactTransitions do
            if transition.Previous.IsEmpty && transition.Current.IsEmpty then
                errors.Add ScopedPublicationError.EmptyArtifactTransition
            for owner in transition.Previous do
                checkContent "ArtifactOwner.Scope" owner.Scope errors
                checkArtifact owner.Artifact errors
            for owner in transition.Current do
                checkContent "ArtifactOwner.Scope" owner.Scope errors
                checkArtifact owner.Artifact errors
        let previousDeclarations = transaction.ArtifactTransitions |> List.collect (fun transition -> Set.toList transition.Previous)
        let currentDeclarations = transaction.ArtifactTransitions |> List.collect (fun transition -> Set.toList transition.Current)
        previousDeclarations
        |> List.countBy id
        |> List.iter (fun (owner, count) ->
            if count > 1 then errors.Add(ScopedPublicationError.DuplicatePreviousArtifactOwner owner))
        currentDeclarations
        |> List.countBy id
        |> List.iter (fun (owner, count) ->
            if count > 1 then errors.Add(ScopedPublicationError.DuplicateCurrentArtifactOwner owner))
        let declaredPrevious = Set.ofList previousDeclarations
        let declaredCurrent = Set.ofList currentDeclarations
        if declaredPrevious <> retiredOwners || declaredCurrent <> establishedOwners then
            errors.Add ScopedPublicationError.ArtifactAccountMismatch

        if errors.Count <> 0 then Error(List.ofSeq errors)
        else
            Ok { Cursor = transaction.TargetCursor; CheckedRevision = transaction.TargetRevision
                 Scopes = scopes
                 Authorizations = transaction.Authorizations |> List.map (fun held -> held.Content.Identity, held) |> Map.ofList }
