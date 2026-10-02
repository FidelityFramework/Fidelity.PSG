module Fidelity.PSG.Tests.ScopedPublicationTests

open Xunit
open Fidelity.PSG

let private revision ordinal : CheckedRevisionId = { Session = "workspace"; Ordinal = ordinal }
let private stamp identity version : ScopeContentStamp = { Identity = identity; Version = version }
let private boundary : BoundaryContractStamp = { Identity = "callee-abi"; Version = 3UL }
let private supports =
    Set.ofList [ SupportKey.Node(NodeId 7); SupportKey.CollectionMembership "overload-candidates"
                 SupportKey.Absence "higher-priority-candidate" ]
let private breadcrumb parent left right : OccurrenceBreadcrumb =
    { Parent = NodeId parent; Port = OccurrencePort.StructuralChild; Ordinal = List.length left
      Extent = List.length left + 1 + List.length right; Stamp = "source-port" }
let private scope identity version artifacts : ScopeDescriptor =
    { Content = stamp identity version; LiveOccurrences = Set.singleton(NodeId 7)
      ContextBreadcrumbs = Map.ofList [ (NodeId 7, [ [ breadcrumb 2 [] [] ] ]) ]
      RequiredBoundaries = Set.singleton boundary; RequiredSupports = supports
      OwnedArtifacts = Set.ofList artifacts }
let private authorize target (scope: ScopeDescriptor) : ScopeAuthorization =
    { Content = scope.Content; CheckedRevision = target
      Boundaries = Set.toList scope.RequiredBoundaries
      Supports = scope.RequiredSupports |> Set.toList |> List.map (fun key -> { Key = key; Version = 1UL }) }
let private owners (scope: ScopeDescriptor) =
    scope.OwnedArtifacts |> Set.map (fun artifact -> { Scope = scope.Content; Artifact = artifact })
let private accepted = function
    | Ok value -> value
    | Error errors -> failwithf "Unexpected refusal: %A" errors
let private empty () = ScopedPublication.start "subscriber" (revision 1UL) |> accepted
let private transaction (catalog: ScopedCatalog) : SourceScopeTransaction =
    { BaseCursor = catalog.Cursor; BaseRevision = catalog.CheckedRevision
      TargetCursor = { catalog.Cursor with Ordinal = catalog.Cursor.Ordinal + 1UL }
      TargetRevision = revision (catalog.CheckedRevision.Ordinal + 1UL)
      Changes = []; Authorizations = []; Withdrawals = []; ArtifactTransitions = [] }
let private withScope (scope: ScopeDescriptor) =
    let catalog = empty ()
    let next = transaction catalog
    { next with Changes = [ ScopeChange.Add scope ]
                Authorizations = [ authorize next.TargetRevision scope ]
                ArtifactTransitions =
                    if scope.OwnedArtifacts.IsEmpty then []
                    else [ { Previous = Set.empty; Current = owners scope } ] }
    |> fun supplied -> ScopedPublication.apply supplied catalog |> accepted
let private refuses error transaction catalog =
    match ScopedPublication.apply transaction catalog with
    | Ok _ -> failwithf "Expected refusal %A" error
    | Error errors -> Assert.True(List.contains error errors, sprintf "Expected %A in %A" error errors)

[<Fact>]
let ``a new subscription begins empty without copying a retained graph`` () =
    let catalog = empty ()
    Assert.Empty catalog.Scopes
    Assert.Empty catalog.Authorizations
    Assert.Equal(0UL, catalog.Cursor.Ordinal)

[<Fact>]
let ``zero versions are source identities and are not reserved by the receiver`` () =
    let catalog = ScopedPublication.start "subscriber" (revision 0UL) |> accepted
    let selected =
        { scope "selected" 0UL [ ArtifactHandle.Definition("entry", 0UL) ] with
            RequiredBoundaries = Set.singleton { boundary with Version = 0UL } }
    let next = { transaction catalog with TargetRevision = revision 0UL }
    let auth = authorize next.TargetRevision selected
    let auth = { auth with Supports = auth.Supports |> List.map (fun support -> { support with Version = 0UL }) }
    let result =
        ScopedPublication.apply
            { next with Changes = [ ScopeChange.Add selected ]; Authorizations = [ auth ]
                        ArtifactTransitions = [ { Previous = Set.empty; Current = owners selected } ] } catalog |> accepted
    Assert.Equal(revision 0UL, result.CheckedRevision)

[<Fact>]
let ``an exact transaction adds only explicitly selected scope metadata`` () =
    let selected = scope "selected-callable" 1UL []
    let catalog = withScope selected
    Assert.Single(catalog.Scopes) |> ignore
    Assert.Equal(selected, catalog.Scopes[selected.Content.Identity])
    Assert.Equal(revision 2UL, catalog.Authorizations[selected.Content.Identity].CheckedRevision)

[<Fact>]
let ``attachment and newly demanded scopes need no invented checked revision`` () =
    let catalog = empty ()
    let selected = scope "selected" 1UL []
    let next = { transaction catalog with TargetRevision = catalog.CheckedRevision }
    let attached =
        ScopedPublication.apply
            { next with Changes = [ ScopeChange.Add selected ]
                        Authorizations = [ authorize next.TargetRevision selected ] } catalog |> accepted
    Assert.Equal(catalog.CheckedRevision, attached.CheckedRevision)
    Assert.Equal(1UL, attached.Cursor.Ordinal)
    let demanded = scope "newly-demanded" 1UL []
    let delivery = { transaction attached with TargetRevision = attached.CheckedRevision }
    let extended =
        ScopedPublication.apply
            { delivery with Changes = [ ScopeChange.Add demanded ]
                            Authorizations = [ authorize delivery.TargetRevision selected; authorize delivery.TargetRevision demanded ] }
            attached |> accepted
    Assert.Equal(catalog.CheckedRevision, extended.CheckedRevision)
    Assert.Equal(2UL, extended.Cursor.Ordinal)
    Assert.Equal(2, extended.Scopes.Count)

[<Fact>]
let ``a stale delivery base cannot advance a catalog`` () =
    let selected = scope "callable" 1UL []
    let catalog = withScope selected
    let next = transaction catalog
    let stale = { next with BaseCursor = { catalog.Cursor with Ordinal = 0UL }
                            Authorizations = [ authorize next.TargetRevision selected ] }
    refuses ScopedPublicationError.BaseCursorMismatch stale catalog
    Assert.Equal(1UL, catalog.Cursor.Ordinal)
    Assert.Equal(revision 2UL, catalog.CheckedRevision)

[<Fact>]
let ``equal ordinals in another session are not the accepted base`` () =
    let catalog = empty ()
    let next = transaction catalog
    refuses ScopedPublicationError.BaseRevisionMismatch
        { next with BaseRevision = { catalog.CheckedRevision with Session = "other-workspace" } } catalog

[<Fact>]
let ``a target cannot change subscription or skip a delivery cursor`` () =
    let catalog = empty ()
    let next = transaction catalog
    refuses ScopedPublicationError.TargetSubscriptionMismatch
        { next with TargetCursor = { next.TargetCursor with Subscription = "other-subscriber" } } catalog
    refuses ScopedPublicationError.TargetCursorNotNext
        { next with TargetCursor = { next.TargetCursor with Ordinal = 9UL } } catalog

[<Fact>]
let ``a target cannot change revision session or regress its acceptance`` () =
    let catalog = empty ()
    let next = transaction catalog
    refuses ScopedPublicationError.TargetSessionMismatch
        { next with TargetRevision = { next.TargetRevision with Session = "other-workspace" } } catalog
    let newerCatalog = { catalog with CheckedRevision = revision 4UL }
    let delivery = transaction newerCatalog
    refuses ScopedPublicationError.TargetRevisionOlder
        { delivery with TargetRevision = revision 3UL } newerCatalog

[<Fact>]
let ``unchanged content requires an explicit target revision disposition`` () =
    let selected = scope "settled" 1UL []
    let catalog = withScope selected
    refuses (ScopedPublicationError.MissingDisposition "settled") (transaction catalog) catalog
    Assert.Equal(revision 2UL, catalog.Authorizations["settled"].CheckedRevision)

[<Fact>]
let ``unchanged content can be reauthorized without replacing metadata`` () =
    let selected = scope "settled" 1UL []
    let catalog = withScope selected
    let next = transaction catalog
    let result = ScopedPublication.apply
                     { next with Authorizations = [ authorize next.TargetRevision selected ] } catalog |> accepted
    Assert.Equal<Map<string, ScopeDescriptor>>(catalog.Scopes, result.Scopes)
    Assert.Equal(next.TargetRevision, result.Authorizations["settled"].CheckedRevision)

[<Fact>]
let ``withdrawing authority retains metadata but no current authorization`` () =
    let selected = scope "settled" 1UL []
    let catalog = withScope selected
    let next = transaction catalog
    let result = ScopedPublication.apply { next with Withdrawals = [ selected.Content ] } catalog |> accepted
    Assert.Equal<Map<string, ScopeDescriptor>>(catalog.Scopes, result.Scopes)
    Assert.Empty result.Authorizations

[<Fact>]
let ``a duplicate authorization or authorization plus withdrawal is refused`` () =
    let selected = scope "settled" 1UL []
    let catalog = withScope selected
    let next = transaction catalog
    let auth = authorize next.TargetRevision selected
    refuses (ScopedPublicationError.DuplicateDisposition "settled")
        { next with Authorizations = [ auth; auth ] } catalog
    refuses (ScopedPublicationError.DuplicateDisposition "settled")
        { next with Authorizations = [ auth ]; Withdrawals = [ selected.Content ] } catalog

[<Fact>]
let ``omitting an absence or membership support cannot authorize unchanged content`` () =
    let selected = scope "settled" 1UL []
    let catalog = withScope selected
    let next = transaction catalog
    let auth = authorize next.TargetRevision selected
    for omitted in [ SupportKey.Absence "higher-priority-candidate"; SupportKey.CollectionMembership "overload-candidates" ] do
        refuses (ScopedPublicationError.SupportAccountMismatch "settled")
            { next with Authorizations = [ { auth with Supports = auth.Supports |> List.filter (fun held -> held.Key <> omitted) } ] } catalog

[<Fact>]
let ``extra and duplicate supports are refused instead of silently normalized`` () =
    let selected = scope "settled" 1UL []
    let catalog = withScope selected
    let next = transaction catalog
    let auth = authorize next.TargetRevision selected
    let extra = { Key = SupportKey.Rule "undeclared-rule"; Version = 1UL }
    refuses (ScopedPublicationError.SupportAccountMismatch "settled")
        { next with Authorizations = [ { auth with Supports = extra :: auth.Supports } ] } catalog
    let duplicate = auth.Supports.Head
    refuses (ScopedPublicationError.DuplicateSupport("settled", duplicate.Key))
        { next with Authorizations = [ { auth with Supports = duplicate :: auth.Supports } ] } catalog

[<Fact>]
let ``boundary authority must match the exact declared version`` () =
    let selected = scope "settled" 1UL []
    let catalog = withScope selected
    let next = transaction catalog
    let auth = authorize next.TargetRevision selected
    refuses (ScopedPublicationError.BoundaryAccountMismatch "settled")
        { next with Authorizations = [ { auth with Boundaries = [ { boundary with Version = 4UL } ] } ] } catalog
    refuses (ScopedPublicationError.DuplicateBoundary("settled", boundary))
        { next with Authorizations = [ { auth with Boundaries = [ boundary; boundary ] } ] } catalog

[<Fact>]
let ``an old checked revision cannot authorize the target even with equal content`` () =
    let selected = scope "settled" 1UL []
    let catalog = withScope selected
    let next = transaction catalog
    refuses (ScopedPublicationError.AuthorizationRevisionMismatch "settled")
        { next with Authorizations = [ catalog.Authorizations["settled"] ] } catalog

[<Fact>]
let ``replacement requires the exact previous content and a newer same identity`` () =
    let selected = scope "settled" 1UL []
    let catalog = withScope selected
    let next = transaction catalog
    let replacement = scope "settled" 2UL []
    let supplied =
        { next with Changes = [ ScopeChange.Replace(selected.Content, replacement) ]
                    Authorizations = [ authorize next.TargetRevision replacement ] }
    ScopedPublication.apply supplied catalog |> accepted |> ignore
    refuses (ScopedPublicationError.PreviousContentMismatch "settled")
        { supplied with Changes = [ ScopeChange.Replace(stamp "settled" 9UL, replacement) ] } catalog
    refuses (ScopedPublicationError.ReplacementVersionNotLater "settled")
        { supplied with Changes = [ ScopeChange.Replace(selected.Content, selected) ]
                        Authorizations = [ authorize next.TargetRevision selected ] } catalog
    refuses (ScopedPublicationError.ReplacementIdentityMismatch "settled")
        { supplied with Changes = [ ScopeChange.Replace(selected.Content, scope "different" 2UL []) ] } catalog

[<Fact>]
let ``a scope cannot omit the context of a declared live occurrence`` () =
    let catalog = empty ()
    let next = transaction catalog
    let incomplete = { scope "selected" 1UL [] with ContextBreadcrumbs = Map.empty }
    refuses (ScopedPublicationError.IncompleteOccurrenceContext "selected")
        { next with Changes = [ ScopeChange.Add incomplete ]
                    Authorizations = [ authorize next.TargetRevision incomplete ] } catalog

[<Fact>]
let ``a context parent handle does not require its body to be selected`` () =
    let selected = scope "selected" 1UL []
    let catalog = withScope selected
    Assert.False(selected.LiveOccurrences.Contains(NodeId 2))
    Assert.Equal<OccurrenceBreadcrumb list list>([ [ breadcrumb 2 [] [] ] ], catalog.Scopes["selected"].ContextBreadcrumbs[NodeId 7])

[<Fact>]
let ``one shared body can retain several actual occurrence contexts`` () =
    let contexts = [ [ breadcrumb 2 [] [ NodeId 8 ] ]; [ breadcrumb 3 [ NodeId 9 ] [] ] ]
    let selected = { scope "shared" 1UL [] with ContextBreadcrumbs = Map.ofList [ (NodeId 7, contexts) ] }
    let catalog = withScope selected
    Assert.Equal<OccurrenceBreadcrumb list list>(contexts, catalog.Scopes["shared"].ContextBreadcrumbs[NodeId 7])

[<Fact>]
let ``a root context is explicit and an empty occurrence inventory is refused`` () =
    let selected = { scope "root" 1UL [] with ContextBreadcrumbs = Map.ofList [ (NodeId 7, [ [] ]) ] }
    withScope selected |> ignore
    let incomplete = { selected with ContextBreadcrumbs = Map.ofList [ (NodeId 7, []) ] }
    let catalog = empty ()
    let next = transaction catalog
    refuses (ScopedPublicationError.IncompleteOccurrenceContext "root")
        { next with Changes = [ ScopeChange.Add incomplete ]; Authorizations = [ authorize next.TargetRevision incomplete ] } catalog

[<Fact>]
let ``stored context ordinals preserve declared positions`` () =
    let malformed = { breadcrumb 2 [ NodeId 8 ] [] with Ordinal = 4 }
    let selected = { scope "selected" 1UL [] with ContextBreadcrumbs = Map.ofList [ (NodeId 7, [ [ malformed ] ]) ] }
    let catalog = empty ()
    let next = transaction catalog
    refuses (ScopedPublicationError.InvalidContextPosition(NodeId 7, NodeId 2, 4, 2))
        { next with Changes = [ ScopeChange.Add selected ]; Authorizations = [ authorize next.TargetRevision selected ] } catalog

[<Fact>]
let ``retirement must explicitly account for definition storage and activation owners`` () =
    let selected =
        scope "old" 1UL [ ArtifactHandle.Definition("entry", 1UL); ArtifactHandle.Storage("frame", 1UL)
                          ArtifactHandle.Activation("continuation", 1UL) ]
    let catalog = withScope selected
    let next = { transaction catalog with Changes = [ ScopeChange.Retire selected.Content ] }
    refuses ScopedPublicationError.ArtifactAccountMismatch next catalog
    let partial = owners selected |> Set.filter (fun owner -> owner.Artifact <> ArtifactHandle.Storage("frame", 1UL))
    refuses ScopedPublicationError.ArtifactAccountMismatch
        { next with ArtifactTransitions = [ { Previous = partial; Current = Set.empty } ] } catalog
    let result = ScopedPublication.apply
                     { next with ArtifactTransitions = [ { Previous = owners selected; Current = Set.empty } ] } catalog |> accepted
    Assert.Empty result.Scopes
    Assert.Empty result.Authorizations

[<Fact>]
let ``split and merge require complete explicit artifact ownership transitions`` () =
    let definition = ArtifactHandle.Definition("entry", 1UL)
    let storage = ArtifactHandle.Storage("frame", 1UL)
    let old = scope "joined" 1UL [ definition; storage ]
    let catalog = withScope old
    let left = scope "definition-owner" 1UL [ definition ]
    let right = scope "storage-owner" 1UL [ storage ]
    let next = transaction catalog
    let split =
        { next with Changes = [ ScopeChange.Retire old.Content; ScopeChange.Add left; ScopeChange.Add right ]
                    Authorizations = [ authorize next.TargetRevision left; authorize next.TargetRevision right ]
                    ArtifactTransitions = [ { Previous = owners old; Current = Set.union (owners left) (owners right) } ] }
    let splitCatalog = ScopedPublication.apply split catalog |> accepted
    refuses ScopedPublicationError.ArtifactAccountMismatch
        { split with ArtifactTransitions = [ { Previous = owners old; Current = owners left } ] } catalog
    let joined = scope "rejoined" 1UL [ definition; storage ]
    let mergeBase = transaction splitCatalog
    let merge =
        { mergeBase with Changes = [ ScopeChange.Retire left.Content; ScopeChange.Retire right.Content; ScopeChange.Add joined ]
                         Authorizations = [ authorize mergeBase.TargetRevision joined ]
                         ArtifactTransitions = [ { Previous = Set.union (owners left) (owners right); Current = owners joined } ] }
    let result = ScopedPublication.apply merge splitCatalog |> accepted
    Assert.Single(result.Scopes) |> ignore
    Assert.True(result.Scopes.ContainsKey "rejoined")
    refuses ScopedPublicationError.ArtifactAccountMismatch
        { merge with ArtifactTransitions = [ { Previous = owners left; Current = owners joined } ] } splitCatalog

[<Fact>]
let ``duplicate artifact transition accounting is refused atomically`` () =
    let selected = scope "old" 1UL [ ArtifactHandle.Definition("entry", 1UL) ]
    let catalog = withScope selected
    let next = transaction catalog
    let transition = { Previous = owners selected; Current = Set.empty }
    refuses (ScopedPublicationError.DuplicatePreviousArtifactOwner (owners selected |> Set.toList |> List.head))
        { next with Changes = [ ScopeChange.Retire selected.Content ]
                    ArtifactTransitions = [ transition; transition ] } catalog
    Assert.True(catalog.Scopes.ContainsKey "old")
    Assert.True(catalog.Authorizations.ContainsKey "old")
