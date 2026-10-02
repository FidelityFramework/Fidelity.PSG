module Fidelity.PSG.Tests.LiveOccurrenceSectionTests

open Xunit
open Fidelity.PSG

let private stamp identity version : ScopeContentStamp = { Identity = identity; Version = version }
let private boundary : BoundaryContractStamp = { Identity = "imported-child-contract"; Version = 2UL }
let private support = SupportKey.Absence "child-has-no-executable-demand"
let private local child ordinal = { Ordinal = ordinal; Traversal = ChildTraversal.EnterLocal(NodeId child) }
let private omitted child ordinal = { Ordinal = ordinal; Traversal = ChildTraversal.SourceOmitted(support, NodeId child) }
let private imported child ordinal =
    { Ordinal = ordinal; Traversal = ChildTraversal.EnterImported(stamp "resident-child" 3UL, boundary, NodeId child) }
let private body number children =
    let kind =
        if List.isEmpty children then SemanticKind.Literal(NativeLiteral.Bool true)
        else SemanticKind.Sequential(List.map NodeId children)
    Build.node number kind children
let private breadcrumb parent left right : OccurrenceBreadcrumb =
    { Parent = NodeId parent; Port = OccurrencePort.StructuralChild; Ordinal = List.length left
      Extent = List.length left + 1 + List.length right; Stamp = "source-port" }
let private occurrence (node: SemanticNode) (dispositions: ChildDisposition list)
                       (contexts: OccurrenceBreadcrumb list list) : LiveOccurrence =
    { Body = node; Children = dispositions; OccurrenceContexts = contexts }
let private section (occurrences: LiveOccurrence list) : LiveOccurrenceSection =
    let rows = occurrences |> List.map (fun held -> held.Body.Id, held) |> Map.ofList
    { Descriptor =
        { Content = stamp "selected" 1UL; LiveOccurrences = rows |> Map.toSeq |> Seq.map fst |> Set.ofSeq
          ContextBreadcrumbs = rows |> Map.map (fun _ held -> held.OccurrenceContexts)
          RequiredBoundaries = Set.singleton boundary; RequiredSupports = Set.singleton support; OwnedArtifacts = Set.empty }
      Occurrences = rows }
let private holds violation value =
    let violations = LiveOccurrenceSection.check value
    Assert.True(List.contains violation violations, sprintf "Expected %A in %A" violation violations)
let private valid value = Assert.Empty(LiveOccurrenceSection.check value)
let private parentWith children dispositions = occurrence (body 1 children) dispositions [ [] ]
let private child = occurrence (body 2 []) [] [ [ breadcrumb 1 [] [] ] ]

[<Fact>]
let ``a live section contains only its declared bodies and source child account`` () =
    section [ parentWith [ 2 ] [ local 2 0 ]; child ] |> valid

[<Fact>]
let ``inactive bodies are refused even when all other stored rows agree`` () =
    let inactive = { child with Body = { child.Body with IsReachable = false } }
    section [ parentWith [ 2 ] [ local 2 0 ]; inactive ]
    |> holds (LiveOccurrenceViolation.InactiveBody(NodeId 2))

[<Fact>]
let ``a body map cannot misfile an identity or omit a declared body`` () =
    let value = section [ child ]
    { value with Occurrences = Map.ofList [ (NodeId 2, { child with Body = body 9 [] }) ] }
    |> holds (LiveOccurrenceViolation.MisfiledBody(NodeId 2, NodeId 9))
    { value with Occurrences = Map.empty } |> holds LiveOccurrenceViolation.OccurrenceAccountMismatch

[<Fact>]
let ``every original child needs exactly one ordinal disposition`` () =
    section [ parentWith [ 2 ] []; child ] |> holds (LiveOccurrenceViolation.ChildCountMismatch(NodeId 1))
    section [ parentWith [ 2 ] [ local 2 0; local 2 1 ]; child ]
    |> holds (LiveOccurrenceViolation.ChildCountMismatch(NodeId 1))
    section [ parentWith [ 2 ] [ local 2 4 ]; child ]
    |> holds (LiveOccurrenceViolation.ChildOrdinalMismatch(NodeId 1, 0, 4))

[<Fact>]
let ``the child account preserves original identity and order`` () =
    let third = occurrence (body 3 []) [] [ [ breadcrumb 1 [ NodeId 2 ] [] ] ]
    section [ parentWith [ 2; 3 ] [ local 3 0; local 2 1 ]; child; third ]
    |> holds (LiveOccurrenceViolation.ChildIdentityMismatch(NodeId 1, 0, NodeId 2, NodeId 3))

[<Fact>]
let ``a declared local child must have a selected live body`` () =
    section [ parentWith [ 2 ] [ local 2 0 ] ]
    |> holds (LiveOccurrenceViolation.MissingLocalChild(NodeId 1, 0, NodeId 2))

[<Fact>]
let ``source omission does not request the omitted child body`` () =
    let parent = parentWith [ 99 ] [ omitted 99 0 ]
    let value = section [ parent ]
    valid value
    Assert.False(value.Occurrences.ContainsKey(NodeId 99))
    Assert.Equal<NodeId list>([ NodeId 99 ], value.Occurrences[NodeId 1].Body.Children)

[<Fact>]
let ``an omission must identify a declared source support`` () =
    let value = section [ parentWith [ 99 ] [ omitted 99 0 ] ]
    { value with Descriptor = { value.Descriptor with RequiredSupports = Set.empty } }
    |> holds (LiveOccurrenceViolation.UndeclaredOmissionSupport(NodeId 1, 0, support))

[<Fact>]
let ``an imported child carries an exact declared boundary instead of a body`` () =
    let value = section [ parentWith [ 99 ] [ imported 99 0 ] ]
    valid value
    Assert.False(value.Occurrences.ContainsKey(NodeId 99))
    { value with Descriptor = { value.Descriptor with RequiredBoundaries = Set.singleton { boundary with Version = 9UL } } }
    |> holds (LiveOccurrenceViolation.UndeclaredImportBoundary(NodeId 1, 0, boundary))

[<Fact>]
let ``an import cannot hide a missing child behind the local scope identity`` () =
    let disguised =
        { Ordinal = 0
          Traversal = ChildTraversal.EnterImported(stamp "selected" 7UL, boundary, NodeId 99) }
    section [ parentWith [ 99 ] [ disguised ] ] |> holds (LiveOccurrenceViolation.SelfImport(NodeId 1, 0))

[<Fact>]
let ``repeated child identities preserve separate original ordinals and paths`` () =
    let repeated =
        { child with OccurrenceContexts =
                         [ [ breadcrumb 1 [] [ NodeId 2 ] ]; [ breadcrumb 1 [ NodeId 2 ] [] ] ] }
    let value = section [ parentWith [ 2; 2 ] [ local 2 0; local 2 1 ]; repeated ]
    valid value
    Assert.Equal(2, value.Occurrences[NodeId 1].Children.Length)
    Assert.Equal(2, value.Occurrences[NodeId 2].OccurrenceContexts.Length)
    section [ parentWith [ 2; 2 ] [ local 2 0; local 2 0 ]; repeated ]
    |> holds (LiveOccurrenceViolation.ChildOrdinalMismatch(NodeId 1, 1, 0))

[<Fact>]
let ``context handles retain absent ancestors and siblings without their bodies`` () =
    let contexts = [ [ breadcrumb 80 [ NodeId 81 ] [ NodeId 82 ] ] ]
    let selected = { child with OccurrenceContexts = contexts }
    let value = section [ selected ]
    valid value
    Assert.Equal(1, value.Occurrences.Count)
    Assert.False(value.Occurrences.ContainsKey(NodeId 80))
    Assert.False(value.Occurrences.ContainsKey(NodeId 81))
    Assert.False(value.Occurrences.ContainsKey(NodeId 82))

[<Fact>]
let ``occurrence contexts must exactly match the declared inventory`` () =
    let value = section [ child ]
    { value with Occurrences = Map.ofList [ (NodeId 2, { child with OccurrenceContexts = [ [] ] }) ] }
    |> holds (LiveOccurrenceViolation.OccurrenceContextMismatch(NodeId 2))
    { value with Descriptor = { value.Descriptor with ContextBreadcrumbs = Map.empty } }
    |> holds LiveOccurrenceViolation.ContextAccountMismatch
    let missing = { child with OccurrenceContexts = [] }
    section [ missing ] |> holds (LiveOccurrenceViolation.MissingOccurrenceContexts(NodeId 2))

[<Fact>]
let ``a module declaration context preserves membership outside execution children`` () =
    let moduleBody = { body 80 [] with Kind = SemanticKind.ModuleDef("source-module", [ NodeId 2; NodeId 99 ]) }
    let declaration =
        { breadcrumb 80 [] [ NodeId 99 ] with Port = OccurrencePort.ModuleDeclaration }
    let selected = { child with OccurrenceContexts = [ [ declaration ] ] }
    let value = section [ occurrence moduleBody [] [ [] ]; selected ]
    valid value
    Assert.Empty(value.Occurrences[NodeId 80].Body.Children)
    Assert.Equal(OccurrencePort.ModuleDeclaration, value.Occurrences[NodeId 2].OccurrenceContexts.Head.Head.Port)
    Assert.False(value.Occurrences.ContainsKey(NodeId 99))

[<Fact>]
let ``a context ordinal must lie within its exact source port extent`` () =
    let malformed = { breadcrumb 80 [ NodeId 81 ] [] with Ordinal = 7 }
    let value = section [ { child with OccurrenceContexts = [ [ malformed ] ] } ]
    value |> holds (LiveOccurrenceViolation.InvalidContextPosition(NodeId 2, NodeId 80, 7, 2))

let private delivery value changes : OccurrenceDelivery =
    { Transaction =
        { BaseCursor = { Subscription = "subscriber"; Ordinal = 0UL }
          BaseRevision = { Session = "workspace"; Ordinal = 0UL }
          TargetCursor = { Subscription = "subscriber"; Ordinal = 1UL }
          TargetRevision = { Session = "workspace"; Ordinal = 0UL }
          Changes = changes; Authorizations = []; Withdrawals = []; ArtifactTransitions = [] }
      Sections = value }
let private deliveryHolds violation value =
    let violations = OccurrenceDelivery.check value
    Assert.True(List.contains violation violations, sprintf "Expected %A in %A" violation violations)

[<Fact>]
let ``an added or replaced scope carries one exact occurrence section`` () =
    let value = section [ child ]
    delivery [ value ] [ ScopeChange.Add value.Descriptor ] |> OccurrenceDelivery.check |> Assert.Empty
    delivery [ value ] [ ScopeChange.Replace(stamp "selected" 0UL, value.Descriptor) ]
    |> OccurrenceDelivery.check |> Assert.Empty

[<Fact>]
let ``an add cannot leave its required occurrence section absent`` () =
    let value = section [ child ]
    delivery [] [ ScopeChange.Add value.Descriptor ]
    |> deliveryHolds (OccurrenceDeliveryViolation.MissingSection value.Descriptor.Content)

[<Fact>]
let ``duplicate sections and duplicate change descriptors are refused`` () =
    let value = section [ child ]
    delivery [ value; value ] [ ScopeChange.Add value.Descriptor ]
    |> deliveryHolds (OccurrenceDeliveryViolation.DuplicateSection "selected")
    delivery [ value ] [ ScopeChange.Add value.Descriptor; ScopeChange.Add value.Descriptor ]
    |> deliveryHolds (OccurrenceDeliveryViolation.DuplicateChangeDescriptor "selected")

[<Fact>]
let ``sections cannot smuggle occurrence bodies into retirement or unchanged reauthorization`` () =
    let value = section [ child ]
    delivery [ value ] [ ScopeChange.Retire value.Descriptor.Content ]
    |> deliveryHolds (OccurrenceDeliveryViolation.UnexpectedSection value.Descriptor.Content)
    let unchanged = delivery [] []
    let authorization =
        { Content = value.Descriptor.Content; CheckedRevision = unchanged.Transaction.TargetRevision
          Boundaries = Set.toList value.Descriptor.RequiredBoundaries
          Supports = value.Descriptor.RequiredSupports |> Set.toList |> List.map (fun key -> { Key = key; Version = 0UL }) }
    let renewed = { unchanged with Transaction = { unchanged.Transaction with Authorizations = [ authorization ] } }
    renewed |> OccurrenceDelivery.check |> Assert.Empty
    { renewed with Sections = [ value ] }
    |> deliveryHolds (OccurrenceDeliveryViolation.UnexpectedSection value.Descriptor.Content)

[<Fact>]
let ``section metadata must match the descriptor declared by its change`` () =
    let value = section [ child ]
    let declared = { value.Descriptor with RequiredSupports = Set.empty }
    delivery [ value ] [ ScopeChange.Add declared ]
    |> deliveryHolds (OccurrenceDeliveryViolation.DescriptorMismatch(declared.Content, value.Descriptor.Content))
    let newer = { value.Descriptor with Content = stamp "selected" 2UL }
    delivery [ value ] [ ScopeChange.Add newer ]
    |> deliveryHolds (OccurrenceDeliveryViolation.DescriptorMismatch(newer.Content, value.Descriptor.Content))

[<Fact>]
let ``delivery rejects invalid sections rather than accepting matching headers`` () =
    let value = section [ { child with Body = { child.Body with IsReachable = false } } ]
    delivery [ value ] [ ScopeChange.Add value.Descriptor ]
    |> deliveryHolds (OccurrenceDeliveryViolation.InvalidSection(value.Descriptor.Content, [ LiveOccurrenceViolation.InactiveBody(NodeId 2) ]))
