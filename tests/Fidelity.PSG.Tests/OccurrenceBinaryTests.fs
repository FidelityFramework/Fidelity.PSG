module Fidelity.PSG.Tests.OccurrenceBinaryTests

open Xunit
open Fidelity.PSG
open BAREWire.Memory

let private take = function Ok value -> value | Error error -> failwithf "%A" error
let private limits : BinaryLimits =
    { MaxBytes = 1024 * 1024; MaxCollectionLength = 10000; MaxDepth = 128
      MaxStringBytes = 65536; MaxBigIntegerBytes = 64; MaxValues = 100000 }
let private revision : CheckedRevisionId = { Session = "source-session"; Ordinal = 0UL }
let private support = SupportKey.WholeOwningAnalysisRegion "source-owner"
let private stamp : ScopeContentStamp = { Identity = "demanded"; Version = 1UL }
let private childContext : OccurrenceBreadcrumb =
    { Parent = NodeId 1; Port = OccurrencePort.StructuralChild; Ordinal = 0
      Extent = 2; Stamp = "source-parent-port" }
let private parent = Build.node 1 (SemanticKind.Sequential [NodeId 2; NodeId 99]) [2; 99]
let private child = { Build.node 2 (SemanticKind.Literal(NativeLiteral.Bool true)) [] with Parent = Some(NodeId 1) }
let private descriptor : ScopeDescriptor =
    { Content = stamp; LiveOccurrences = Set.ofList [NodeId 1; NodeId 2]
      ContextBreadcrumbs = Map.ofList [NodeId 1, [[]]; NodeId 2, [[childContext]]]
      RequiredBoundaries = Set.empty; RequiredSupports = Set.singleton support; OwnedArtifacts = Set.empty }
let private section : LiveOccurrenceSection =
    { Descriptor = descriptor
      Occurrences = Map.ofList [
          NodeId 1, { Body = parent; OccurrenceContexts = [[]]
                      Children = [{Ordinal = 0; Traversal = ChildTraversal.EnterLocal(NodeId 2)}
                                  {Ordinal = 1; Traversal = ChildTraversal.SourceOmitted(support, NodeId 99)}] }
          NodeId 2, { Body = child; OccurrenceContexts = [[childContext]]; Children = [] } ] }
let private authorization checkedRevision : ScopeAuthorization =
    { Content = stamp; CheckedRevision = checkedRevision; Boundaries = []; Supports = [{Key = support; Version = 7UL}] }
let private catalog = ScopedPublication.start "receiver" revision |> take
let private initial : OccurrenceDelivery =
    { Transaction =
        { BaseCursor = catalog.Cursor; BaseRevision = revision
          TargetCursor = {catalog.Cursor with Ordinal = 1UL}; TargetRevision = revision
          Changes = [ScopeChange.Add descriptor]; Authorizations = [authorization revision]
          Withdrawals = []; ArtifactTransitions = [] }
      Sections = [section] }
let private encode value = OccurrenceBinary.encode limits value |> take
let private decode bytes = OccurrenceBinary.decode limits bytes |> take

[<Fact>]
let ``scoped occurrence codec roundtrips live bodies without omitted child body`` () =
    let received = initial |> encode |> decode
    Assert.Equal<OccurrenceDelivery>(initial, received)
    Assert.Equal(2, received.Sections[0].Occurrences.Count)
    Assert.False(received.Sections[0].Occurrences.ContainsKey(NodeId 99))
    let context = received.Sections.[0].Descriptor.ContextBreadcrumbs.[NodeId 2].[0].[0]
    Assert.Equal(0, context.Ordinal)
    Assert.Equal(2, context.Extent)
    Assert.Equal("source-parent-port", context.Stamp)
    Assert.Equal(1UL, (ScopedPublication.apply received.Transaction catalog |> take).Cursor.Ordinal)

[<Fact>]
let ``unchanged reauthorization delivers no settled bodies and still requires exact base`` () =
    let resident = ScopedPublication.apply initial.Transaction catalog |> take
    let nextRevision = {revision with Ordinal = 1UL}
    let update =
        { Transaction =
            { initial.Transaction with BaseCursor = resident.Cursor; BaseRevision = resident.CheckedRevision
                                       TargetCursor = {resident.Cursor with Ordinal = 2UL}; TargetRevision = nextRevision
                                       Changes = []; Authorizations = [authorization nextRevision] }
          Sections = [] }
    let bytes = encode update
    let received = decode bytes
    Assert.Empty(received.Sections)
    Assert.True(bytes.Length < (encode initial).Length)
    let installed = ScopedPublication.apply received.Transaction resident |> take
    Assert.Equal(nextRevision, installed.Authorizations[stamp.Identity].CheckedRevision)
    match ScopedPublication.apply received.Transaction catalog with
    | Error errors -> Assert.Contains(ScopedPublicationError.BaseCursorMismatch, errors)
    | Ok _ -> failwith "Accepted an occurrence delta against another resident base"

[<Fact>]
let ``inactive body cannot be encoded even with matching declared metadata`` () =
    let inactive = { section.Occurrences[NodeId 2] with Body = {child with IsReachable = false} }
    let packet = {initial with Sections = [{section with Occurrences = Map.add (NodeId 2) inactive section.Occurrences}]}
    match OccurrenceBinary.encode limits packet with
    | Error(BinaryError.InvalidOccurrenceDelivery errors) ->
        Assert.Contains(OccurrenceDeliveryViolation.InvalidSection(stamp, [LiveOccurrenceViolation.InactiveBody(NodeId 2)]), errors)
    | other -> failwithf "Expected inactive body refusal: %A" other

[<Fact>]
let ``retirement cannot carry a node section`` () =
    let packet = {initial with Transaction = {initial.Transaction with Changes = [ScopeChange.Retire stamp]}}
    match OccurrenceBinary.encode limits packet with
    | Error(BinaryError.InvalidOccurrenceDelivery errors) -> Assert.Contains(OccurrenceDeliveryViolation.UnexpectedSection stamp, errors)
    | other -> failwithf "Expected retirement body refusal: %A" other

[<Fact>]
let ``complete revision magic is refused by scoped reader without alternate decoder`` () =
    let complete = Binary.encode limits Build.bindingWithLiteral |> take
    match OccurrenceBinary.decode limits complete with
    | Error(BinaryError.Malformed(0, reason)) -> Assert.Equal("Unknown occurrence image magic", reason)
    | other -> failwithf "Accepted complete revision as an occurrence packet: %A" other
    match Binary.decode limits (encode initial) with
    | Error(BinaryError.Malformed(0, _)) -> ()
    | other -> failwithf "Accepted occurrence packet as complete revision: %A" other

[<Fact>]
let ``scope envelope refuses unknown format schema contract and inconsistent extents`` () =
    let bytes = encode initial
    let mutate at value = let altered = Array.copy bytes in altered[at] <- value; altered
    match OccurrenceBinary.decode limits (mutate 8 2uy) with
    | Error(BinaryError.UnsupportedFormat 2u) -> () | other -> failwithf "%A" other
    match OccurrenceBinary.decode limits (mutate 12 15uy) with
    | Error(BinaryError.SchemaMismatch(14, 15)) -> () | other -> failwithf "%A" other
    match OccurrenceBinary.decode limits (mutate 16 (bytes[16] ^^^ 1uy)) with
    | Error BinaryError.ContractMismatch -> () | other -> failwithf "%A" other
    for offset in [48; 56] do
        match OccurrenceBinary.decode limits (mutate offset (bytes[offset] ^^^ 1uy)) with
        | Error(BinaryError.Malformed(48, _)) -> () | other -> failwithf "%A" other

[<Fact>]
let ``every truncated occurrence packet and appended byte is refused`` () =
    let bytes = encode initial
    for length in 0 .. bytes.Length - 1 do
        Assert.True(OccurrenceBinary.decode limits bytes[..length - 1] |> Result.isError, sprintf "Accepted occurrence truncation %d" length)
    Assert.True(OccurrenceBinary.decode limits (Array.append bytes [|0uy|]) |> Result.isError)

[<Fact>]
let ``occurrence codec enforces byte bounds before mapping any body`` () =
    let bytes = encode initial
    let bound = {limits with MaxBytes = bytes.Length - 1; MaxStringBytes = 32}
    match OccurrenceBinary.decode bound bytes with
    | Error(BinaryError.LimitExceeded("MaxBytes", 0)) -> () | other -> failwithf "%A" other
    Assert.True(OccurrenceBinary.encode bound initial |> Result.isError)

[<Fact>]
let ``stable host byte source uses the same scoped reading`` () =
    let view = OccurrenceBinary.openSource limits (initial |> encode |> ByteSource.ofArray) |> take
    Assert.Equal<OccurrenceDelivery>(initial, OccurrenceBinary.readDelivery view |> take)
