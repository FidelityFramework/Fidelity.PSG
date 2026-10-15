/// These fixtures state contract rows. They neither admit source residence nor
/// discharge a source or artifact obligation on behalf of the compiler.
module Fidelity.PSG.Tests.ArtifactAccountTests

open Xunit
open Fidelity.PSG
open Fidelity.PSG.Tests.Build

let private participant role ordinal group node : Participant =
    { Node = NodeId node; Role = role; Ordinal = ordinal; Group = NodeId group }

let private obligation name kind body : ObligationInfo =
    { Id = name; Kind = kind; Logic = "QF_LIA"; Statement = "Contract fixture"
      Source = "contract-test.clef"; Refs = []; Body = body }

let private withStorage storage (original: Revision) =
    { original with Emission = { original.Emission with Storage = storage } }

let private hasViolation part (original: Revision) =
    Assert.Contains(Integrity.check original, fun violation -> violation.Part = part)
    match Binary.encode BinaryTests.limits original with
    | Error(BinaryError.InvalidRevision failures) ->
        Assert.Contains(failures, fun violation -> violation.Part = part)
    | other -> failwithf "An inconsistent artifact account was accepted: %A" other

/// Finite contract-value fixture for the imported-entry family. It states source
/// metadata; it does not grant source residence or execute the foreign function.
let private importedEntryAccount () =
    let signature = TypeIdentity.Function(unitType, unitType)

    let constructor name kind parameters : ConstructorIdentity =
        {
            Declaration = { Module = []; Name = name }
            Parameters = parameters
            NativeKind = kind
        }

    let pointerType =
        TypeIdentity.Application(constructor "FnPtr" (Some NTUKind.NTUfnptr) [ TypeParamKind.Type ], [ signature ])

    let intrinsic operation =
        SemanticKind.Intrinsic
            {
                Module = IntrinsicModule.FnPtr
                Operation = operation
                Category = IntrinsicCategory.Pure
                FullName = "FnPtr." + operation
            }

    let original =
        revision
            [
                { node 10 (SemanticKind.Binding("external", false, false, None)) [] with
                    Type = signature
                }
                { node 11 (SemanticKind.VarRef("external", Some(NodeId 10))) [] with
                    Type = signature
                }
                node 12 (intrinsic "ofExtern") []
                { node 13 (SemanticKind.Application(NodeId 12, [ NodeId 11 ])) [ 12; 11 ] with
                    Type = pointerType
                }
                { node 14 (SemanticKind.Binding("entry", false, false, None)) [ 13 ] with
                    Type = pointerType
                }
                { node 15 (SemanticKind.VarRef("entry", Some(NodeId 14))) [] with
                    Type = pointerType
                }
                node 16 (intrinsic "invoke") []
                node 17 (SemanticKind.Application(NodeId 16, [ NodeId 15; NodeId 19 ])) [ 16; 15; 19 ]
                node 19 (SemanticKind.Literal NativeLiteral.Unit) []
            ]

    let contract: BAREWire.Platform.ProcessLinkContract =
        {
            Identity = "fixture-libc"
            Version = "1"
            Source = "explicit-fixture-assumption"
            Library = "c"
            Runtime = "libc"
            Os = "linux"
            Arch = "x86_64"
            LoadAt = "ProcessStartup"
            LiveUntil = "ProcessTermination"
            Unloading = "Forbidden"
            ExportedLibrary = "Forbidden"
        }

    let fields =
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

    let namedType name =
        TypeIdentity.Application(constructor name None [], [])

    let fact form text references children parent ty : BoundaryDeclarationFact =
        {
            Form = form
            Text = text
            Numbers = []
            References = references
            Children = children
            Parent = parent
            SourceType = ty
        }

    let fieldRows =
        fields
        |> List.mapi (fun index (_, value) -> NodeId(40 + index), fact "string" [ value ] [] [] (Some(NodeId 30)) (namedType "string"))

    let fieldIds = fieldRows |> List.map fst

    let record =
        fact "record" (fields |> List.map fst) fieldIds fieldIds (Some(NodeId 31)) (namedType "ProcessLinkContract")

    let binding =
        { fact "binding" [ "loading" ] [ NodeId 30 ] [ NodeId 30 ] None record.SourceType with
            Numbers = [ 0I; 0I ]
        }

    let facts =
        [
            NodeId 30, record
            NodeId 31, binding
            NodeId 32, fact "record" [] [] [] None (namedType "PlatformDescription")
            NodeId 33, fact "record" [] [] [] None (namedType "TargetCore")
        ]
        @ fieldRows
        |> Map.ofList

    let loading: BoundaryLoading =
        {
            Identity = NodeId 30
            Binding = NodeId 31
            Selector = "Fixture.loading"
            Contract = contract
            Platform = NodeId 32
            Core = NodeId 33
            DeclarationFacts = facts
            Participants = facts.Keys |> Set.ofSeq
        }

    let imported: BoundaryImport =
        {
            Identity = NodeId 20
            Binding = NodeId 10
            Scope = NodeId 21
            Library = "c"
            Symbol = "fixture_external"
            CallingConvention = "cdecl"
            DeclarationPath = [ NodeId 10 ]
            Parameters = []
            Result = None
            Participants = Set.singleton (NodeId 10)
            SourceTypes = Map.empty
            DeclarationFacts = Map.empty
        }

    let transport =
        Set.ofList [ NodeId 10; NodeId 11; NodeId 12; NodeId 13; NodeId 14; NodeId 15 ]

    let entry: BoundaryEntry =
        {
            Formation = NodeId 13
            Operand = NodeId 11
            Import = imported.Identity
            Declaration = imported.Binding
            Loading = loading.Identity
            SourceType = pointerType
            Transport = transport
            Participants = Set.union transport loading.Participants
        }

    let call: BoundaryCall =
        {
            Site = NodeId 17
            Import = imported.Identity
            Callee = NodeId 15
            Entry = Some entry.Formation
            Arguments = []
            ErasedUnitArguments = [ NodeId 19 ]
            Result = None
            ResultAdaptation = None
            Participants = entry.Participants
            SourceTypes = Map.empty
        }

    { original with
        Codata =
            { original.Codata with
                FunctionPointers = Map.ofList [ entry.Formation, FunctionPointerPlan.ExternAddress entry.Formation ]
            }
        SourceReadings =
            { original.SourceReadings with
                ContextHeaders =
                    Map.ofList
                        [
                            NodeId 21,
                            {
                                Identity = NodeId 21
                                Name = "fixture"
                                Ports = Map.empty
                            }
                        ]
            }
        Emission =
            { original.Emission with
                Boundary =
                    { original.Emission.Boundary with
                        Loading = Some loading
                        Entries = Map.ofList [ entry.Formation, entry ]
                        Imports = Map.ofList [ imported.Identity, imported ]
                        Calls = Map.ofList [ call.Site, call ]
                        DeclarationLeaves = Set.singleton imported.Binding
                    }
            }
    }

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``imported entry accounts retain exact loading literals and refreshed source metadata`` refreshed =
    let original = importedEntryAccount ()
    let loading = original.Emission.Boundary.Loading.Value

    let loading =
        if not refreshed then
            loading
        else
            { loading with
                Contract = { loading.Contract with Version = "2" }
                DeclarationFacts =
                    loading.DeclarationFacts.Add(
                        NodeId 41,
                        { loading.DeclarationFacts[NodeId 41] with
                            Text = [ "2" ]
                        }
                    )
            }

    let original =
        { original with
            Emission =
                { original.Emission with
                    Boundary =
                        { original.Emission.Boundary with
                            Loading = Some loading
                        }
                }
        }

    Assert.Empty(Integrity.check original)
    let bytes = Binary.encode BinaryTests.limits original |> BinaryTests.take
    let copy = Binary.decode BinaryTests.limits bytes |> BinaryTests.take
    Assert.Equal(original.Emission.Boundary, copy.Emission.Boundary)
    Assert.Equal<Map<NodeId, FunctionPointerPlan>>(original.Codata.FunctionPointers, copy.Codata.FunctionPointers)

[<Theory>]
[<InlineData("loading-withdrawal", "Entries.Account")>]
[<InlineData("loading-version", "Loading.Contract")>]
[<InlineData("literal-withdrawal", "Loading.Contract")>]
[<InlineData("import-withdrawal", "Entries.Account")>]
[<InlineData("signature", "Entries.Signature")>]
[<InlineData("transport", "Calls.Entry")>]
[<InlineData("call-pointer", "Calls.Entry")>]
[<InlineData("ordered-actual", "Calls.Entry")>]
[<InlineData("plan", "Entries.Plan")>]
let ``imported entry accounts refuse stale loading import signature or pointer correspondence`` change suffix =
    let original = importedEntryAccount ()
    let boundary = original.Emission.Boundary
    let loading = boundary.Loading.Value
    let entry = boundary.Entries[NodeId 13]
    let call = boundary.Calls[NodeId 17]

    let boundary =
        match change with
        | "loading-withdrawal" -> { boundary with Loading = None }
        | "loading-version" ->
            { boundary with
                Loading =
                    Some
                        { loading with
                            Contract = { loading.Contract with Version = "2" }
                        }
            }
        | "literal-withdrawal" ->
            { boundary with
                Loading =
                    Some
                        { loading with
                            DeclarationFacts = loading.DeclarationFacts.Remove(NodeId 41)
                        }
            }
        | "import-withdrawal" -> { boundary with Imports = Map.empty }
        | "signature" ->
            { boundary with
                Entries = Map.ofList [ entry.Formation, { entry with SourceType = unitType } ]
            }
        | "transport" ->
            { boundary with
                Entries =
                    Map.ofList
                        [
                            entry.Formation,
                            { entry with
                                Transport = Set.remove call.Callee entry.Transport
                            }
                        ]
            }
        | "call-pointer" ->
            { boundary with
                Calls = Map.ofList [ call.Site, { call with Callee = NodeId 11 } ]
            }
        | "ordered-actual" ->
            { boundary with
                Calls = Map.ofList [ call.Site, { call with ErasedUnitArguments = [] } ]
            }
        | _ -> boundary

    let altered =
        { original with
            Emission =
                { original.Emission with
                    Boundary = boundary
                }
            Codata =
                if change = "plan" then
                    { original.Codata with
                        FunctionPointers = Map.empty
                    }
                else
                    original.Codata
        }

    let part = "Emission.Boundary." + suffix
    let reason =
        match suffix with
        | "Entries.Account" -> "The imported entry differs from its exact import, original declaration or selected loading account."
        | "Loading.Contract" -> "The selected loading contract differs from its immutable declaration and exact eleven literal fields."
        | "Entries.Signature" -> "The imported function pointer differs from its exact source declaration signature."
        | "Calls.Entry" -> "The indirect call differs from its exact imported entry, source pointer transport or ordered native ABI."
        | "Entries.Plan" -> "The imported entry lacks its formation-only ExternAddress plan."
        | other -> failwithf "Unknown declared refusal %s" other
    Assert.Contains(Integrity.check altered, fun violation -> violation.Part = part && violation.Reason = reason)
    hasViolation part altered

let private foreignResultAccount stated enclosure =
    let original = revision [node 1 (SemanticKind.Binding("read", false, false, None)) []
                             node 2 (SemanticKind.Application(NodeId 1, [NodeId 3])) [1; 3]
                             node 3 (SemanticKind.Literal NativeLiteral.Unit) []
                             node 4 (SemanticKind.Literal NativeLiteral.Unit) []
                             node 5 (SemanticKind.Literal NativeLiteral.Unit) []
                             node 6 (SemanticKind.Literal NativeLiteral.Unit) []
                             node 7 (SemanticKind.Literal NativeLiteral.Unit) []]
    let hypothesis : ForeignResultHypothesis =
        { Quote = NodeId 4; Declaration = NodeId 1; Identity = "posix-read"; Version = "profile-1"
          Source = "pilot/read"; Lower = ForeignResultBound.Constant -1I; Upper = ForeignResultBound.Argument 0 }
    let application : ForeignResultApplication =
        { Declaration = NodeId 1; Call = NodeId 2; Context = [NodeId 5]
          Hypothesis = if stated then Some hypothesis else None
          Arguments = [{Index = 0; Node = NodeId 3; Enclosure = enclosure}] }
    let ready = stated && enclosure <> ValueRange.Unbounded
    let roles = [ForeignResultProofRole.LogicalCoverage, NodeId 40; ForeignResultProofRole.AbiNarrowing, NodeId 41]
    let models = roles |> List.map (fun (role, citizen) ->
        let model : ForeignResultCoverageModel =
            { Application = application; Role = role
              ResultRange = if ready then ValueRange.Bounded(-1I, 1024I) else ValueRange.Unbounded
              Destination = if ready then ValueRange.Bounded(-32768I, 32767I) else ValueRange.Unbounded
              DestinationDeclaration = if ready then Some(NodeId 7) else None
              Abi = if ready then Some(NodeId 6) else None
              AbiRange = if ready then ValueRange.Bounded(-32768I, 32767I) else ValueRange.Unbounded
              AbiIdentity = if ready then Some "fixture:abi:incarnation-1" else None
              DestinationIdentity = if ready then Some "fixture:destination:incarnation-1" else None }
        citizen, obligation ("read-result:" + string role) "foreign-result-coverage" (ObligationBody.ForeignResultCoverage model))
    let participants =
        [participant ParticipantRole.ForeignResultDeclaration 0 2 1
         participant ParticipantRole.ForeignResultCall 0 2 2
         participant ParticipantRole.ForeignResultContext 0 2 5] @
        (if stated then [participant ParticipantRole.ForeignResultHypothesis 0 2 4] else []) @
        [participant ParticipantRole.ForeignResultActual 0 2 3] @
        (if ready then [participant ParticipantRole.ForeignResultAbi 0 2 6
                        participant ParticipantRole.ForeignResultDestination 0 2 7
                        participant ParticipantRole.ForeignResultAbi 1 2 6
                        participant ParticipantRole.ForeignResultDestination 1 2 7] else [])
    let account : ForeignResultUse =
        { Application = application; Claims = roles
          Participants = if ready then ParticipantEvidence.Established participants else ParticipantEvidence.Pending {Derived = participants} }
    let boundary = {original.Emission.Boundary with ResultHypotheses = if stated then [hypothesis] else []}
    let numeric = {original.Emission.Numeric with ForeignResultUses = [account]}
    { original with
        Emission = {original.Emission with Boundary = boundary; Numeric = numeric}
        CurrentClaims = Map.ofList models; Obligations = models |> List.map snd
        ObligationSources = roles |> List.map (fun (_, citizen) -> citizen, [participants |> List.map _.Node]) |> Map.ofList }

[<Theory>]
[<InlineData("ready")>]
[<InlineData("absent")>]
[<InlineData("unknown")>]
[<InlineData("unanchored")>]
let ``foreign result accounts retain conditional and pending model shape`` state =
    let original = foreignResultAccount (state <> "absent") (if state = "ready" || state = "unanchored" then ValueRange.Bounded(0I, 1024I) else ValueRange.Unbounded)
    let original =
        if state <> "unanchored" then original
        else
            let claims = original.CurrentClaims |> Map.map (fun _ info ->
                match info.Body with
                | ObligationBody.ForeignResultCoverage model ->
                    {info with Body = ObligationBody.ForeignResultCoverage {model with AbiIdentity = None; DestinationIdentity = None}}
                | _ -> info)
            {original with CurrentClaims = claims; Obligations = claims |> Map.toList |> List.map snd}
    let issues = Integrity.check original
    if state = "ready" || state = "unanchored" then
        // These contract-only Unit-node fixtures never issued the claimed ABI
        // import or selected destination. Real source-issued codec controls
        // live in ForeignReferenceTests, with those current premises retained.
        Assert.Contains(issues, fun issue -> issue.Part = "Emission.Numeric.ForeignResultUses.Abi"
                                           && issue.Reason = "A conditional ABI premise lacks its own call's imported declaration fact.")
        Assert.Contains(issues, fun issue -> issue.Part = "Emission.Numeric.ForeignResultUses.Destination"
                                           && issue.Reason = "A conditional destination premise differs from its own call's selected numeric carrier.")
        hasViolation "Emission.Numeric.ForeignResultUses.Abi" original
    else
        Assert.Empty issues
    if state = "absent" || state = "unknown" then
      let bytes = Binary.encode BinaryTests.limits original |> BinaryTests.take
      let copy = Binary.decode BinaryTests.limits bytes |> BinaryTests.take
      Assert.Equal<ForeignResultHypothesis list>(original.Emission.Boundary.ResultHypotheses, copy.Emission.Boundary.ResultHypotheses)
      Assert.Equal<ForeignResultUse list>(original.Emission.Numeric.ForeignResultUses, copy.Emission.Numeric.ForeignResultUses)
      Assert.Equal<Map<NodeId, ObligationInfo>>(original.CurrentClaims, copy.CurrentClaims)
      for KeyValue(_, claim) in copy.CurrentClaims do
          match claim.Body with
          | ObligationBody.ForeignResultCoverage model ->
              Assert.Equal(None, model.AbiIdentity)
              Assert.Equal(None, model.DestinationIdentity)
          | _ -> failwith "Conditional model was lost in the typed codec."
      Assert.Equal<byte>(bytes, Binary.encode BinaryTests.limits copy |> BinaryTests.take)
      Assert.Equal(2, copy.CurrentClaims.Count)
      let view = Binary.openSource BinaryTests.limits (BAREWire.Memory.ByteSource.ofArray bytes) |> BinaryTests.take
      let inspection = Fidelity.PSG.Json.Inspection.render false view |> BinaryTests.take
      Assert.Contains("ForeignResultUses", inspection)
      Assert.Contains("ForeignResultCoverage", inspection)
      if state <> "absent" then Assert.Contains("profile-1", inspection)
      else Assert.DoesNotContain("profile-1", inspection)

[<Fact>]
let ``foreign result absence retains the declaration and same role claim anchors`` () =
    let ready = foreignResultAccount true (ValueRange.Bounded(0I, 1024I))
    let pending = foreignResultAccount false ValueRange.Unbounded
    Assert.Equal<NodeId list>(ready.CurrentClaims |> Map.keys |> Seq.toList, pending.CurrentClaims |> Map.keys |> Seq.toList)
    Assert.Equal<(string * string) list>(ready.Obligations |> List.map (fun row -> row.Id, row.Source), pending.Obligations |> List.map (fun row -> row.Id, row.Source))
    let account = Assert.Single pending.Emission.Numeric.ForeignResultUses
    Assert.Equal(NodeId 1, account.Application.Declaration)
    Assert.Equal(None, account.Application.Hypothesis)
    match account.Participants with ParticipantEvidence.Pending _ -> () | _ -> failwith "Missing contract was not retained Pending."

[<Theory>]
[<InlineData("abi-empty")>]
[<InlineData("destination-empty")>]
[<InlineData("abi-unheld")>]
[<InlineData("destination-unheld")>]
let ``foreign premise provenance refuses blank anchors and anchors without premise nodes`` change =
    let original = foreignResultAccount true (ValueRange.Bounded(0I, 1024I))
    let claims = original.CurrentClaims |> Map.map (fun _ info ->
        match info.Body with
        | ObligationBody.ForeignResultCoverage model ->
            let changed =
                match change with
                | "abi-empty" -> {model with AbiIdentity = Some ""}
                | "destination-empty" -> {model with DestinationIdentity = Some " "}
                | "abi-unheld" -> {model with Abi = None}
                | "destination-unheld" -> {model with DestinationDeclaration = None}
                | _ -> failwith "Unknown provenance control"
            {info with Body = ObligationBody.ForeignResultCoverage changed}
        | _ -> info)
    hasViolation "Emission.Numeric.ForeignResultUses.Provenance" {original with CurrentClaims = claims; Obligations = claims |> Map.toList |> List.map snd}

[<Theory>]
[<InlineData("version", "Hypothesis")>]
[<InlineData("withdrawal", "Hypothesis")>]
[<InlineData("false-absence", "Hypothesis")>]
[<InlineData("declaration", "Hypothesis")>]
[<InlineData("duplicate", "Application")>]
[<InlineData("argument", "Arguments")>]
[<InlineData("claim", "Claims")>]
[<InlineData("dropped-use", "Claims")>]
[<InlineData("participants", "Participants")>]
[<InlineData("sources", "Sources")>]
let ``foreign result accounts refuse stale hypothesis and ledger crosslinks`` (change, suffix) =
    let original = foreignResultAccount true (ValueRange.Bounded(0I, 1024I))
    let boundary, numeric = original.Emission.Boundary, original.Emission.Numeric
    let account = List.head numeric.ForeignResultUses
    let altered =
        match change with
        | "version" -> {original with Emission = {original.Emission with Boundary = {boundary with ResultHypotheses = boundary.ResultHypotheses |> List.map (fun row -> {row with Version = "profile-2"})}}}
        | "withdrawal" -> {original with Emission = {original.Emission with Boundary = {boundary with ResultHypotheses = []}}}
        | "false-absence" -> {original with Emission = {original.Emission with Numeric = {numeric with ForeignResultUses = [{account with Application = {account.Application with Hypothesis = None}}]}}}
        | "declaration" -> {original with Emission = {original.Emission with Numeric = {numeric with ForeignResultUses = [{account with Application = {account.Application with Declaration = NodeId 7}}]}}}
        | "duplicate" -> {original with Emission = {original.Emission with Numeric = {numeric with ForeignResultUses = [account; account]}}}
        | "argument" -> {original with Emission = {original.Emission with Numeric = {numeric with ForeignResultUses = [{account with Application = {account.Application with Arguments = [{Index = 2; Node = NodeId 3; Enclosure = ValueRange.Bounded(0I, 1024I)}]}}]}}}
        | "claim" -> {original with CurrentClaims = original.CurrentClaims.Remove(NodeId 40)}
        | "dropped-use" -> {original with Emission = {original.Emission with Numeric = {numeric with ForeignResultUses = []}}}
        | "participants" -> {original with Emission = {original.Emission with Numeric = {numeric with ForeignResultUses = [{account with Participants = ParticipantEvidence.Established []}]}}}
        | "sources" -> {original with ObligationSources = original.ObligationSources.Add(NodeId 40, [[NodeId 2]])}
        | other -> failwithf "Unknown foreign result mutation %s" other
    hasViolation ("Emission.Numeric.ForeignResultUses." + suffix) altered

[<Theory>]
[<InlineData("identity")>]
[<InlineData("version")>]
[<InlineData("source")>]
let ``foreign result provenance refuses partially supplied hypotheses`` field =
    let original = foreignResultAccount true (ValueRange.Bounded(0I, 1024I))
    let malformed = original.Emission.Boundary.ResultHypotheses |> List.map (fun row ->
        match field with "identity" -> {row with Identity = ""} | "version" -> {row with Version = ""} | _ -> {row with Source = ""})
    hasViolation "Emission.Boundary.ResultHypotheses.Provenance" {original with Emission = {original.Emission with Boundary = {original.Emission.Boundary with ResultHypotheses = malformed}}}

let private pendingReservations =
    let original = revision [node 1 (SemanticKind.EnvironmentAllocate(NodeId 1)) []
                             node 2 (SemanticKind.Binding("first", false, false, None)) []
                             node 3 (SemanticKind.Binding("second", false, false, None)) []]
    let reservation claim binding : EnvironmentReservationAccount =
        { Claim = NodeId claim; Allocation = NodeId 1; Binding = NodeId binding; Initializer = NodeId 1
          Participants =
            [ participant ParticipantRole.EnvironmentAllocation 0 1 1
              participant ParticipantRole.EnvironmentBinding 0 1 binding
              participant ParticipantRole.EnvironmentInitializer 0 1 1
              // Repeated identity, different ordered role occurrences; no body.
              participant ParticipantRole.EnvironmentAuthorityInput 0 1 900
              participant ParticipantRole.EnvironmentAuthorityInput 1 1 900
              participant ParticipantRole.EnvironmentDeclarationInput 0 1 901 ] }
    let accounts = [reservation 40 2; reservation 41 3]
    let claims =
        accounts
        |> List.map (fun row ->
            let claim =
                obligation (sprintf "proposal-%d" (NodeId.value row.Claim)) "environment-storage-reservation"
                    (ObligationBody.EnvironmentStorageReservation(None, None, None, None, None))
            row.Claim, claim)
        |> Map.ofList
    let storage = { original.Emission.Storage with EnvironmentReservations = accounts |> List.map (fun row -> row.Claim, row) |> Map.ofList }
    let assembled = withStorage storage original
    { assembled with
        CurrentClaims = claims; Obligations = claims |> Map.values |> Seq.toList
        ObligationSources = accounts |> List.map (fun row -> row.Claim, [row.Participants |> List.map (fun (p: Participant) -> p.Node)]) |> Map.ofList }

[<Fact>]
let ``two unresolved proposals retain separate claims without admitting a residence`` () =
    Assert.Empty(Integrity.check pendingReservations)
    Assert.Equal(2, pendingReservations.Emission.Storage.EnvironmentReservations.Count)
    Assert.Empty pendingReservations.Emission.Storage.EnvironmentResidences
    Assert.False(pendingReservations.Nodes.ContainsKey(NodeId 900))
    let bytes = Binary.encode BinaryTests.limits pendingReservations |> BinaryTests.take
    let copy = Binary.decode BinaryTests.limits bytes |> BinaryTests.take
    Assert.Equal(pendingReservations.Emission.Storage, copy.Emission.Storage)
    Assert.Equal<Map<NodeId, NodeId list list>>(pendingReservations.ObligationSources, copy.ObligationSources)
    Assert.Equal<byte>(bytes, Binary.encode BinaryTests.limits copy |> BinaryTests.take)

[<Theory>]
[<InlineData("key")>]
[<InlineData("claim-family")>]
[<InlineData("current-claim")>]
[<InlineData("source-vector")>]
[<InlineData("role-order")>]
[<InlineData("duplicate-role")>]
[<InlineData("ordinal")>]
[<InlineData("group")>]
let ``reservation accounts refuse stale keys claims and ordered role occurrences`` change =
    let original = pendingReservations
    let storage = original.Emission.Storage
    let row = storage.EnvironmentReservations[NodeId 40]
    let update participants =
        withStorage { storage with EnvironmentReservations = storage.EnvironmentReservations.Add(row.Claim, { row with Participants = participants }) } original
    let part, altered =
        match change with
        | "key" -> "Claim", withStorage { storage with EnvironmentReservations = storage.EnvironmentReservations.Remove(row.Claim).Add(NodeId 42, row) } original
        | "claim-family" -> "Claim", { original with CurrentClaims = original.CurrentClaims.Add(row.Claim, { original.CurrentClaims[row.Claim] with Kind = "other" }) }
        | "current-claim" -> "Claim", { original with CurrentClaims = original.CurrentClaims.Remove row.Claim }
        | "source-vector" -> "Participants", { original with ObligationSources = original.ObligationSources.Add(row.Claim, [row.Participants |> List.map (fun (p: Participant) -> p.Node) |> List.rev]) }
        | "role-order" -> "Participants", update (row.Participants |> List.rev)
        | "duplicate-role" -> "Allocation", update (row.Participants.Head :: row.Participants)
        | "ordinal" -> "Participants", update (row.Participants |> List.map (fun p -> if p.Role = ParticipantRole.EnvironmentAuthorityInput then {p with Ordinal = 0} else p))
        | "group" -> "Binding", update (row.Participants |> List.map (fun p -> if p.Role = ParticipantRole.EnvironmentBinding then {p with Group = NodeId 3} else p))
        | other -> failwithf "Unknown mutation %s" other
    hasViolation ("Emission.Storage.EnvironmentReservations." + part) altered

let private factoryResults =
    let parameters = ["value", boolType, NodeId 6; "destination", boolType, NodeId 7]
    let original = revision [node 1 (SemanticKind.EnvironmentAllocate(NodeId 1)) []
                             node 3 (SemanticKind.Literal(NativeLiteral.Bool true)) []
                             node 4 (SemanticKind.Application(NodeId 5, [NodeId 6; NodeId 3])) [5; 6; 3]
                             node 5 (SemanticKind.Lambda(parameters, NodeId 8, [], None, LambdaContext.RegularClosure)) [6; 7; 8]
                             node 6 (SemanticKind.PatternBinding "value") []
                             node 7 (SemanticKind.PatternBinding "destination") []
                             node 8 (SemanticKind.Literal(NativeLiteral.Bool true)) []
                             node 9 (SemanticKind.EnvironmentCreate(NodeId 1, [])) []]
    let name = CallableSymbolName.Anonymous(NodeId 5)
    let declaration : CallableEmissionDeclaration =
        { Lookup = NodeId 5; Implementation = NodeId 5; Parameters = parameters; Result = NodeId 8
          Context = LambdaContext.RegularClosure; Captures = []; Name = name; Parent = None; Participants = Set.empty }
    let call : CallableEmissionCall =
        { Site = NodeId 4; Implementation = NodeId 5; Parameters = parameters; Arguments = [NodeId 6; NodeId 3]
          Result = NodeId 8; SignatureData = Set.ofList [NodeId 6; NodeId 7; NodeId 8]; Participants = Set.empty }
    let account : EnvironmentFactoryResultAccount =
        { Call = NodeId 4; Ordinal = 0; Factory = NodeId 5; Constructor = NodeId 9
          Formal = NodeId 7; Allocation = NodeId 1; Destination = NodeId 3 }
    { original with
        Codata = { original.Codata with EnvironmentDestinations = Map.ofList [NodeId 9, NodeId 7] }
        Emission =
            { original.Emission with
                Callable =
                    { original.Emission.Callable with
                        Calls = Map.ofList [NodeId 4, call]
                        Symbols = Map.ofList [NodeId 5, name]
                        Declarations = Map.ofList [NodeId 5, declaration] }
                Storage = { original.Emission.Storage with EnvironmentFactoryResults = Map.ofList [account.Call, account] } } }

[<Fact>]
let ``factory result ordinal is independent of destination formal position`` () =
    Assert.Empty(Integrity.check factoryResults)
    let row = factoryResults.Emission.Storage.EnvironmentFactoryResults[NodeId 4]
    Assert.Equal(0, row.Ordinal)
    let _, _, destinationFormal = factoryResults.Emission.Callable.Calls[row.Call].Parameters[1]
    Assert.Equal(row.Formal, destinationFormal)
    let bytes = Binary.encode BinaryTests.limits factoryResults |> BinaryTests.take
    Assert.Equal(factoryResults.Emission.Storage, (Binary.decode BinaryTests.limits bytes |> BinaryTests.take).Emission.Storage)

[<Theory>]
[<InlineData("call")>]
[<InlineData("factory")>]
[<InlineData("formal")>]
[<InlineData("allocation")>]
[<InlineData("destination")>]
[<InlineData("constructor")>]
let ``factory account identities cannot be replaced by other current nodes`` change =
    let original = factoryResults
    let storage = original.Emission.Storage
    let row = storage.EnvironmentFactoryResults[NodeId 4]
    let field, altered =
        match change with
        | "call" -> "Call", { row with Call = NodeId 3 }
        | "factory" -> "Factory", { row with Factory = NodeId 6 }
        | "formal" -> "Formal", { row with Formal = NodeId 6 }
        | "allocation" -> "Allocation", { row with Allocation = NodeId 3 }
        | "destination" -> "Formal", { row with Destination = NodeId 6 }
        | "constructor" -> "Formal", { row with Constructor = NodeId 8 }
        | other -> failwithf "Unknown mutation %s" other
    withStorage {storage with EnvironmentFactoryResults = Map.ofList [NodeId 4, altered]} original
    |> hasViolation ("Emission.Storage.EnvironmentFactoryResults." + field)

let private initializationOrders =
    let original = revision [node 1 (SemanticKind.Literal(NativeLiteral.Bool true)) []
                             node 2 (SemanticKind.Binding("second", false, false, None)) []
                             node 3 (SemanticKind.Binding("first", false, false, None)) []]
    let moduleId = NodeId 100
    let port : SourcePortAccount = { Extent = 0; Stamp = "module-declarations"; Positions = Map.empty }
    let startup : StartupWitness =
        { EntryBinding = NodeId 1; EntryLambda = NodeId 1; SourceBinding = NodeId 1; SourceLambda = NodeId 1
          OriginalBody = NodeId 1; Spine = NodeId 1; EntryCall = NodeId 1; Symbol = "main"
          Initializers = [{Module = moduleId; Binding = NodeId 3; Initializer = NodeId 1; Ordinal = 0}
                          {Module = moduleId; Binding = NodeId 2; Initializer = NodeId 1; Ordinal = 1}]
          ValueBindings = Set.ofList [NodeId 2; NodeId 3] }
    let participants =
        [ participant ParticipantRole.InitializationBinding 0 2 2
          participant ParticipantRole.InitializationEntry 1 2 1
          participant ParticipantRole.InitializationSpine 1 2 1
          participant ParticipantRole.InitializationValue 1 2 1
          participant ParticipantRole.InitializationPhase 0 2 3
          participant ParticipantRole.InitializationPhase 1 2 2
          participant ParticipantRole.InitializationPhase 2 2 1
          participant ParticipantRole.InitializationParent 0 2 900 ]
    let account : ProgramInitializationOrderAccount = {Binding = NodeId 2; Claim = NodeId 40; Participants = participants}
    let claim = obligation "second-order" "program-initialization-order" (ObligationBody.ProgramInitializationOrder(1, 2, [0; 1; 2]))
    { original with
        SourceReadings =
            { original.SourceReadings with
                Ports = original.SourceReadings.Ports.Add((moduleId, OccurrencePort.ModuleDeclaration), port)
                ContextHeaders = Map.ofList [moduleId, {Identity = moduleId; Name = "module"; Ports = Map.ofList [OccurrencePort.ModuleDeclaration, port]}] }
        CurrentClaims = Map.ofList [account.Claim, claim]; Obligations = [claim]
        ObligationSources = Map.ofList [account.Claim, [participants |> List.map (fun (p: Participant) -> p.Node)]]
        Emission =
            { original.Emission with
                Storage =
                    { original.Emission.Storage with
                        Startup = Some startup
                        ProgramInitializationOrders = Map.ofList [account.Binding, account] } } }

[<Fact>]
let ``initialization binding zero and initializer ordinal one retain their distinct roles`` () =
    Assert.Empty(Integrity.check initializationOrders)
    Assert.False(initializationOrders.Nodes.ContainsKey(NodeId 900))
    let bytes = Binary.encode BinaryTests.limits initializationOrders |> BinaryTests.take
    let copy = Binary.decode BinaryTests.limits bytes |> BinaryTests.take
    Assert.Equal(initializationOrders.Emission.Storage, copy.Emission.Storage)

[<Theory>]
[<InlineData("key")>]
[<InlineData("ordinal")>]
[<InlineData("phase")>]
[<InlineData("vector")>]
let ``initialization accounts refuse changed binding ordinal phase and complete sources`` change =
    let original = initializationOrders
    let storage = original.Emission.Storage
    let account = storage.ProgramInitializationOrders[NodeId 2]
    let replace participants = withStorage {storage with ProgramInitializationOrders = Map.ofList [account.Binding, {account with Participants = participants}]} original
    let field, altered =
        match change with
        | "key" -> "Binding", withStorage {storage with ProgramInitializationOrders = Map.ofList [NodeId 3, account]} original
        | "ordinal" -> "Initializer", replace (account.Participants |> List.map (fun p -> if p.Role = ParticipantRole.InitializationValue then {p with Ordinal = 0} else p))
        | "phase" -> "Participants", replace (account.Participants |> List.map (fun p -> if p.Role = ParticipantRole.InitializationPhase && p.Ordinal = 1 then {p with Node = NodeId 3} else p))
        | "vector" -> "Participants", {original with ObligationSources = original.ObligationSources.Add(account.Claim, [[]])}
        | other -> failwithf "Unknown mutation %s" other
    hasViolation ("Emission.Storage.ProgramInitializationOrders." + field) altered

[<Fact>]
let ``all artifact tables preserve exact ordered fields through the generated storage codec`` () =
    // A field-level codec fixture does not claim these independently stated
    // rows together form a structurally valid, source-admitted revision.
    let reservations = pendingReservations.Emission.Storage.EnvironmentReservations
    let residence : EnvironmentResidenceAccount =
        { Allocation = NodeId 1; Binding = NodeId 2; Owner = NodeId 10; Implementation = NodeId 11
          Formal = NodeId 12; ReservationClaim = NodeId 40; AuthorityInputs = [NodeId 900; NodeId 900]
          BindingPath = [NodeId 1; NodeId 8; NodeId 2]; LayoutClaims = [NodeId 42; NodeId 43]
          DeclarationInputs = [NodeId 901; NodeId 902] }
    let original =
        { Empty.storage with
            EnvironmentReservations = reservations
            EnvironmentFactoryResults = factoryResults.Emission.Storage.EnvironmentFactoryResults
            EnvironmentResidences = Map.ofList [residence.Allocation, residence]
            ProgramInitializationOrders = initializationOrders.Emission.Storage.ProgramInitializationOrders }
    let plan = BinaryGenerated.write_Fidelity_PSG_StorageWitnessProjection (BinaryIndexed.initialWrite BinaryTests.limits) original |> BinaryTests.take
    let fragment = BinaryIndexed.fragment plan |> BinaryTests.take
    let bytes = Array.zeroCreate (BinaryIndexed.size fragment)
    BinaryIndexed.writeFragment bytes 0 fragment
    let source = BAREWire.Memory.ByteSource.ofArray bytes
    let initial = BinaryIndexed.initialRead BinaryTests.limits source {Offset = 0UL; Length = uint64 bytes.Length}
    let copy, state = BinaryGenerated.read_Fidelity_PSG_StorageWitnessProjection initial |> BinaryTests.take
    Assert.Equal(original, copy)
    Assert.Equal(0, state.Depth)
    Assert.Equal(1, state.Current.Next)

[<Theory>]
[<InlineData("key")>]
[<InlineData("reservation")>]
let ``residence cannot be filed under a different allocation or invent reservation authority`` change =
    let original = pendingReservations
    let storage = original.Emission.Storage
    let residence : EnvironmentResidenceAccount =
        { Allocation = NodeId 1; Binding = NodeId 2; Owner = NodeId 1; Implementation = NodeId 1
          Formal = NodeId 1; ReservationClaim = NodeId 40; AuthorityInputs = []
          BindingPath = [NodeId 1]; LayoutClaims = []; DeclarationInputs = [] }
    let field, key, row =
        match change with
        | "key" -> "Allocation", NodeId 3, residence
        | "reservation" -> "ReservationClaim", residence.Allocation, {residence with ReservationClaim = NodeId 42}
        | other -> failwithf "Unknown mutation %s" other
    withStorage {storage with EnvironmentResidences = Map.ofList [key, row]} original
    |> hasViolation ("Emission.Storage.EnvironmentResidences." + field)

let private admittedResidence =
    // Contract-only account: each source-authorized row is stated explicitly.
    // The source/consumer suites own actual program compilation and execution.
    let nodes =
        factoryResults.Nodes
        |> Map.add (NodeId 2) (node 2 (SemanticKind.Binding("resident", false, false, None)) [])
        |> Map.add (NodeId 10) (node 10 (SemanticKind.Binding("alias", false, false, None)) [])
    let original = covered {factoryResults with Nodes = nodes}
    let moduleId, spaceId = NodeId 100, NodeId 902
    let space : BAREWire.Platform.MemorySpace =
        {Name = "program"; Kind = "ram"; Capacity = 4096L; Alignment = 8; Granularity = 8; Growth = "fixed"; Access = "rw"
         Base = None; Notes = ""; MapKind = ""; Since = ""; Until = ""}
    let identity = ProgramStorageIdentity.Allocation(NodeId 1)
    let entry : ProgramStorageEntry =
        {Identity = identity; SourceType = unitType; Shape = ProgramStorageShape.Bytes
         Bytes = 8; Alignment = 8; SpaceNode = spaceId; Space = space; Participants = Set.ofList [spaceId; NodeId 900]}
    let storageInventory : ProgramStorageInventory =
        {Entries = Map.ofList [identity, entry]
         Reservations = Map.ofList [spaceId, {Space = space; Requests = [|{Name = "allocation:1"; Length = 8L; Alignment = 8}|]; PayloadSize = 8L}]
         Unresolved = Map.empty}
    let reservationParticipants =
        [ participant ParticipantRole.EnvironmentAllocation 0 1 1
          participant ParticipantRole.EnvironmentBinding 0 1 2
          participant ParticipantRole.EnvironmentInitializer 0 1 4
          participant ParticipantRole.EnvironmentOwner 0 1 1
          participant ParticipantRole.EnvironmentImplementation 0 1 5
          participant ParticipantRole.EnvironmentConstructor 0 1 9
          participant ParticipantRole.EnvironmentFormal 0 1 6
          participant ParticipantRole.EnvironmentSpace 0 1 902
          participant ParticipantRole.EnvironmentAuthorityInput 0 1 900
          participant ParticipantRole.EnvironmentAuthorityInput 1 1 900
          participant ParticipantRole.EnvironmentDeclarationInput 0 1 901
          participant ParticipantRole.EnvironmentDeclarationInput 1 1 901
          participant ParticipantRole.EnvironmentCall 0 4 4
          participant ParticipantRole.EnvironmentFactory 0 4 5
          participant ParticipantRole.EnvironmentConstructor 0 4 9
          participant ParticipantRole.EnvironmentFormal 0 4 7
          participant ParticipantRole.EnvironmentAllocation 0 4 1
          participant ParticipantRole.EnvironmentDestination 0 4 3 ]
    let reservation : EnvironmentReservationAccount =
        {Claim = NodeId 40; Allocation = NodeId 1; Binding = NodeId 2; Initializer = NodeId 4; Participants = reservationParticipants}
    let residence : EnvironmentResidenceAccount =
        {Allocation = NodeId 1; Binding = NodeId 2; Owner = NodeId 1; Implementation = NodeId 5; Formal = NodeId 6
         ReservationClaim = reservation.Claim; AuthorityInputs = [NodeId 900; NodeId 900]; BindingPath = [NodeId 1; NodeId 4; NodeId 2]
         LayoutClaims = []; DeclarationInputs = [NodeId 901; NodeId 901]}
    let parameters = original.Emission.Callable.Calls[NodeId 4].Parameters
    // closure-representation §2.4: "The ordinary calling contract preserves
    // the arguments, result and environment convention"; each alternative
    // conforms to "the slot's one receiving contract or a source-settled adapter."
    // A settled residence therefore publishes a real receiving contract, not
    // the pending convention used by an unused carrier-only fixture.
    let contract : CallableContract =
        {Identity = NodeId 43; Kind = CallableKind.OrdinaryFlatClosure; Convention = CallableConvention.Ordinary
         ParameterTypes = [boolType; boolType]; OmittedParameters = []
         ParameterRepresentations = [0, ValueRepresentation.Scalar SettledSlot.Bool; 1, ValueRepresentation.Scalar SettledSlot.Bool]
         ResultType = original.Emission.Numeric.SourceTypes[NodeId 8]
         ResultRepresentation = ValueRepresentation.Scalar SettledSlot.Bool
         EnvironmentBytes = Some 8; SourcePremises = Map.empty
         Participants = [participant ParticipantRole.CallableContract 0 43 43
                         participant ParticipantRole.CallableImplementation 0 43 5
                         participant ParticipantRole.CalleeParameter 0 43 6
                         participant ParticipantRole.CalleeParameter 1 43 7
                         participant ParticipantRole.CalleeBody 0 43 8]}
    let carrier binding : CallableCarrier =
        {Occurrence = NodeId binding; Kind = CallableKind.OrdinaryFlatClosure; Formation = NodeId binding; EnvironmentValue = Some(NodeId binding)
         Contract = Ok contract.Identity; Lifetime = [participant ParticipantRole.CallableLifetime 0 binding 40]
         SourceType = unitType; Implementation = NodeId 5; Parameters = parameters
         ParameterShapes = [CallableValueShape.Data(NodeId 6); CallableValueShape.Data(NodeId 7)]; OmittedParameters = Set.empty
         Result = NodeId 8; ResultShape = CallableValueShape.Data(NodeId 8); Environment = Some {Owner = NodeId 1; Formal = NodeId 6}}
    let instance binding : CallableProgramInstance =
        {Carrier = carrier binding; Allocation = Some(NodeId 1); Participants = Set.ofList [NodeId binding; NodeId 2; NodeId 1]}
    let port : SourcePortAccount = {Extent = 0; Stamp = "module-declarations"; Positions = Map.empty}
    let startup : StartupWitness =
        {EntryBinding = NodeId 1; EntryLambda = NodeId 1; SourceBinding = NodeId 1; SourceLambda = NodeId 1
         OriginalBody = NodeId 1; Spine = NodeId 1; EntryCall = NodeId 1; Symbol = "main"
         Initializers = [{Module = moduleId; Binding = NodeId 2; Initializer = NodeId 4; Ordinal = 0}
                         {Module = moduleId; Binding = NodeId 10; Initializer = NodeId 2; Ordinal = 1}]
         ValueBindings = Set.ofList [NodeId 2; NodeId 10]}
    let order binding initializer ordinal claim : ProgramInitializationOrderAccount =
        {Binding = NodeId binding; Claim = NodeId claim
         Participants = [participant ParticipantRole.InitializationBinding 0 binding binding
                         participant ParticipantRole.InitializationEntry ordinal binding 1
                         participant ParticipantRole.InitializationSpine ordinal binding 1
                         participant ParticipantRole.InitializationValue ordinal binding initializer
                         participant ParticipantRole.InitializationPhase 0 binding 2
                         participant ParticipantRole.InitializationPhase 1 binding 10
                         participant ParticipantRole.InitializationPhase 2 binding 1
                         participant ParticipantRole.InitializationParent 0 binding 900]}
    let orders = [order 2 4 0 41; order 10 2 1 42]
    let reservationClaim =
        obligation "resident-space" "environment-storage-reservation"
            (ObligationBody.EnvironmentStorageReservation(Some 8, Some 8, Some 4096L, Some 8, Some 8))
    let claims =
        Map.ofList
            [ NodeId 40, reservationClaim
              NodeId 41, obligation "resident-order" "program-initialization-order" (ObligationBody.ProgramInitializationOrder(0, 2, [0; 1; 2]))
              NodeId 42, obligation "alias-order" "program-initialization-order" (ObligationBody.ProgramInitializationOrder(1, 2, [0; 1; 2])) ]
    let sources = (reservation.Claim, reservation.Participants) :: (orders |> List.map (fun row -> row.Claim, row.Participants))
    let layout : EnvironmentLayout =
        {Owner = NodeId 1; Implementation = NodeId 5; Formal = NodeId 6
         Slots = []; Bytes = 8; Alignment = 8; Obligations = []}
    let callable =
        {original.Emission.Callable with
            Contracts = Map.ofList [contract.Identity, contract]
            Carriers = Map.ofList [NodeId 2, carrier 2; NodeId 10, carrier 10]
            SignatureData = Map.ofList [NodeId 2, Set.ofList [NodeId 6; NodeId 7; NodeId 8]
                                        NodeId 10, Set.ofList [NodeId 6; NodeId 7; NodeId 8]]
            ProgramInstances = Map.ofList [NodeId 2, instance 2; NodeId 10, instance 10]}
    {original with
        Codata =
            {original.Codata with
                ProgramStorage = storageInventory
                CallableCarriers = callable.Carriers; CallableContracts = callable.Contracts
                EnvironmentLayouts = Map.ofList [NodeId 1, layout]}
        SourceReadings =
            {original.SourceReadings with
                Ports = original.SourceReadings.Ports.Add((moduleId, OccurrencePort.ModuleDeclaration), port)
                ContextHeaders = Map.ofList [moduleId, {Identity = moduleId; Name = "module"; Ports = Map.ofList [OccurrencePort.ModuleDeclaration, port]}]}
        CurrentClaims = claims; Obligations = claims |> Map.values |> Seq.toList
        ObligationSources = sources |> List.map (fun (claim, participants) -> claim, [participants |> List.map (fun (p: Participant) -> p.Node)]) |> Map.ofList
        Emission =
            {original.Emission with
                Callable = callable
                Storage =
                    {original.Emission.Storage with
                        ProgramStorage = storageInventory; Startup = Some startup
                        EnvironmentReservations = Map.ofList [reservation.Claim, reservation]
                        EnvironmentResidences = Map.ofList [residence.Allocation, residence]
                        ProgramInitializationOrders = orders |> List.map (fun row -> row.Binding, row) |> Map.ofList}}}

[<Fact>]
let ``canonical residence and its immutable alias retain one allocation without demanding premise bodies`` () =
    Assert.Empty(Integrity.check admittedResidence)
    let storage = admittedResidence.Emission.Storage
    Assert.Equal(1, storage.EnvironmentResidences.Count)
    Assert.Equal(2, admittedResidence.Emission.Callable.ProgramInstances.Count)
    Assert.Equal(NodeId 2, storage.EnvironmentResidences[NodeId 1].Binding)
    Assert.False(admittedResidence.Nodes.ContainsKey(NodeId 900))
    Assert.False(admittedResidence.Nodes.ContainsKey(NodeId 901))
    let bytes = Binary.encode BinaryTests.limits admittedResidence |> BinaryTests.take
    let copy = Binary.decode BinaryTests.limits bytes |> BinaryTests.take
    Assert.Equal(admittedResidence.Emission, copy.Emission)
    Assert.Equal(admittedResidence.Codata, copy.Codata)

[<Theory>]
[<InlineData("implementation")>]
[<InlineData("owner")>]
[<InlineData("formal")>]
[<InlineData("canonical-binding")>]
[<InlineData("allocation")>]
let ``sharing an allocation does not waive an alias exact carrier convention and canonical provenance`` change =
    let original = admittedResidence
    let callable = original.Emission.Callable
    let instance = callable.ProgramInstances[NodeId 10]
    let altered =
        match change with
        | "implementation" -> {instance with Carrier = {instance.Carrier with Implementation = NodeId 6}}
        | "owner" -> {instance with Carrier = {instance.Carrier with Environment = Some {Owner = NodeId 3; Formal = NodeId 6}}}
        | "formal" -> {instance with Carrier = {instance.Carrier with Environment = Some {Owner = NodeId 1; Formal = NodeId 7}}}
        | "canonical-binding" -> {instance with Participants = instance.Participants.Remove(NodeId 2)}
        | "allocation" -> {instance with Participants = instance.Participants.Remove(NodeId 1)}
        | other -> failwithf "Unknown mutation %s" other
    {original with Emission = {original.Emission with Callable = {callable with ProgramInstances = callable.ProgramInstances.Add(NodeId 10, altered)}}}
    |> hasViolation "Emission.Storage.EnvironmentResidences.Allocation"

[<Theory>]
[<InlineData("reservation")>]
[<InlineData("layout")>]
[<InlineData("authority")>]
[<InlineData("declaration")>]
[<InlineData("path")>]
[<InlineData("storage")>]
[<InlineData("initializer")>]
let ``admitted residence refuses changed complete source and storage correspondence`` change =
    let original = admittedResidence
    let storage = original.Emission.Storage
    let row = storage.EnvironmentResidences[NodeId 1]
    let update (residence: EnvironmentResidenceAccount) =
        withStorage {storage with EnvironmentResidences = Map.ofList [residence.Allocation, residence]} original
    let field, altered =
        match change with
        | "reservation" -> "ReservationClaim", update {row with ReservationClaim = NodeId 41}
        | "layout" -> "Owner", {original with Codata = {original.Codata with EnvironmentLayouts = original.Codata.EnvironmentLayouts.Add(row.Owner, {original.Codata.EnvironmentLayouts[row.Owner] with Alignment = 4})}}
        | "authority" -> "AuthorityInputs", update {row with AuthorityInputs = [NodeId 900]}
        | "declaration" -> "DeclarationInputs", update {row with DeclarationInputs = [NodeId 901]}
        | "path" -> "BindingPath", update {row with BindingPath = [NodeId 1; NodeId 2]}
        | "storage" -> "ReservationClaim", withStorage {storage with ProgramStorage = {storage.ProgramStorage with Entries = Map.empty}} original
        | "initializer" -> "Initializer", withStorage {storage with Startup = storage.Startup |> Option.map (fun startup -> {startup with Initializers = startup.Initializers |> List.map (fun initializer -> if initializer.Binding = NodeId 2 then {initializer with Initializer = NodeId 3} else initializer)})} original
        | other -> failwithf "Unknown mutation %s" other
    hasViolation ("Emission.Storage.EnvironmentResidences." + field) altered
