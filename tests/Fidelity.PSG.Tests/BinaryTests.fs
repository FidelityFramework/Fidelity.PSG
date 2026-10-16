module Fidelity.PSG.Tests.BinaryTests

open System
open System.IO
open Xunit
open Fidelity.PSG

let limits : Binary.Limits =
    { MaxBytes = 4 * 1024 * 1024; MaxCollectionLength = 10000; MaxDepth = 128
      MaxStringBytes = 1024 * 1024; MaxBigIntegerBytes = 4096; MaxValues = 1000000 }

let take = function
    | Result.Ok value -> value
    | Result.Error error -> failwithf "Unexpected binary refusal: %A" error

let private writeState bounds : BinaryRuntime.WriteState =
    { Data = None; Offset = 0; Depth = 0; Remaining = bounds.MaxValues; Limits = bounds }

let private readState bounds bytes : BinaryRuntime.ReadState =
    { Data = bytes; Offset = 0; Depth = 0; Remaining = bounds.MaxValues; Limits = bounds }

let private encoded (writer: BinaryRuntime.WriteState -> 'a -> Result<BinaryRuntime.WriteState, BinaryError>) value =
    let initial = writeState limits
    let measured = writer initial value |> take
    let bytes = Array.zeroCreate measured.Offset
    let written = writer { initial with Data = Some bytes } value |> take
    Assert.Equal(bytes.Length, written.Offset)
    bytes

let private decoded (reader: BinaryRuntime.ReadState -> Result<'a * BinaryRuntime.ReadState, BinaryError>) bytes =
    let value, state = reader (readState limits bytes) |> take
    Assert.Equal(bytes.Length, state.Offset)
    Assert.Equal(0, state.Depth)
    value

let private indexedEncoded (writer: BinaryIndexed.WriteState -> 'a -> Result<BinaryIndexed.WriteState, BinaryError>) value =
    let plan = writer (BinaryIndexed.initialWrite limits) value |> take
    let fragment = BinaryIndexed.fragment plan |> take
    let bytes = Array.zeroCreate (BinaryIndexed.size fragment)
    BinaryIndexed.writeFragment bytes 0 fragment
    bytes

let private indexedReadState bounds bytes =
    BinaryIndexed.initialRead bounds (BAREWire.Memory.ByteSource.ofArray bytes) { Offset = 0UL; Length = uint64 bytes.Length }

[<Fact>]
let ``closed callback binary retains receiving hypothesis and complete original entry incidence`` () =
    let signature : NativeEntrySignature =
        {Parameters = [BoundaryScalar.Integer(64,true)]; Result = Some(BoundaryScalar.Integer(64,true)); CallingConvention = "CDecl"}
    let invocation : BoundaryCallbackInvocation =
        {Identity = NodeId 40; Import = NodeId 41; Parameter = 3; Formal = NodeId 42; Scope = NodeId 43; Signature = signature
         Extent = BoundaryCallbackExtent.DuringCall
         Contract = {Binding = "Foreign.call"; Parameter = 3
                     Signature = {Parameters = [|{Name = "unused"; Type = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed,64); PassBy = BAREWire.Descriptors.PassBy.Value}|]
                                  ReturnType = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed,64); CallingConvention = BAREWire.Descriptors.CallConv.CDecl}
                     Hypothesis = {Identity = "foreign-demand"; Version = "7"; Source = "explicit-fixture"}; Scope = "Foreign.scope"}
         Participants = Set.ofList [NodeId 40; NodeId 41; NodeId 42; NodeId 43]}
    let entry : BoundaryClosedEntry =
        {Formation = NodeId 50; Operand = NodeId 51; Declaration = NodeId 52; Implementation = NodeId 53
         Formals = [NodeId 54]; Body = NodeId 55; Lifetime = {Module = NodeId 56; Binding = NodeId 52; Implementation = NodeId 53}
         Invocation = invocation.Identity; ParameterAdaptations = [None]; ResultAdaptation = Some {Consumer = NodeId 55; Operand = NodeId 55; From = 8; To = 64; Adapt = MeetKind.ExtendUnsigned}
         Registrations = Map.empty
         Transport = Set.ofList [NodeId 50; NodeId 51]; Participants = Set.ofList [NodeId 50; NodeId 51; NodeId 52; NodeId 53; NodeId 54; NodeId 55; NodeId 56; NodeId 40]}
    let bytes = indexedEncoded BinaryGenerated.write_Fidelity_PSG_BoundaryCallbackInvocation invocation
    let actual, state = BinaryGenerated.read_Fidelity_PSG_BoundaryCallbackInvocation (indexedReadState limits bytes) |> take
    Assert.Equal(invocation, actual)
    Assert.Equal(0,state.Depth)
    let bytes = indexedEncoded BinaryGenerated.write_Fidelity_PSG_BoundaryClosedEntry entry
    let actual, state = BinaryGenerated.read_Fidelity_PSG_BoundaryClosedEntry (indexedReadState limits bytes) |> take
    Assert.Equal(entry, actual)
    Assert.Equal(0,state.Depth)
    let carrier = BoundaryScalar.Entry invocation.Identity
    let bytes = indexedEncoded BinaryGenerated.write_Fidelity_PSG_BoundaryScalar carrier
    Assert.Equal(carrier, BinaryGenerated.read_Fidelity_PSG_BoundaryScalar (indexedReadState limits bytes) |> take |> fst)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``optional entry binary retains exact absent and present source selection`` present =
    let selected : BoundaryOptionalEntry =
        {Construction = NodeId 60; CaseOrdinal = if present then 1 else 0
         Payload = if present then Some(NodeId 61) else None
         Formation = if present then Some(NodeId 62) else None
         Transport = Set.ofList [NodeId 60; NodeId 63]
         Obligation = NodeId 64}
    let operand : BoundaryOperand =
        {Actual = NodeId 63; Formal = NodeId 42; Abi = BoundaryScalar.Entry(NodeId 40)
         Adaptation = None; OptionalEntry = Some selected}
    let bytes = indexedEncoded BinaryGenerated.write_Fidelity_PSG_BoundaryOperand operand
    let actual, state = BinaryGenerated.read_Fidelity_PSG_BoundaryOperand (indexedReadState limits bytes) |> take
    Assert.Equal(operand, actual)
    Assert.Equal(0, state.Depth)

[<Fact>]
let ``Pending binary retains reason order duplicates and Unicode without a solver body`` () =
    let expected = ObligationBody.Pending ["Selected target conversion remains Pending."; "λ nullable premise"; "λ nullable premise"]
    let bytes = indexedEncoded BinaryGenerated.write_Fidelity_PSG_ObligationBody expected
    let actual, state = BinaryGenerated.read_Fidelity_PSG_ObligationBody (indexedReadState limits bytes) |> take
    Assert.Equal(expected, actual)
    Assert.Equal(0, state.Depth)

[<Fact>]
let ``absence conversion binary retains exact promise content and source plan`` () =
  let roles = [CallbackAbsenceInputRole.Binding; CallbackAbsenceInputRole.Parameter; CallbackAbsenceInputRole.Hypothesis
               CallbackAbsenceInputRole.HypothesisIdentity; CallbackAbsenceInputRole.HypothesisVersion; CallbackAbsenceInputRole.HypothesisSource]
  let account : BoundaryCallbackAbsence =
    { Quote = NodeId 70; DescriptorBinding = NodeId 71; Record = NodeId 72; Import = NodeId 73
      Parameter = 2; Formal = NodeId 74; Invocation = NodeId 75
      Contract = {Binding = "Foreign.receive"; Parameter = 2
                  Hypothesis = {Identity = "foreign.absence"; Version = "v2"; Source = "fixture-λ.pilot.toml"}}
      SourcePath = [NodeId 71; NodeId 70; NodeId 72]
      Inputs = roles |> List.mapi (fun index role -> role, [NodeId(80 + index); NodeId(90 + index)])
      DeclarationFacts = Map.ofList [NodeId 72,
        {Form = "record"; Text = ["current"; "λ"]; Numbers = [-1I; 2I]; References = [NodeId 73]
         Children = [NodeId 80; NodeId 81]; Parent = Some(NodeId 70); SourceType = Build.unitType}] }
  let model : OptionalEntryAbsenceArgumentConversionModel =
    { Call = NodeId 100; Parameter = 2; Actual = NodeId 101; Construction = NodeId 102; SourceCase = 0; Absence = account.Quote
      Arms = [{CaseOrdinal = 0; Choice = OptionalEntryAbsencePlanChoice.AbsentEntry}
              {CaseOrdinal = 1; Choice = OptionalEntryAbsencePlanChoice.RequiresClosedEntry}] }
  let body = ObligationBody.OptionalEntryAbsenceArgumentConversion model
  let bodyBytes = indexedEncoded BinaryGenerated.write_Fidelity_PSG_ObligationBody body
  let decodedBody, bodyState = BinaryGenerated.read_Fidelity_PSG_ObligationBody (indexedReadState limits bodyBytes) |> take
  Assert.Equal(body, decodedBody)
  Assert.Equal(0, bodyState.Depth)
  let projection = {Empty.boundary with CallbackAbsences = Map.ofList [account.Quote, account]}
  let bytes = indexedEncoded BinaryGenerated.write_Fidelity_PSG_BoundaryEmissionProjection projection
  let actual, state = BinaryGenerated.read_Fidelity_PSG_BoundaryEmissionProjection (indexedReadState limits bytes) |> take
  Assert.Equal(projection, actual)
  Assert.Equal(0, state.Depth)
  let edge = EdgeRole.BoundaryCallbackAbsence account
  let bytes = indexedEncoded BinaryGenerated.write_Fidelity_PSG_EdgeRole edge
  let actual, state = BinaryGenerated.read_Fidelity_PSG_EdgeRole (indexedReadState limits bytes) |> take
  Assert.Equal(edge, actual)
  Assert.Equal(0, state.Depth)

[<Fact>]
let ``absence promise binary refuses a record missing its current content field`` () =
  let contract : BAREWire.Descriptors.CallbackAbsenceContract =
    {Binding = "Foreign.receive"; Parameter = 0; Hypothesis = {Identity = "absence"; Version = "1"; Source = "fixture"}}
  let bytes = indexedEncoded BinaryGenerated.write_BAREWire_Descriptors_CallbackAbsenceContract contract
  // The record frame must retain all three declared fields, including provenance.
  BAREWire.Encoding.Encoder.writeU64 bytes 0 2UL |> ignore
  match BinaryGenerated.read_BAREWire_Descriptors_CallbackAbsenceContract (indexedReadState limits bytes) with
  | Result.Error(BinaryError.Malformed(offset, reason)) ->
    Assert.Equal(0, offset)
    Assert.Equal("Directory arity disagrees with its schema", reason)
  | other -> failwithf "Expected exact absence record field-count refusal, got %A" other

[<Fact>]
let ``Pending binary refuses a ledger claim detached from its optional operand owner`` () =
    let claim : ObligationInfo =
        {Id = "optional-conversion-1"; Kind = "foreign-optional-entry-conversion-0"; Logic = ""
         Statement = "The exact source Option selection requires an admitted target boundary conversion."
         Source = "contract-test.clef:1:1"; Refs = []
         Body = ObligationBody.Pending ["Selected-target optional-entry conversion remains Pending."]}
    let sourceGroups = [[NodeId 1; NodeId 2]; [NodeId 2]]
    let expected =
        {Build.bindingWithLiteral with
            Obligations = [claim]; CurrentClaims = Map.ofList [NodeId 90, claim]
            ObligationSources = Map.ofList [NodeId 90, sourceGroups]}
    match Binary.encode limits expected with
    | Result.Error(BinaryError.InvalidRevision violations) ->
        let violation = Assert.Single violations
        Assert.Equal("CurrentClaims.Pending.Owner", violation.Part)
        Assert.Equal(Some(NodeId 90), violation.Node)
        Assert.Equal("A Pending claim requires exactly one current optional-entry operand account.", violation.Reason)
    | other -> failwithf "Expected exact Pending ownership refusal, got %A" other

[<Fact>]
let ``ordinary omission origins retain their kind ordinal and identities in the binary contract`` () =
  let omissions : OrdinaryOmission list =
    [ {Site = NodeId 5; Origin = OrdinaryOmissionOrigin.CallArgument 0; Actual = NodeId 3}
      {Site = NodeId 5; Origin = OrdinaryOmissionOrigin.CallArgument 7; Actual = NodeId 3}
      {Site = NodeId 5; Origin = OrdinaryOmissionOrigin.BindingInitializer; Actual = NodeId 3} ]
  let images = omissions |> List.map (indexedEncoded BinaryGenerated.write_Fidelity_PSG_OrdinaryOmission)
  Assert.Equal(3, images |> List.distinct |> List.length)
  List.iter2 (fun expected bytes ->
    let actual, state = BinaryGenerated.read_Fidelity_PSG_OrdinaryOmission (indexedReadState limits bytes) |> take
    Assert.Equal(0, state.Depth)
    Assert.Equal(expected, actual)) omissions images

[<Fact>]
let ``initializer omission participant roles retain their distinct binary identities`` () =
  let roles = [ParticipantRole.OmissionSite; ParticipantRole.OmittedActual; ParticipantRole.OmissionBinding; ParticipantRole.OmittedInitializer]
  let images = roles |> List.map (indexedEncoded BinaryGenerated.write_Fidelity_PSG_ParticipantRole)
  Assert.Equal(4, images |> List.distinct |> List.length)
  List.iter2 (fun expected bytes ->
    Assert.Equal(expected, BinaryGenerated.read_Fidelity_PSG_ParticipantRole (indexedReadState limits bytes) |> take |> fst)) roles images

let child (bytes: byte array) (at: int) (index: int) =
    let offset, _ = BAREWire.Encoding.Decoder.readU64 bytes (at + 8 + index * 16)
    int offset

let private malformed = function
    | Result.Error (BinaryError.Malformed _) -> ()
    | value -> failwithf "Expected malformed input refusal, got %A" value

let private exceeded name = function
    | Result.Error (BinaryError.LimitExceeded(actual, _)) -> Assert.Equal(name, actual)
    | value -> failwithf "Expected %s refusal, got %A" name value

[<Fact>]
let ``binary generator output agrees with every reachable compiled contract field`` () =
    let produced = PsgBinaryGeneration.generate typeof<Revision>.Assembly.Location
    let repository = Path.GetFullPath(Path.Combine(__SOURCE_DIRECTORY__, "..", ".."))
    let held = File.ReadAllText(Path.Combine(repository, "src", "Fidelity.PSG", "BinaryGenerated.fs"))
    Assert.True((held = produced), "BinaryGenerated.fs drifted from the compiled contract. Regenerate the complete codec; do not hand-edit cases.")

[<Fact>]
let ``snapshot header has independent version schema and fingerprint bytes`` () =
    let bytes = Binary.encode limits (Revision.empty "g") |> take
    // Pin the approved schema/shape pair independently of the generated values.
    // A changed published shape must earn a deliberate schema migration; merely
    // regenerating the codecs cannot update this oracle.
    let prefix = Convert.FromHexString("465053474944583202000000260000002521EE15F0FCDB2902EF7A14976A8974E0180BC1874F48675FBE13A40307BE49")
    Assert.Equal<byte>(prefix, bytes[..47])
    Assert.Equal(Revision.Schema, System.Buffers.Binary.BinaryPrimitives.ReadInt32LittleEndian(bytes.AsSpan(12, 4)))
    Assert.Equal<byte>(Convert.FromHexString(BinaryGenerated.Fingerprint), bytes[16..47])
    Assert.Equal<byte>([|64uy;0uy;0uy;0uy;0uy;0uy;0uy;0uy|], bytes[48..55])
    let header = child bytes 64 0
    let schema = child bytes header 0
    let producer = child bytes header 1
    Assert.Equal(Revision.Schema, System.Buffers.Binary.BinaryPrimitives.ReadInt32LittleEndian(bytes.AsSpan(schema, 4)))
    Assert.Equal<byte>([|1uy;byte 'g'|], bytes[producer..producer + 1])
    let copy = Binary.decode limits bytes |> take
    Assert.Equal(Revision.Schema, copy.Header.Schema)
    Assert.Equal("g", copy.Header.Producer)

[<Fact>]
let ``complete populated snapshot preserves identity ranges relations and literal bits`` () =
    let nan = BitConverter.Int64BitsToDouble(0x7FF8000000000042L)
    let negativeZero = BitConverter.Int64BitsToDouble(Int64.MinValue)
    let literals =
        [ NativeLiteral.Int(Int64.MinValue, NTUKind.NTUint(NTUWidth.Fixed 64))
          NativeLiteral.UInt(UInt64.MaxValue, NTUKind.NTUuint(NTUWidth.Fixed 64))
          NativeLiteral.Float(nan, NTUKind.NTUfloat(NTUWidth.Fixed 64))
          NativeLiteral.Float(negativeZero, NTUKind.NTUfloat(NTUWidth.Fixed 64))
          NativeLiteral.Decimal(Decimal(1234500, 0, 0, true, 4uy))
          NativeLiteral.String "λ\u0000😀"
          NativeLiteral.ByteArray [|0uy;127uy;255uy|]
          NativeLiteral.UInt16Array [|0us;65535us|] ]
    let wide = bigint.One <<< 300
    let nodes = literals |> List.mapi (fun index literal ->
        { Build.node (index + 1) (SemanticKind.Literal literal) [] with
            ValueRange = Some(ValueRange.Bounded(-wide, wide + 7I)) })
    let basis = Build.revision nodes
    let original =
        { basis with
            Platform = { Register = Result.Ok 64; Pointer = Result.Ok 64 }
            DeclarationRoots = [NodeId 1, DeclRoot.EntryPoint]
            Edges = [{ Class = EdgeClass.Range; Role = EdgeRole.SequencePullComposition(23, wide)
                       Ordinal = 9; Sources = [NodeId 2; NodeId 1]; Target = NodeId 3 }]
            Codata = { basis.Codata with SequenceOrigins = Map.ofList [NodeId 2, NodeId 1] }
            Emission = { basis.Emission with Boundary = { basis.Emission.Boundary with Links = Set.ofList ["m"; "c"] } } }
    Assert.Empty(Integrity.check original)
    let bytes = Binary.encode limits original |> take
    let copy = Binary.decode limits bytes |> take
    Assert.Equal<byte>(bytes, Binary.encode limits copy |> take)
    Assert.Equal<NodeId list>(original.Nodes |> Map.keys |> Seq.toList, copy.Nodes |> Map.keys |> Seq.toList)
    Assert.Equal<Hyperedge list>(original.Edges, copy.Edges)
    Assert.Equal(original.Codata, copy.Codata)
    Assert.Equal(original.Emission, copy.Emission)
    Assert.Equal<(NodeId * DeclRoot) list>(original.DeclarationRoots, copy.DeclarationRoots)
    for KeyValue(id, node) in original.Nodes do
        Assert.Equal(node.ValueRange, copy.Nodes[id].ValueRange)
    match copy.Nodes[NodeId 3].Kind, copy.Nodes[NodeId 4].Kind, copy.Nodes[NodeId 5].Kind with
    | SemanticKind.Literal(NativeLiteral.Float(a, _)), SemanticKind.Literal(NativeLiteral.Float(b, _)), SemanticKind.Literal(NativeLiteral.Decimal(c)) ->
        Assert.Equal(0x7FF8000000000042L, BitConverter.DoubleToInt64Bits a)
        Assert.Equal(Int64.MinValue, BitConverter.DoubleToInt64Bits b)
        Assert.Equal<int>(Decimal.GetBits(Decimal(1234500, 0, 0, true, 4uy)), Decimal.GetBits c)
    | _ -> failwith "Literal cases changed during transport"

[<Fact>]
let ``declaration root tags retain LibraryExport distinctly from executable roots`` () =
    for root, tag in [DeclRoot.EntryPoint, 0uy; DeclRoot.HardwareModule, 1uy; DeclRoot.KernelModule, 2uy; DeclRoot.LibraryExport, 3uy] do
        let bytes = indexedEncoded BinaryGenerated.write_Fidelity_PSG_DeclRoot root
        Assert.Equal(tag, bytes[child bytes 0 0])
        let copy, state = BinaryGenerated.read_Fidelity_PSG_DeclRoot (indexedReadState limits bytes) |> take
        Assert.Equal(root, copy)
        Assert.Equal(0, state.Depth)
    let unknown = indexedEncoded BinaryGenerated.write_Fidelity_PSG_DeclRoot DeclRoot.LibraryExport
    unknown[child unknown 0 0] <- 4uy
    match BinaryGenerated.read_Fidelity_PSG_DeclRoot (indexedReadState limits unknown) with
    | Result.Error(BinaryError.Malformed(_, "Unknown Fidelity.PSG.DeclRoot case")) -> ()
    | other -> failwithf "Expected exact unknown declaration-root refusal, got %A" other

[<Fact>]
let ``library export binding and root tables retain their distinct flavor in a revision`` () =
    let basis = Build.bindingWithLiteral
    let binding = {basis.Nodes[NodeId 1] with Kind = SemanticKind.Binding("value", false, false, Some DeclRoot.LibraryExport)}
    let classification : ModuleClassification =
        { Name = "Library"; ModuleInit = []; Definitions = [NodeId 1]
          DeclarationRoot = Some(NodeId 1, DeclRoot.LibraryExport) }
    let original =
        {basis with
            Nodes = basis.Nodes.Add(NodeId 1, binding)
            DeclarationRoots = [NodeId 1, DeclRoot.LibraryExport]
            ModuleClassifications = Map.ofList [NodeId 1, classification]}
    Assert.Empty(Integrity.check original)
    let copy = Binary.encode limits original |> take |> Binary.decode limits |> take
    Assert.Equal(binding.Kind, copy.Nodes[NodeId 1].Kind)
    Assert.Equal<(NodeId * DeclRoot) list>(original.DeclarationRoots, copy.DeclarationRoots)
    Assert.Equal<Map<NodeId, ModuleClassification>>(original.ModuleClassifications, copy.ModuleClassifications)
    // This is a transport record control; no lambda or invocation is inferred.
    let roots = {basis.Codata with DeclarationRootLambdas = Map.ofList [NodeId 17, DeclRoot.LibraryExport]}
    let rootBytes = indexedEncoded BinaryGenerated.write_Fidelity_PSG_Codata roots
    let rootCopy, _ = BinaryGenerated.read_Fidelity_PSG_Codata (indexedReadState limits rootBytes) |> take
    Assert.Equal<Map<NodeId, DeclRoot>>(roots.DeclarationRootLambdas, rootCopy.DeclarationRootLambdas)

[<Fact>]
let ``all proper truncations and trailing bytes are refused`` () =
    let bytes = Binary.encode limits Build.bindingWithLiteral |> take
    for length in 0 .. bytes.Length - 1 do
        Assert.True(Binary.decode limits bytes[..length - 1] |> Result.isError, sprintf "Accepted truncation at %d" length)
    Binary.decode limits (Array.append bytes [|0uy|]) |> malformed

[<Fact>]
let ``unknown format schema digest and union cases fail closed`` () =
    let bytes = Binary.encode limits (Revision.empty "g") |> take
    let mutate at value = let copy = Array.copy bytes in copy[at] <- value; copy
    match Binary.decode limits (mutate 8 3uy) with
    | Result.Error(BinaryError.UnsupportedFormat 3u) -> () | other -> failwithf "%A" other
    // Binary_Images.md: "A schema, format or fingerprint mismatch is refused."
    // Change only the schema; preserve format and digest to isolate refusal.
    let precedingSchema = Revision.Schema - 1
    let incompatibleSchema = Array.copy bytes
    System.Buffers.Binary.BinaryPrimitives.WriteInt32LittleEndian(incompatibleSchema.AsSpan(12, 4), precedingSchema)
    match Binary.decode limits incompatibleSchema with
    | Result.Error(BinaryError.SchemaMismatch(expected, actual)) ->
        Assert.Equal(Revision.Schema, expected)
        Assert.Equal(precedingSchema, actual)
    | other -> failwithf "%A" other
    match Binary.decode limits (mutate 16 (bytes[16] ^^^ 0xFFuy)) with
    | Result.Error BinaryError.ContractMismatch -> () | other -> failwithf "%A" other
    let unknown = indexedEncoded BinaryGenerated.write_Fidelity_PSG_NativeLiteral NativeLiteral.Unit
    unknown[child unknown 0 0] <- 127uy
    BinaryGenerated.read_Fidelity_PSG_NativeLiteral (indexedReadState limits unknown) |> malformed

[<Fact>]
let ``structural inconsistencies fail encoding and decoding without repair`` () =
    let foreign = { Build.bindingWithLiteral with Nodes = Build.bindingWithLiteral.Nodes.Remove(NodeId 2) }
    match Binary.encode limits foreign with
    | Result.Error(BinaryError.InvalidRevision failures) -> Assert.NotEmpty failures
    | other -> failwithf "%A" other
    // Corrupt only the referenced child identity in a previously valid image.
    let bytes = Binary.encode limits Build.bindingWithLiteral |> take
    let nodes = child bytes 64 1
    let entry = child bytes nodes 1
    let node = child bytes entry 1
    let children = child bytes node 4
    let childId = child bytes children 1
    let childValue = child bytes childId 1
    BAREWire.Encoding.Encoder.writeI32 bytes childValue 999 |> ignore
    match Binary.decode limits bytes with
    | Result.Error(BinaryError.InvalidRevision failures) -> Assert.NotEmpty failures
    | other -> failwithf "%A" other

[<Fact>]
let ``null graph and byte input are typed refusals`` () =
    Binary.encode limits Unchecked.defaultof<Revision> |> malformed
    Binary.decode limits null |> malformed
    BinaryRuntime.writeArray BinaryRuntime.writeU8 (writeState limits) null |> malformed

[<Fact>]
let ``each public resource limit is enforced before acceptance`` () =
    let revision = Build.bindingWithLiteral
    let bytes = Binary.encode limits revision |> take
    let byteLimit = { limits with MaxBytes = bytes.Length - 1; MaxStringBytes = 100; MaxBigIntegerBytes = 100 }
    Binary.encode byteLimit revision |> exceeded "MaxBytes"
    Binary.decode byteLimit bytes |> exceeded "MaxBytes"
    for name, bounds in
        [ "MaxCollectionLength", { limits with MaxCollectionLength = 0 }
          "MaxDepth", { limits with MaxDepth = 1 }
          "MaxStringBytes", { limits with MaxStringBytes = 0 }
          "MaxValues", { limits with MaxValues = 1 } ] do
        Binary.encode bounds revision |> exceeded name
        Binary.decode bounds bytes |> exceeded name
    BinaryRuntime.writeBigInteger (writeState { limits with MaxBigIntegerBytes = 0 }) 1I |> exceeded "MaxBigIntegerBytes"
    BinaryRuntime.readBigInteger (readState { limits with MaxBigIntegerBytes = 0 } [|1uy;1uy;1uy|]) |> exceeded "MaxBigIntegerBytes"

[<Fact>]
let ``invalid limits refuse even an empty graph`` () =
    let invalid =
        [ {limits with MaxBytes = 0}; {limits with MaxBytes = Int32.MaxValue}
          {limits with MaxCollectionLength = -1}; {limits with MaxDepth = 0}; {limits with MaxDepth = 257}
          {limits with MaxStringBytes = -1}; {limits with MaxBigIntegerBytes = -1}; {limits with MaxValues = 0} ]
    for bounds in invalid do
        match Binary.encode bounds (Revision.empty ""), Binary.decode bounds [||] with
        | Result.Error(BinaryError.InvalidLimits _), Result.Error(BinaryError.InvalidLimits _) -> ()
        | other -> failwithf "Invalid limits accepted: %A" other

[<Fact>]
let ``integer boolean and floating primitives match independent BARE vectors`` () =
    Assert.Equal<byte>([|0xEFuy;0xCDuy;0xABuy;0x89uy|], encoded BinaryRuntime.writeU32 0x89ABCDEFu)
    Assert.Equal<byte>(Array.create 8 255uy, encoded BinaryRuntime.writeI64 -1L)
    Assert.Equal<byte>([|0xACuy;2uy|], encoded BinaryRuntime.writeUInt 300UL)
    Assert.Equal<byte>([|1uy|], encoded BinaryRuntime.writeBool true)
    Assert.Equal<byte>([|0uy;0uy;0uy;0uy;0uy;0uy;0uy;128uy|], encoded BinaryRuntime.writeF64 (BitConverter.Int64BitsToDouble Int64.MinValue))
    Assert.Equal(300UL, decoded BinaryRuntime.readUInt [|0xACuy;2uy|])
    Assert.Equal(-1L, decoded BinaryRuntime.readI64 (Array.create 8 255uy))
    BinaryRuntime.readBool (readState limits [|2uy|]) |> malformed
    BinaryRuntime.readUInt (readState limits [|0x80uy;0uy|]) |> malformed
    BinaryRuntime.readUInt (readState limits (Array.append (Array.create 9 255uy) [|2uy|])) |> malformed

[<Fact>]
let ``arbitrary integers preserve canonical magnitude and sign`` () =
    for value, bytes in [0I, [|0uy;0uy|]; 256I, [|1uy;2uy;0uy;1uy|]; -256I, [|2uy;2uy;0uy;1uy|]] do
        Assert.Equal<byte>(bytes, encoded BinaryRuntime.writeBigInteger value)
        Assert.Equal(value, decoded BinaryRuntime.readBigInteger bytes)
    for value in [bigint.One <<< 4096; -(bigint.One <<< 4096) - 1I] do
        Assert.Equal(value, encoded BinaryRuntime.writeBigInteger value |> decoded BinaryRuntime.readBigInteger)
    for bytes in [[|0uy;1uy;0uy|]; [|1uy;0uy|]; [|2uy;1uy;0uy|]; [|3uy;1uy;1uy|]; [|1uy;2uy;1uy;0uy|]] do
        BinaryRuntime.readBigInteger (readState limits bytes) |> malformed

[<Fact>]
let ``decimal bits including signed scaled zero survive and invalid flags refuse`` () =
    for value in [Decimal.Zero; Decimal.MinValue; Decimal.MaxValue; Decimal(0,0,0,true,28uy); Decimal(125,0,0,false,2uy)] do
        let copy = encoded BinaryRuntime.writeDecimal value |> decoded BinaryRuntime.readDecimal
        Assert.Equal<int>(Decimal.GetBits value, Decimal.GetBits copy)
    let golden = Array.append [|125uy;0uy;0uy;0uy|] (Array.append (Array.zeroCreate 8) [|0uy;0uy;2uy;0uy|])
    Assert.Equal<byte>(golden, encoded BinaryRuntime.writeDecimal (Decimal(125,0,0,false,2uy)))
    for at, bad in [12,1uy; 14,29uy; 15,1uy] do
        let bytes = Array.zeroCreate 16
        bytes[at] <- bad
        BinaryRuntime.readDecimal (readState limits bytes) |> malformed

[<Fact>]
let ``strict text preserves supplementary characters and rejects substitutions`` () =
    Assert.Equal<byte>([|4uy;0xF0uy;0x9Fuy;0x98uy;0x80uy|], encoded BinaryRuntime.writeString "😀")
    for value in [""; "\u0000λ😀"; "\uFFFD"] do
        Assert.Equal(value, encoded BinaryRuntime.writeString value |> decoded BinaryRuntime.readString)
    for bytes in [[|1uy;0x80uy|]; [|2uy;0xC0uy;0x80uy|]; [|3uy;0xEDuy;0xA0uy;0x80uy|]; [|4uy;0xF4uy;0x90uy;0x80uy;0x80uy|]] do
        BinaryRuntime.readString (readState limits bytes) |> malformed
    BinaryRuntime.writeString (writeState limits) (String [|char 0xD800|]) |> malformed
    BinaryRuntime.writeString (writeState limits) null |> malformed

[<Fact>]
let ``collections reject duplicate and unordered keys and members`` () =
    let mapReader = BinaryRuntime.readMap BinaryRuntime.readU8 BinaryRuntime.readBool
    for bytes in [[|2uy;1uy;0uy;1uy;1uy|]; [|2uy;2uy;0uy;1uy;1uy|]] do
        mapReader (readState limits bytes) |> malformed
    let setReader = BinaryRuntime.readSet BinaryRuntime.readU8
    for bytes in [[|2uy;1uy;1uy|]; [|2uy;2uy;1uy|]] do
        setReader (readState limits bytes) |> malformed
    Assert.Equal<Map<byte,bool>>(Map.ofList [1uy,false;2uy,true], decoded mapReader [|2uy;1uy;0uy;2uy;1uy|])
    Assert.Equal<Set<byte>>(Set.ofList [1uy;2uy], decoded setReader [|2uy;1uy;2uy|])
    BinaryRuntime.readOption BinaryRuntime.readBool (readState limits [|2uy|]) |> malformed
    BinaryRuntime.readResult BinaryRuntime.readBool BinaryRuntime.readBool (readState limits [|2uy|]) |> malformed

[<Fact>]
let ``declared allocation counts and nested types are bounded`` () =
    BinaryRuntime.readArray BinaryRuntime.readU8 (readState limits [|0xFFuy;0xFFuy;0xFFuy;0xFFuy;15uy|]) |> exceeded "MaxCollectionLength"
    let nested = [1..300] |> List.fold (fun ty _ -> TypeIdentity.Sequence ty) Build.unitType
    BinaryGenerated.write_Fidelity_PSG_TypeIdentity (BinaryIndexed.initialWrite limits) nested |> exceeded "MaxDepth"
    let bounded = [1..30] |> List.fold (fun ty _ -> TypeIdentity.Sequence ty) Build.unitType
    let tooDeep = indexedEncoded BinaryGenerated.write_Fidelity_PSG_TypeIdentity bounded
    BinaryGenerated.read_Fidelity_PSG_TypeIdentity (indexedReadState {limits with MaxDepth = 10} tooDeep) |> exceeded "MaxDepth"

[<Fact>]
let ``a node identity has an independent fixed directory golden vector`` () =
    // count=2, tag at offset40 length1, int32 identity at offset41 length4.
    let golden = Convert.FromHexString("020000000000000028000000000000000100000000000000290000000000000004000000000000000007000000")
    Assert.Equal<byte>(golden, indexedEncoded BinaryGenerated.write_Fidelity_PSG_NodeId (NodeId 7))
    let value, _ = BinaryGenerated.read_Fidelity_PSG_NodeId (indexedReadState limits golden) |> take
    Assert.Equal(NodeId 7, value)

[<Fact>]
let ``arbitrary node reads work from a relocated source without visiting siblings`` () =
    let bytes = Binary.encode limits Build.bindingWithLiteral |> take
    let backing = Array.concat [Array.create 137 0xCCuy; bytes; Array.create 29 0xDDuy]
    let reads = ResizeArray<uint64 * int>()
    let source = BAREWire.Memory.ByteSource.create (uint64 bytes.Length) (fun offset count ->
        reads.Add(offset, count)
        Some(Array.sub backing (137 + int offset) count))
    let view = Binary.openSource limits source |> take
    reads.Clear()
    for id in [2;1;2] do
        let node = Binary.tryNode (NodeId id) view |> take |> Option.get
        Assert.Equal(Build.bindingWithLiteral.Nodes[NodeId id], node)
    Assert.True(reads |> Seq.forall(fun (_, length) -> length < bytes.Length), "Random access copied the whole revision")
    Assert.Equal(None, Binary.tryNode (NodeId 999) view |> take)
    Assert.Equal(Build.bindingWithLiteral, Binary.readRevision view |> take)

[<Fact>]
let ``opening and reading one node does not hide a malformed sibling`` () =
    let bytes = Binary.encode limits Build.bindingWithLiteral |> take
    let nodes = child bytes 64 1
    let secondNode = child bytes (child bytes nodes 2) 1
    // A valid directory at the node-map level does not validate node payloads.
    BAREWire.Encoding.Encoder.writeU32 bytes (secondNode + 4) 1u |> ignore
    let view = Binary.openSource limits (BAREWire.Memory.ByteSource.ofArray bytes) |> take
    Assert.True((Binary.tryNode (NodeId 1) view |> take).IsSome)
    Binary.tryNode (NodeId 2) view |> malformed
    Binary.readRevision view |> malformed

[<Fact>]
let ``indexed offsets counts overlap holes and duplicate node keys are refused`` () =
    let original = Binary.encode limits Build.bindingWithLiteral |> take
    for corrupt in
        [ (fun bytes -> BAREWire.Encoding.Encoder.writeU64 bytes 48 UInt64.MaxValue |> ignore)
          (fun bytes -> BAREWire.Encoding.Encoder.writeU64 bytes (64 + 8) 64UL |> ignore)
          (fun bytes -> BAREWire.Encoding.Encoder.writeU64 bytes (64 + 16) UInt64.MaxValue |> ignore)
          (fun bytes -> BAREWire.Encoding.Encoder.writeU32 bytes 64 UInt32.MaxValue |> ignore)
          (fun bytes -> BAREWire.Encoding.Encoder.writeU32 bytes (64 + 4) 1u |> ignore)
          (fun bytes ->
              let nodes = child bytes 64 1
              let key = child bytes (child bytes nodes 2) 0
              BAREWire.Encoding.Encoder.writeI32 bytes (child bytes key 1) 1 |> ignore) ] do
        let bytes = Array.copy original
        corrupt bytes
        Assert.True(Binary.decode limits bytes |> Result.isError)

[<Fact>]
let ``host disposal and access exceptions are typed source failures`` () =
    let bytes = Binary.encode limits Build.bindingWithLiteral |> take
    let mutable available = true
    let source = BAREWire.Memory.ByteSource.create (uint64 bytes.Length) (fun offset count ->
        if available then Some(Array.sub bytes (int offset) count)
        else raise (ObjectDisposedException "test byte source"))
    let view = Binary.openSource limits source |> take
    available <- false
    match Binary.tryNode (NodeId 1) view, Binary.tryNode (NodeId 999) view, Binary.readRevision view with
    | Result.Error(BinaryError.SourceUnavailable _), Result.Error(BinaryError.SourceUnavailable _), Result.Error(BinaryError.SourceUnavailable _) -> ()
    | other -> failwithf "Disposed source escaped typed refusal: %A" other

[<Fact>]
let ``a scalar leaf exceeding its declared cap is refused before host allocation`` () =
    let bytes = Binary.encode limits Build.bindingWithLiteral |> take
    let nodes = child bytes 64 1
    let node = child bytes (child bytes nodes 2) 1
    let file = child bytes (child bytes node 2) 0
    let mutable copiedExcess = false
    let source = BAREWire.Memory.ByteSource.create (uint64 bytes.Length) (fun offset count ->
        if offset = uint64 file && count > 10 then copiedExcess <- true
        Some(Array.sub bytes (int offset) count))
    let view = Binary.openSource {limits with MaxStringBytes = 0} source |> take
    Binary.tryNode (NodeId 2) view |> exceeded "MaxStringBytes"
    Assert.False(copiedExcess, "Reader requested the oversized string leaf before enforcing its byte limit")

[<Fact>]
let ``collection caps refuse directory tables before host allocation`` () =
    let bytes = Binary.encode limits Build.bindingWithLiteral |> take
    let nodes = child bytes 64 1
    let bounds = {limits with MaxCollectionLength = 0}
    let empty = Build.revision []
    Assert.Equal(empty, Binary.encode bounds empty |> take |> Binary.decode bounds |> take)
    for openIndexOnly in [true; false] do
        let mutable tableRead = false
        let source = BAREWire.Memory.ByteSource.create (uint64 bytes.Length) (fun offset count ->
            if offset = uint64 (nodes + 8) then tableRead <- true
            Some(Array.sub bytes (int offset) count))
        if openIndexOnly then Binary.openSource bounds source |> exceeded "MaxCollectionLength"
        else
            let location : BinaryIndexed.Location = {Offset = 64UL; Length = uint64 (bytes.Length - 64)}
            BinaryGenerated.readRevision (BinaryIndexed.initialRead bounds source location) |> exceeded "MaxCollectionLength"
        Assert.False(tableRead, "Collection directory copied before its declared cap was checked")

[<Fact>]
let ``known record arities refuse directory tables before host allocation`` () =
    for rootRecord in [true; false] do
        let bytes = Binary.encode limits Build.bindingWithLiteral |> take
        let at = if rootRecord then 64 else child bytes (child bytes (child bytes 64 1) 1) 1
        let count, _ = BAREWire.Encoding.Decoder.readU32 bytes at
        BAREWire.Encoding.Encoder.writeU32 bytes at (count + 1u) |> ignore
        let mutable tableRead = false
        let source = BAREWire.Memory.ByteSource.create (uint64 bytes.Length) (fun offset count ->
            if offset = uint64 (at + 8) then tableRead <- true
            Some(Array.sub bytes (int offset) count))
        if rootRecord then Binary.openSource limits source |> malformed
        else
            let view = Binary.openSource limits source |> take
            Binary.tryNode (NodeId 1) view |> malformed
        Assert.False(tableRead, "Known record directory copied before its arity was checked")

[<Fact>]
let ``leaf value budgets and nested depth refuse before reading owned ranges`` () =
    let check reader writer value remaining =
        let bytes = indexedEncoded writer value
        let mutable reads = 0
        let source = BAREWire.Memory.ByteSource.create (uint64 bytes.Length) (fun offset count ->
            reads <- reads + 1
            Some(Array.sub bytes (int offset) count))
        let location : BinaryIndexed.Location = {Offset = 0UL; Length = uint64 bytes.Length}
        let state = {BinaryIndexed.initialRead limits source location with Remaining = remaining}
        reader state |> exceeded "MaxValues"
        Assert.Equal(0, reads)
    check BinaryIndexed.readU8 BinaryIndexed.writeU8 1uy 0
    check BinaryIndexed.readString BinaryIndexed.writeString "value" 1
    check BinaryIndexed.readBigInteger BinaryIndexed.writeBigInteger 100I 2
    check BinaryIndexed.readDecimal BinaryIndexed.writeDecimal 10M 3
    let bytes = indexedEncoded BinaryGenerated.write_Fidelity_PSG_TypeIdentity (TypeIdentity.Sequence Build.unitType)
    let inner = child bytes 0 1
    let mutable nestedRead = false
    let source = BAREWire.Memory.ByteSource.create (uint64 bytes.Length) (fun offset count ->
        if offset = uint64 inner then nestedRead <- true
        Some(Array.sub bytes (int offset) count))
    let location : BinaryIndexed.Location = {Offset = 0UL; Length = uint64 bytes.Length}
    BinaryGenerated.read_Fidelity_PSG_TypeIdentity (BinaryIndexed.initialRead {limits with MaxDepth = 1} source location) |> exceeded "MaxDepth"
    Assert.False(nestedRead, "Nested directory read before depth was checked")
