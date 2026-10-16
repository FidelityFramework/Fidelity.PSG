namespace Fidelity.PSG

/// Exact source declaration resident in the containing compiled program image.
type ProgramImageCodeLifetime = {
    Module: NodeId
    Binding: NodeId
    Implementation: NodeId
}

/// Source boundary facts are carried by joint Baker rows, before publication.
[<RequireQualifiedAccess>]
type MeetKind = ExtendUnsigned | ExtendSigned | Truncate | ExtendFloat | TruncateFloat

type Meet = { Consumer: NodeId; Operand: NodeId; From: int; To: int; Adapt: MeetKind }

[<RequireQualifiedAccess>]
type BoundaryScalar =
    | Integer of bits: int * signed: bool
    | Boolean
    | Entry of invocation: NodeId
    /// Exact resource declaration owns the opaque native ABI and nullability.
    /// This is neither a source integer nor permission to expose an address.
    | ResourceHandle of declaration: NodeId * nullable: bool
    /// Exact direct-call writable byte-buffer declaration; never a numeric scalar.
    | WritableBytes of declaration: NodeId

/// The physical target carriers settled from a quoted native entry signature.
/// This has no C symbol: the code is the original Clef declaration.
type NativeEntrySignature = {
    Parameters: BoundaryScalar list
    Result: BoundaryScalar option
    CallingConvention: string
}

/// A physical slot settled by the source numeric/layout owner.
[<RequireQualifiedAccess>]
type SettledSlot =
    | InlineBytes of bytes: int * alignment: int
    | Integer of bits: int * representation: string option
    | Bool
    | Char
    | Real of bits: int
    | Pointer of words: int
    | Unit
    | Opaque of what: string
    /// Nonnull, nonspatial logical handle. Alignment is settled independently
    /// from the selected target layout; width does not imply alignment.
    | CHandle of handleType: TypeIdentity * bits: int * alignment: int

type SettledField = { Name: string; Slot: SettledSlot; Offset: int option; Size: int option; Align: int option }

[<RequireQualifiedAccess>]
type SettledLayout =
    | Record of fields: SettledField list * size: int option * align: int option
    | Union of cases: (string * SettledSlot option) list * payloadOffset: int option * size: int option * align: int option

/// Immutable source representation. No checker cells or native-type lookup is
/// available to a witness through this contract.
[<RequireQualifiedAccess>]
type ValueRepresentation =
    | Scalar of SettledSlot
    | Buffer of count: int option * element: ValueRepresentation
    | Record of fields: (string * ValueRepresentation) list * placement: (int list * int * int) option
    /// The slot row owns selector/environment data placement. Code is not data.
    | CallableComponent of slot: NodeId * data: ValueRepresentation
    | Union of cases: (string * ValueRepresentation list) list * placement: (int * int * int) option
    | Tag of cases: int

type ScalarCarrier = {
    Site: NodeId
    Slot: SettledSlot
    Range: ValueRange
    Representation: NumericRepresentation option
    Declaration: NodeId option
    SourceType: TypeIdentity
    Obligations: NodeId list
    Participants: Set<NodeId>
}

/// Exact source-authorized transport into the selected platform's index domain.
type NumericIndexTransport = {
    Site: NodeId
    Operand: NodeId
    Carrier: ScalarCarrier
    PointerDeclaration: NodeId
    PointerBits: int
    Unsigned: bool
    Capacity: ValueRange
    Obligation: NodeId
    Participants: Set<NodeId>
}

[<RequireQualifiedAccess>]
type NumericOperationKind =
    | Add | Subtract | Multiply | Divide | Remainder
    | BitAnd | BitOr | BitXor | ShiftLeft | ShiftRight
    | Equal | NotEqual | Less | LessOrEqual | Greater | GreaterOrEqual
    | Negate | Complement | Identity | LogicalNot

[<RequireQualifiedAccess>]
type NumericOperationForm = Integer of signed: bool | Real | Boolean | Unit | OpaqueReference

type NumericOperationOperand = { Actual: NodeId; Carrier: ScalarCarrier option; Adaptation: Meet option }

type NumericOperationWitness = {
    Site: NodeId; Callee: NodeId; Kind: NumericOperationKind; Form: NumericOperationForm
    Operands: NumericOperationOperand list; OperationCarrier: SettledSlot option
    Representation: NumericRepresentation option; Declaration: NodeId option
    Result: ScalarCarrier; ResultAdaptation: Meet option; Range: ValueRange option
    Obligations: NodeId list; Participants: Set<NodeId>
}

type BoundaryDeclarationFact = {
    Form: string
    Text: string list
    Numbers: bigint list
    References: NodeId list
    Children: NodeId list
    Parent: NodeId option
    SourceType: TypeIdentity
}

/// A source-declared resource protocol only. This row grants no nullable-word
/// conversion, acquisition, cleanup, alias retirement or execution authority.
type BoundaryResourceDeclaration = {
    Identity: NodeId
    Acquisition: NodeId
    AcquisitionBody: NodeId
    AcquisitionDescriptor: NodeId
    Release: NodeId
    ReleaseBody: NodeId
    ReleaseDescriptor: NodeId
    ReleaseFormal: NodeId
    ReleaseOrdinal: int
    PointerBits: int
    AcquisitionType: TypeIdentity
    ResultType: TypeIdentity
    HandleType: TypeIdentity
    Contract: BAREWire.Descriptors.ResourceDescriptor
    DeclarationFacts: Map<NodeId, BoundaryDeclarationFact>
    Participants: Set<NodeId>
}

/// Exact writable-byte declaration provenance only; this grants no borrow,
/// foreign memory effect, call adapter, proof discharge or execution authority.
type BoundaryWritableBufferDeclaration = {
    Identity: NodeId
    Declaration: NodeId
    Body: NodeId
    Formals: NodeId list
    Descriptor: NodeId
    Parameter: int
    CountParameter: int
    BufferFormal: NodeId
    CountFormal: NodeId
    Contract: BAREWire.Descriptors.WritableBufferDescriptor
    DeclarationFacts: Map<NodeId, BoundaryDeclarationFact>
    Participants: Set<NodeId>
}

/// Current direct application and finite byte-storage/proof incidence.
type BoundaryWritableBufferUse = {
    Call: NodeId
    Declaration: NodeId
    Parameter: int
    CountParameter: int
    Buffer: NodeId
    Count: NodeId
    Allocation: NodeId
    Capacity: NodeId
    ByteFormat: NodeId
    CountCoverage: NodeId
    StorageCoverage: NodeId
    Participants: Set<NodeId>
}

type BoundaryImport = {
    Identity: NodeId
    Binding: NodeId
    Scope: NodeId
    Library: string
    Symbol: string
    CallingConvention: string
    DeclarationPath: NodeId list
    Parameters: (NodeId * BoundaryScalar) list
    Result: BoundaryScalar option
    Participants: Set<NodeId>
    SourceTypes: Map<NodeId, TypeIdentity>
    DeclarationFacts: Map<NodeId, BoundaryDeclarationFact>
}

/// Original tagged Option selection at one native-entry argument. Absence is
/// explicit source evidence, never a null function value or native authority.
type BoundaryOptionalEntry = {
    Construction: NodeId
    CaseOrdinal: int
    Payload: NodeId option
    Formation: NodeId option
    Transport: Set<NodeId>
    /// The existing boundary ledger owns target conversion/absence readiness.
    Obligation: NodeId
}

type BoundaryOperand = {
    Actual: NodeId
    Formal: NodeId
    Abi: BoundaryScalar
    Adaptation: Meet option
    OptionalEntry: BoundaryOptionalEntry option
}

/// A source-stated loading assumption; node identities describe this revision.
type BoundaryLoading = {
    Identity: NodeId
    Binding: NodeId
    Selector: string
    Contract: BAREWire.Platform.ProcessLinkContract
    Platform: NodeId
    Core: NodeId
    DeclarationFacts: Map<NodeId, BoundaryDeclarationFact>
    Participants: Set<NodeId>
}

type BoundaryEntry = {
    Formation: NodeId
    Operand: NodeId
    Import: NodeId
    Declaration: NodeId
    Loading: NodeId
    SourceType: TypeIdentity
    Transport: Set<NodeId>
    Participants: Set<NodeId>
}

[<RequireQualifiedAccess>]
type BoundaryCallbackExtent =
    | DuringCall
    | ProcessExit of ExitBinding: NodeId option * SuccessStatus: int

/// One conditional registration occurrence, never a synchronous invocation.
type BoundaryCallbackRegistration = {
    Call: NodeId
    Parameter: int
    Formation: NodeId
    Invocation: NodeId
    Result: NodeId
    Context: NodeId list
    Participants: Set<NodeId>
}

/// Exact quoted receiving contract and its source-resolved native formal/scope.
type BoundaryCallbackInvocation = {
    Identity: NodeId
    Import: NodeId
    Parameter: int
    Formal: NodeId
    Scope: NodeId
    Contract: BAREWire.Descriptors.CallbackInvocationContract
    Signature: NativeEntrySignature
    Extent: BoundaryCallbackExtent
    Participants: Set<NodeId>
}

/// Source-issued closed native entry. Lifetime and numeric conversions retain
/// their existing owners; activation supplies no fabricated foreign arguments.
[<RequireQualifiedAccess>]
type CallbackAbsenceInputRole =
    | Binding | Parameter | Hypothesis | HypothesisIdentity | HypothesisVersion | HypothesisSource

/// Independent quoted absence promise, with complete current source content.
/// Invocation names the receiving descriptor, never a callable occurrence.
type BoundaryCallbackAbsence = {
    Quote: NodeId
    DescriptorBinding: NodeId
    Record: NodeId
    Import: NodeId
    Parameter: int
    Formal: NodeId
    Invocation: NodeId
    Contract: BAREWire.Descriptors.CallbackAbsenceContract
    SourcePath: NodeId list
    Inputs: (CallbackAbsenceInputRole * NodeId list) list
    DeclarationFacts: Map<NodeId, BoundaryDeclarationFact>
}

type BoundaryClosedEntry = {
    Formation: NodeId
    Operand: NodeId
    Declaration: NodeId
    Implementation: NodeId
    Formals: NodeId list
    Body: NodeId
    Lifetime: ProgramImageCodeLifetime
    Invocation: NodeId
    ParameterAdaptations: Meet option list
    ResultAdaptation: Meet option
    Registrations: Map<NodeId * int * NodeId list, BoundaryCallbackRegistration>
    Transport: Set<NodeId>
    Participants: Set<NodeId>
}

type BoundaryByteView = {
    Site: NodeId
    Source: NodeId
    ExtentSource: NodeId
    Representation: NumericRepresentation
    RepresentationDeclaration: NodeId
    StaticOrigins: Map<NodeId, bigint>
    /// The occurrences of the borrow, in order: the row's own occurrences, then one group
    /// for each demanded input and one for each omitted input with the site of every omission
    /// that is its reason, by call and ordinal, with the roles of a group in case order; an
    /// omitted actual is in the group of its omission's site, at its ordinal, and a callee's
    /// body is in the group of the callee. A node in two groups or two roles
    /// occurs in each.
    Participants: ParticipantEvidence
}

type BoundaryStringExtent = {
    Site: NodeId
    Source: NodeId
    ExtentSource: NodeId
    StaticOrigins: Map<NodeId, bigint>
    /// The occurrences of the extent, ordered and grouped as `BoundaryByteView.Participants`.
    Participants: ParticipantEvidence
}

type IntrinsicWriteImport = {
    Identity: NodeId
    Scope: NodeId
    Symbol: string
    Fd: BoundaryScalar
    Count: BoundaryScalar
    Result: BoundaryScalar
    ByteRepresentation: NumericRepresentation
    Core: NodeId
    ReturnContract: NodeId
    Endpoint: NodeId
    Surface: NodeId
    SyscallNumber: bigint
    Participants: Set<NodeId>
}

type IntrinsicWriteCall = {
    Site: NodeId
    Import: NodeId
    Callee: NodeId
    Fd: NodeId
    Buffer: NodeId
    Count: NodeId
    FdAdaptation: Meet option
    CountAdaptation: Meet option
    ResultAdaptation: Meet option
    Participants: Set<NodeId>
}

type IntrinsicWriteProof = {
    Site: NodeId
    Obligation: NodeId
    Ordinal: int
    Body: ObligationBody
    Participants: Set<NodeId>
}

/// Native result ordinal zero is converted indivisibly into the enclosing
/// call's logical Option result. No intermediate source pointer is introduced.
type BoundaryResourceAcquisition = {
    Declaration: NodeId
    Tag: SettledSlot
    NoneCase: int
    SomeCase: int
    Conversion: NodeId
    Cleanup: NodeId
}

/// The enclosing call owns the exact unary actual/formal vector. Cleanup is
/// the original acquisition's alias/exit obligation, not a new release promise.
type BoundaryResourceRelease = {
    Declaration: NodeId
    Acquisition: NodeId
    Cleanup: NodeId
}

[<RequireQualifiedAccess>]
type BoundaryResourceUse =
    | AcquireNullable of BoundaryResourceAcquisition
    | ReleaseOwned of BoundaryResourceRelease

[<RequireQualifiedAccess>]
type BoundaryResourceAccessKind = OptionTag | OptionPayload | ImmutableAlias

type BoundaryResourceSelection = {
    Decision: NodeId
    Scrutinee: NodeId
    Arm: int
    CaseOrdinal: int option
    Guard: (NodeId * bool) option
}

/// Per-read lineage, distinct from call incidence. Selection records actual
/// source guard polarity; it does not define true as the Some alternative.
type BoundaryResourceAccess = {
    Site: NodeId
    Source: NodeId
    Acquisition: NodeId
    Declaration: NodeId
    Kind: BoundaryResourceAccessKind
    Selection: BoundaryResourceSelection list
    Cleanup: NodeId
    Participants: Set<NodeId>
}

type BoundaryCall = {
    Site: NodeId
    Import: NodeId
    Callee: NodeId
    Entry: NodeId option
    Arguments: BoundaryOperand list
    ErasedUnitArguments: NodeId list
    Result: BoundaryScalar option
    ResultAdaptation: Meet option
    Resource: BoundaryResourceUse option
    Participants: Set<NodeId>
    SourceTypes: Map<NodeId, TypeIdentity>
}

/// Only source-selection and numeric facts consulted by boundary rules. The
/// startup configuration is deliberately absent: it establishes no boundary.
type BoundaryPlatformPremise = {
    Id: string
    Description: string option
    Loading: string option
    LibraryPath: string option
    SourcePaths: Set<string>
    Architecture: string option
    OS: string option
    RuntimeClaim: RuntimeModel option
    Substrate: SubstrateKind option
    Dimensions: Map<string, int>
    Representations: Map<string, NumericRepresentation>
    EndpointReturns: Map<string, ReturnBound>
}

type MemoryExtentWitness = {
    Site: NodeId
    Source: NodeId
    Element: NumericRepresentation
    ElementDeclaration: NodeId
    Result: ScalarCarrier
    Extent: BoundaryStringExtent
    IndexUnsigned: bool
    Participants: Set<NodeId>
}

type RequirementWitness = {
    Site: NodeId
    Condition: NodeId
    Diagnostic: string
    Frontier: NodeId
    Continuation: NodeId
    PatternTest: NodeId option
    Participants: NodeId list
}

[<RequireQualifiedAccess>]
type ProgramStorageIdentity = Allocation of NodeId | BindingSlot of NodeId

type MemoryArrayExtentWitness = { Site: NodeId; Source: NodeId; Element: SettledSlot; Result: ScalarCarrier; Participants: Set<NodeId> }

type MemoryBoundsWitness = {
    Buffer: NodeId
    Index: NodeId
    IndexCarrier: ScalarCarrier
    ExtentCarrier: ScalarCarrier
    IndexUnsigned: bool
    Length: NodeId
    Lower: NodeId
    Upper: NodeId
    Requirement: RequirementWitness
    Participants: Set<NodeId>
}

type MemoryArrayAccessWitness = {
    Site: NodeId; Buffer: NodeId; Index: NodeId; Value: NodeId option
    Element: SettledSlot; Adaptation: Meet option; Bounds: MemoryBoundsWitness; Participants: Set<NodeId>
}

[<RequireQualifiedAccess>]
type MemoryResidence = Stack of scope: NodeId * space: NodeId | Program of ProgramStorageIdentity | ImmutableProgram of space: NodeId

type MemoryArrayLiteralWitness = {
    Site: NodeId; Elements: (NodeId * Meet option) list; Element: SettledSlot
    Length: int; Residence: MemoryResidence; Initializers: NativeLiteral list option
    Alignment: int; ElementBytes: int; Participants: Set<NodeId>
}

type MemoryArrayAllocationWitness = {
    Site: NodeId; Count: NodeId; CountCarrier: ScalarCarrier; IndexUnsigned: bool
    Element: SettledSlot; ElementBytes: int; Alignment: int; Residence: MemoryResidence
    MinimumCount: bigint; MaximumCount: bigint; Requirement: RequirementWitness
    Construction: ArrayAllocationConstruction; Participants: Set<NodeId>
}

type MemoryArrayCopyWitness = {
    Site: NodeId; Source: NodeId; SourceOffset: NodeId; Destination: NodeId; DestinationOffset: NodeId
    Count: NodeId; CountCarrier: ScalarCarrier; CountOperand: ArrayBoundOperand
    Allocation: NodeId option; Loop: NodeId option
    Read: MemoryArrayAccessWitness option; Write: MemoryArrayAccessWitness option
    Requirements: RequirementWitness list; Participants: Set<NodeId>
}

[<RequireQualifiedAccess>]
type MemoryPlace =
    | MutableCell of binding: NodeId
    | ExistingReference of source: NodeId
    | ArrayElement of buffer: NodeId * index: NodeId * bounds: MemoryBoundsWitness
    | RecordField of receiver: NodeId * receiverBytes: int * field: SettledField

type MemoryAddressWitness = { Site: NodeId; Place: MemoryPlace; Element: SettledSlot option; ElementBytes: int option; PointerBits: int; Participants: Set<NodeId> }

[<RequireQualifiedAccess>]
type MemoryStringViewDirection = FromBytes | ToBytes

type MemoryStringViewWitness = {
    Site: NodeId
    Source: NodeId
    Owner: NodeId
    Snapshot: NodeId
    Direction: MemoryStringViewDirection
    SourceCarrier: ValueRepresentation
    ResultCarrier: ValueRepresentation
    Element: SettledSlot
    Representation: NumericRepresentation
    Declaration: NodeId
    Extent: ScalarCarrier
    Participants: Set<NodeId>
}

[<RequireQualifiedAccess>]
type MemoryWitnessOperation =
    | BufferExtent of MemoryExtentWitness
    | ArrayExtent of MemoryArrayExtentWitness
    | ArrayAccess of MemoryArrayAccessWitness
    | ArrayLiteral of MemoryArrayLiteralWitness
    | ArrayAllocation of MemoryArrayAllocationWitness
    | Address of MemoryAddressWitness
    | StringView of MemoryStringViewWitness

type PinConstraint = { PortName: string; PackagePin: string; IOStandard: string; Direction: string }

type ClockConstraint = { PortName: string; PackagePin: string; IOStandard: string; FrequencyHz: int64 }

type ResetConstraint = { PortName: string; IsExternal: bool; PackagePin: string; IOStandard: string; ActiveHigh: bool }

/// Immutable declared pins shared by source spatial settlement and target realization.
type PinMapping = {
    Pins: PinConstraint list
    Clock: ClockConstraint
    Reset: ResetConstraint option
    DevicePart: string
    FieldPinAttrs: Map<string, string list>
}

type HardwarePortWitness = { Name: string; Path: string list; Representation: ValueRepresentation; Declaration: NodeId }

type HardwareStateFieldWitness = {
    Name: string; Literal: NodeId; Reset: bigint; Slot: SettledSlot
    Range: ValueRange; Capacity: ValueRange
}

type HardwareModuleWitness = {
    Site: NodeId; Scope: NodeId; Name: string
    StepBinding: NodeId; Implementation: NodeId
    Parameters: (string * NodeId) list; Result: NodeId
    StateRepresentation: ValueRepresentation
    InputRepresentation: ValueRepresentation option
    ResultRepresentation: ValueRepresentation
    InputPorts: HardwarePortWitness list; OutputPorts: HardwarePortWitness list
    ResetFields: HardwareStateFieldWitness list
    ClockReference: NodeId; ClockDeclaration: NodeId; ResetDeclaration: NodeId
    ClockPath: Set<NodeId>; Pins: PinMapping
    MetadataOnly: Set<NodeId>; Participants: Set<NodeId>; Obligations: NodeId list
}

/// A complete ordered scalar computation, including actual argument identity.
/// Operations retain the numeric owner's exact construction and adaptations.
[<RequireQualifiedAccess>]
type KernelScalarLiteral = Integer of bigint | Boolean of bool | Character of char

[<RequireQualifiedAccess>]
type KernelScalarStep =
    | Parameter of site: NodeId * ordinal: int * carrier: ScalarCarrier
    | Literal of site: NodeId * value: KernelScalarLiteral * carrier: ScalarCarrier
    | Alias of site: NodeId * source: NodeId * carrier: ScalarCarrier * adaptation: Meet option
    | Operation of NumericOperationWitness

/// These are source-declared topology/scheduling facts, not backend defaults.
type KernelTransport = {
    Declaration: NodeId
    Representation: NumericRepresentation
    Range: ValueRange
}

/// Source-declared external decoding domains, before ordinary range saturation.
type KernelIngress = {
    Site: NodeId; Scope: NodeId; Target: NodeId; Core: NodeId
    ComputeBinding: NodeId; Implementation: NodeId
    ComputePath: Set<NodeId>
    Uses: Map<NodeId, BoundaryDeclarationFact>
    Parameters: (string * NodeId) list; Result: NodeId
    Inputs: KernelTransport list; Output: KernelTransport
    Participants: Set<NodeId>
    Premises: Map<NodeId, BoundaryDeclarationFact>
    SourceFiles: Map<NodeId, string>
    Platform: BoundaryPlatformPremise option
}

type KernelTargetPlan = {
    Declaration: NodeId; Device: string; Columns: int
    ShimRow: int; ComputeRow: int; FifoDepth: int; Iterations: bigint
    Participants: Set<NodeId>
}

type KernelTileSlice = { Column: int; ShimRow: int; ComputeRow: int; Offset: int; Elements: int }

type KernelModuleWitness = {
    Site: NodeId; Scope: NodeId; Name: string
    ComputeBinding: NodeId; Implementation: NodeId
    Parameters: (string * NodeId) list; Result: NodeId
    Steps: KernelScalarStep list
    Ingress: KernelIngress
    ElementsSite: NodeId; GrainSite: NodeId; Elements: int; Grain: int
    Target: KernelTargetPlan; Tiles: KernelTileSlice list
    MetadataOnly: Set<NodeId>; Participants: Set<NodeId>; Obligations: NodeId list
}

[<RequireQualifiedAccess>]
type SpatialModuleWitness = Hardware of HardwareModuleWitness | Kernel of KernelModuleWitness
