namespace Fidelity.PSG

/// How a constructed value escapes its defining scope: the four-point lifetime lattice
/// (closure-representation.md §3.3). Read by the allocation site's witness to place the value on
/// the stack, in static storage, or in the arena.
[<RequireQualifiedAccess>]
type EscapeKind =
    | StackScoped
    | EscapesViaClosure of target: NodeId
    | EscapesViaReturn
    | EscapesViaByRef
    | StaticLifetime

/// A partial application of a flattened curried function.
type PartialApplication = { TargetBindingId: NodeId; SuppliedArgNodes: NodeId list; TotalParams: int }

/// A call that saturates a partial application: the target and every argument in order.
type SaturatedCall = { TargetBindingId: NodeId; AllArgNodes: NodeId list }

/// The curried structure of the graph once nested lambdas are flattened (Curry.fs).
type CurryInfo = {
    PartialApplications: Map<NodeId, PartialApplication>
    SaturatedCalls: Map<NodeId, SaturatedCall>
    /// Bindings that hold a partial application (their witnesses emit nothing).
    PartialAppBindings: Set<NodeId>
    /// Lambdas absorbed by flattening (unreachable now).
    AbsorbedLambdas: Set<NodeId>
}

/// What a closure environment slot holds.
[<RequireQualifiedAccess>]
type CaptureSlotKind =
    /// The actual environment of a separately known callable implementation.
    /// No function address, runtime type tag or legacy closure pair is stored.
    | EnvironmentView of owner: NodeId
    /// A complete rank-one memref descriptor for a captured mutable cell.
    /// Its payload type is retained; no address-to-view reconstruction occurs.
    | CellView of TypeIdentity
    /// A complete rank-one descriptor for a buffer-backed value. Bounds and
    /// stride travel with the value rather than being reconstructed from an address.
    | ValueView of TypeIdentity
    /// Owned aggregate bytes, never a descriptor to separately lived storage.
    | InlineValue of TypeIdentity
    /// One word: the base address of a buffer-backed value (a record, tuple, union, lazy, seq,
    /// function value's pair) or of a mutable cell; construction extracts the base pointer first.
    | Address
    /// One word held as it arrives, such as an opaque handle.
    | Handle
    /// A string or array, decomposed into its base address and its extent: two words.
    | Decomposed
    /// A scalar at its settled slot.
    | Scalar of SettledSlot

/// One settled slot of a closure environment.
type CaptureSlot = {
    Capture: string
    Index: int
    Holds: CaptureSlotKind
    /// The byte offset after the environment's prefix.
    ByteOffset: int
    Bytes: int
    Mutable: bool
    SourceNode: NodeId option
}

/// The prefix an environment carries before its capture slots.
[<RequireQualifiedAccess>]
type ClosurePrefix =
    /// The code pointer.
    | RegularClosure
    /// A lazy thunk: the computed flag, the value at its slot, the code pointer.
    | LazyThunk of value: SettledSlot * valueBytes: int
    /// A seq generator: the state, the current value's address, the code pointer.
    | SeqGenerator

/// The settled placement of a closure's environment (Layout_As_Joint_Constraint.md §2.1, the
/// closure aggregate). Composer reads offsets and sizes here and computes none.
type ClosurePlacement = {
    Lambda: NodeId
    Prefix: ClosurePrefix
    PrefixBytes: int
    Captures: CaptureSlot list
    /// The captures alone.
    CapturesBytes: int
    /// One word for the code pointer, then the captures.
    WithCodePointerBytes: int
    /// The prefix, then the captures.
    WithPrefixBytes: int
}

/// A continuation slot retains the declaration/value identity used by Baker's
/// liveness relation and the exact representation chosen by placement.
type ContinuationSlot = {
    Source: NodeId
    ValueType: TypeIdentity
    Field: SettledField
    Holds: CaptureSlotKind
    IsCapture: bool
}

/// Shared typed slot placement for one materialized closure environment.
/// Empty captures have a real zero-byte, alignment-one environment.
type EnvironmentLayout = {
    Owner: NodeId
    Implementation: NodeId
    Formal: NodeId
    Slots: ContinuationSlot list
    Bytes: int
    Alignment: int
    Obligations: NodeId list
}

/// One explicit lazy schema's typed storage. Each runtime formation/allocation
/// retains its own environment operand; a shared schema never shares a cache.
/// The computed bit and cached result are source declarations, and the cache
/// is uninitialized until the admitted force stores a result before publication.
type LazyLayout = {
    Owner: NodeId
    Thunk: NodeId
    Formal: NodeId
    Computed: NodeId
    Cached: NodeId
    Slots: ContinuationSlot list
    Bytes: int
    Alignment: int
    Obligations: NodeId list
}

/// This proves only the function half and layout. The environment itself is
/// always the value at the queried occurrence, including aliases/frame reads.
type KnownCallable = { Implementation: NodeId; EnvironmentOwner: NodeId }

/// The environment portion of a settled callable convention. The layout stays
/// in EnvironmentLayouts; this relation identifies its actual leading formal.
type CallableEnvironment = { Owner: NodeId; Formal: NodeId }

/// A physical boundary retains each value participant. Callable components
/// refer to that occurrence's settled carrier, so code/environment expansion
/// cannot be guessed from the source type or a different formation's layout.
[<RequireQualifiedAccess>]
type CallableValueShape = Data of NodeId | Callable of NodeId | Sequence of NodeId | Lazy of NodeId

/// One callable occurrence's settled physical boundary. Parameter identities,
/// rather than the source type's arrow count, determine native arity. SourceType
/// remains the public type; hidden formals belong only to Parameters.
/// None denotes code alone, never an invented empty environment.
type CallableCarrier = {
    Occurrence: NodeId
    SourceType: TypeIdentity
    Implementation: NodeId
    Parameters: (string * TypeIdentity * NodeId) list
    ParameterShapes: CallableValueShape list
    /// Logical formals whose physical components are absent under current,
    /// source-owned unused-formal evidence. Their source types remain intact.
    OmittedParameters: Set<NodeId>
    Result: NodeId
    ResultShape: CallableValueShape
    Environment: CallableEnvironment option
}

/// A finite source dispatch retains every possible callable, rather than
/// assigning a representative implementation to a mutable read. Read identifies
/// the snapshot frontier; aliases retain that frontier after later writes.
type CallableJoin = {
    Occurrence: NodeId
    SourceType: TypeIdentity
    Storage: NodeId
    Read: NodeId
    Alternatives: NodeId list
}

/// A complete semantic invocation retains every formal/actual participant.
/// This row is value-flow evidence, not a physical code/environment choice.
type CallableFlowCall = {
    Call: NodeId
    Implementation: NodeId
    Parameters: NodeId list
    Arguments: NodeId list
    Result: NodeId
}

/// Ordinary callable transport across formals, results and immutable aliases.
/// Unlike CallableJoin it has no mutable storage or read-snapshot frontier.
type CallableFlow = {
    Occurrence: NodeId
    SourceType: TypeIdentity
    Alternatives: NodeId list
    Dependencies: Map<NodeId, NodeId list>
    Calls: CallableFlowCall list
}

/// A write updates the finite alternative discriminator and the actual
/// environment descriptor together. The discriminator is not a code address.
type MutableCallableWrite = { Site: NodeId; Destination: NodeId; Value: NodeId; Alternative: int }

/// Source-owned mutable callable protocol. Code remains a function value, never
/// a cell field. Captures name the original shared cell; this semantic protocol
/// does not itself prove its allocation or any retained environment's lifetime.
type MutableCallableStorage = {
    Binding: NodeId
    SourceType: TypeIdentity
    Initializer: MutableCallableWrite
    Writes: MutableCallableWrite list
    Reads: Set<NodeId>
    Alternatives: NodeId list
    AlternativeCarriers: CallableCarrier list
    EnvironmentBytes: int option
    Captures: Set<NodeId>
    Borrows: Set<NodeId>
}

/// Source construction, fresh enumeration and generator access share this
/// single settled frame contract. The callable identity is separate from its
/// storage; no slot carries a function address.
type ContinuationRegion = {
    ParentOwner: NodeId
    ParentFormal: NodeId
    ChildOwner: NodeId
    Offset: int
    Bytes: int
    Alignment: int
}

type ContinuationFrame = {
    Owner: NodeId
    Generator: NodeId
    Formal: NodeId
    State: NodeId
    Current: NodeId
    Slots: ContinuationSlot list
    Bytes: int
    Alignment: int
    ScratchSlots: ContinuationSlot list
    ScratchBytes: int
    ScratchAlignment: int
    Initializers: (NodeId * NodeId) list
    ResumeStates: int list
    Obligations: NodeId list
}

/// Complete source alternatives at one sequence value occurrence. This is
/// flow evidence, not permission to substitute an environment instance or an
/// admitted common physical carrier. Unknown alternatives prevent elision.
type SequenceFlow = {
    Occurrence: NodeId
    ElementType: TypeIdentity
    IsEnumerator: bool
    Owners: Set<NodeId>
    Unknown: Set<NodeId>
}

/// One member of a source-settled sequence transport family. Every field keeps
/// its own source identity; a common byte extent does not select a generator.
type SequenceFamilyMember = {
    Generator: NodeId
    Formal: NodeId
    Signature: TypeIdentity
    State: NodeId
    Current: NodeId option
    Slots: ContinuationSlot list
    Captures: Set<NodeId>
    Uninitialized: Set<NodeId>
    Obligations: NodeId list
}

/// A finite, connected set of exact sequence alternatives with one physical
/// invocation/current-access convention. Code and the actual environment are
/// still separate values. Empty members supply no current success premise.
type SequenceFamily = {
    Identity: NodeId
    ElementType: TypeIdentity
    Participants: Set<NodeId>
    Members: Map<NodeId, SequenceFamilyMember>
    Bytes: int
    Alignment: int
    StateField: SettledField
    CurrentField: SettledField option
    CurrentRepresentation: (TypeIdentity * CaptureSlotKind) option
}

/// A fresh enumeration copies representation from this exact template. Capture
/// identities can themselves retain deferred computations; copying never forces
/// them or grants source definite assignment or a successful-current premise.
type SequenceTemplateCopy = {
    Family: NodeId
    Template: NodeId
    SourceAcquisition: NodeId
    StorageSite: NodeId
    Residence: EscapeKind
    Region: ContinuationRegion option
    Bytes: int
    Alignment: int
    AddressSpace: NTUMemorySpace
    /// Exhaustive actual backing allocations for each possible constructor.
    /// The fresh destination is proved disjoint from every one of these.
    TemplateStorage: Map<NodeId, Set<NodeId>>
    /// Snapshot/deferred value identities are retained; copying cannot invoke
    /// an initializer or clone a referenced mutable cell.
    Initializers: Map<NodeId, (NodeId * NodeId) list>
    /// Owned child regions have no live interior views in the template. Their
    /// contents become meaningful only under the generator's later stores.
    UninitializedRegions: Map<NodeId, NodeId list>
    Captures: Map<NodeId, Set<NodeId>>
    Uninitialized: Map<NodeId, Set<NodeId>>
}

/// A native callback keeps a resolved declaration edge, without a closure environment.
type FunctionPointerPlan =
    | Address of symbol: string * lambda: NodeId
    | Invoke of pointer: NodeId * arguments: NodeId list * parameters: TypeIdentity list * result: TypeIdentity

/// A quoted source condition's standing at its declaration dependencies.
type PredicateStatus = Established | Contradicted | Pending

type PredicateEvidence = {
    Name: string
    Declaration: NodeId
    Expression: NodeId
    Dependencies: NodeId list
    Status: PredicateStatus
    Message: string
    Source: string
}

type MmioBindingEvidence = {
    Plan: string
    Grant: string
    Register: string
    Region: string
    Mapping: string
    AddressSpace: string
    DeclarationNodes: NodeId list
    Predicates: PredicateEvidence list
    /// Platform/loader assertions. Arithmetic checks do not prove hardware.
    Premises: string list
}

type MmioAccessEvidence = {
    Operation: string
    Address: bigint
    Bits: int
    Binding: MmioBindingEvidence option
}

[<RequireQualifiedAccess>]
type ProgramStorageShape = Bytes | Scalar of SettledSlot | ValueView of TypeIdentity

/// One source-owned writable object. No linker section, address or pooled
/// offset is implied: those belong to the selected backend's commitment.
type ProgramStorageEntry = {
    Identity: ProgramStorageIdentity
    SourceType: TypeIdentity
    Shape: ProgramStorageShape
    Bytes: int
    Alignment: int
    SpaceNode: NodeId
    Space: BAREWire.Platform.MemorySpace
    Participants: Set<NodeId>
}

type ProgramStorageInventory = {
    Entries: Map<ProgramStorageIdentity, ProgramStorageEntry>
    Reservations: Map<NodeId, BAREWire.Platform.WritableReservation>
    Unresolved: Map<ProgramStorageIdentity, string>
}

/// Source-settled physical projection of one logical call. The source retains
/// every actual and its type, including computations that remain deferred.
type OrdinaryCallProjection = {
    Implementation: NodeId
    Actuals: NodeId list
    Omitted: Set<int>
    Eager: Set<int>
}

[<RequireQualifiedAccess>]
type CallableSymbolName =
    | ModuleBinding of moduleName: string * name: string
    | LocalBinding of declaration: NodeId * name: string
    | RootBinding of name: string
    | Anonymous of implementation: NodeId

type CallableEmissionDeclaration = {
    Lookup: NodeId
    Implementation: NodeId
    Parameters: (string * TypeIdentity * NodeId) list
    Result: NodeId
    Context: LambdaContext
    Captures: CaptureInfo list
    Name: CallableSymbolName
    /// None is an observed absence, not permission to search for another owner.
    Parent: NodeId option
    Participants: Set<NodeId>
}

type CallableEmissionCall = {
    Site: NodeId
    Implementation: NodeId
    Parameters: (string * TypeIdentity * NodeId) list
    Arguments: NodeId list
    Result: NodeId
    SignatureData: Set<NodeId>
    Participants: Set<NodeId>
}

type CallableProgramInstance = {
    Carrier: CallableCarrier
    Allocation: NodeId option
    Participants: Set<NodeId>
}

/// Logical source comparison; no representation/ABI selection is implied.
[<RequireQualifiedAccess>]
type CallableBranchComparison = Equal | NotEqual

/// This authority includes all current reachable origin inputs, relation/capture
/// membership, and absence/uniqueness tests. Participants below are navigation;
/// they are not a complete dependency key or permission for selective reuse.
[<RequireQualifiedAccess>]
type CallableBranchScope = WholeRevision

/// An exact zero-offset constructor alternative in the final origin fixed point.
type CallableBranchAlternative = {
    Constructor: NodeId
    Tag: int
    Payloads: NodeId list
}

/// A unanimous final logical guard observation authored by Baker. Both source
/// arms remain in the graph; selection neither erases effects nor proves reachability.
type CallableBranchObservation = {
    Choice: NodeId
    Guard: NodeId
    Operator: NodeId
    Comparison: CallableBranchComparison
    TagRead: NodeId
    Subject: NodeId
    Literal: NodeId
    ExpectedTag: int
    UnionType: TypeIdentity
    TrueArm: NodeId
    FalseArm: NodeId
    SelectedArm: NodeId
    Alternatives: CallableBranchAlternative list
    /// Ordered direct observations with explicit roles; WholeRevision remains
    /// the joint authority, including transitive inputs and negative premises.
    Participants: Participant list
}

/// Conservative joint authority for callable facts. Each listed occurrence
/// depends on every observation in this revision. Empty observation inventory
/// has empty use sets. Current full source revalidation is mandatory; a new
/// origin/opaque path can invalidate a row without removing any participant ID.
type CallableBranchAuthority = {
    Scope: CallableBranchScope
    Observations: Map<NodeId, CallableBranchObservation>
    CarrierUses: Set<NodeId>
    FlowUses: Set<NodeId>
    CallUses: Set<NodeId>
}

module CallableBranchAuthority =
    let empty = {
        Scope = CallableBranchScope.WholeRevision
        Observations = Map.empty
        CarrierUses = Set.empty
        FlowUses = Set.empty
        CallUses = Set.empty
    }

/// Eager source-owned observations for passive callable witnessing. No field
/// contains an analysis callback or a deferred semantic computation. These are
/// snapshot observations; source revision/worklist authority is a separate
/// contract, and the immutable leaf emission model additionally freezes types.
type CallableEmissionProjection = {
    Branches: CallableBranchAuthority
    Carriers: Map<NodeId, CallableCarrier>
    Joins: Map<NodeId, CallableJoin>
    Flows: Map<NodeId, CallableFlow>
    MutableStorage: Map<NodeId, MutableCallableStorage>
    ValueShapes: Map<NodeId, CallableValueShape>
    SignatureData: Map<NodeId, Set<NodeId>>
    Calls: Map<NodeId, CallableEmissionCall>
    /// Only actual source instance paths appear here, not all pairs of nodes.
    Transports: Map<NodeId, Set<NodeId>>
    Declarations: Map<NodeId, CallableEmissionDeclaration>
    Symbols: Map<NodeId, CallableSymbolName>
    IntrinsicAliases: Set<NodeId>
    DirectCallees: Map<NodeId, NodeId>
    ForeignCalls: Set<NodeId>
    MutableRetentions: Set<NodeId>
    ProgramInstances: Map<NodeId, CallableProgramInstance>
    VoidCallbacks: Set<NodeId>
    VoidPointers: Set<NodeId>
    NativeEntries: Map<NodeId, string>
    FunctionBindings: Set<NodeId>
    DefinitionOnlyBindings: Set<NodeId>
    DefinitionOnlyLambdas: Set<NodeId>
    /// Physical components of each logical formal, indexed by its actual code
    /// declaration. Empty components mean source-proven omitted transport.
    /// A shared formal can occupy different positions in different occurrences.
    Arguments: Map<NodeId, Map<NodeId, int list>>
    AliasTargets: Map<NodeId, NodeId>
    TakesEnvironment: Set<NodeId>
    UnitNodes: Set<NodeId>
    ClosedData: Set<NodeId>
    Supports: Map<NodeId, Set<NodeId>>
}

type OrdinaryDemandProjection = {
    Parameters: Map<NodeId, Set<NodeId>>
    Calls: Map<NodeId, OrdinaryCallProjection>
    DeferredOnly: Set<NodeId>
}

/// Source-validated storage contracts. These are completed values, never lazy
/// analyses or readers over a graph. Witnesses preserve the actual operands
/// against these identities and cannot reconstruct missing source authority.
type LazyWitnessContract = { Layout: LazyLayout; ElementType: TypeIdentity; ThunkBody: NodeId }

type LazyProgramWitness = { Owner: NodeId; Allocation: NodeId }

type SequenceWitnessContract = { Flow: SequenceFlow; Family: SequenceFamily }

type SequenceProgramWitness = { Owner: NodeId; Generator: NodeId; Allocation: NodeId; Participants: Set<NodeId> }

type StartupInitializerWitness = { Module: NodeId; Binding: NodeId; Initializer: NodeId; Ordinal: int }

type StartupWitness = {
    EntryBinding: NodeId
    EntryLambda: NodeId
    SourceBinding: NodeId
    SourceLambda: NodeId
    OriginalBody: NodeId
    Spine: NodeId
    EntryCall: NodeId
    Symbol: string
    Initializers: StartupInitializerWitness list
    ValueBindings: Set<NodeId>
}

type StorageWitnessProjection = {
    Lazies: Map<NodeId, LazyWitnessContract>
    LazyOccurrences: Map<NodeId, NodeId>
    LazyValues: Set<NodeId>
    DefinitionOnlyThunks: Set<NodeId>
    LazyPrograms: Map<NodeId, LazyProgramWitness>
    Sequences: Map<NodeId, SequenceWitnessContract>
    SequenceCopies: Map<NodeId, SequenceTemplateCopy>
    SequencePrograms: Map<NodeId, SequenceProgramWitness>
    Startup: StartupWitness option
    SlotAuthorities: Set<NodeId>
    Requirements: Map<NodeId, RequirementWitness>
    PatternRequirements: Map<NodeId, NodeId>
    ProgramStorage: ProgramStorageInventory
    LiteralPoolAnchors: string list
}

type BoundaryEmissionProjection = {
    Imports: Map<NodeId, BoundaryImport>
    ByScope: Map<NodeId, NodeId list>
    Calls: Map<NodeId, BoundaryCall>
    ByteViews: Map<NodeId, BoundaryByteView>
    StringExtents: Map<NodeId, BoundaryStringExtent>
    IntrinsicWriteImports: Map<NodeId, IntrinsicWriteImport>
    IntrinsicWrites: Map<NodeId, IntrinsicWriteCall>
    IntrinsicWriteProofs: Map<NodeId, IntrinsicWriteProof list>
    /// Exact source declaration bindings whose bodies are placeholders, not
    /// executable ordinary function definitions.
    DeclarationLeaves: Set<NodeId>
    /// Exclusive structural declaration nodes retained for source proof. They
    /// have no executable coverage obligation and cannot justify an SSA value.
    DeclarationOnly: Set<NodeId>
    /// Link requirements come from this admitted source boundary domain.
    Links: Set<string>
}

/// Complete emission-domain facts published by their source owners. Absence is
/// distinct from a valid publication whose domain maps happen to be empty.
type NumericWitnessProjection = {
    Values: Map<NodeId, ScalarCarrier>
    Operations: Map<NodeId, NumericOperationWitness>
    OperationRequired: Set<NodeId>
    IndexTransports: Map<NodeId, NumericIndexTransport>
    Required: Set<NodeId>
    ResultSites: Set<NodeId>
    Unresolved: Map<NodeId, string>
    SourceTypes: Map<NodeId, TypeIdentity>
    Layouts: Map<TypeIdentity, SettledLayout>
    Elements: Map<NodeId, SettledSlot>
    ElementTypes: Map<TypeIdentity, SettledSlot>
    DeclaredScalars: Map<NTUKind, SettledSlot>
    OccurrenceRepresentations: Map<NodeId, Result<ValueRepresentation, string>>
    TypeRepresentations: Map<TypeIdentity, Result<ValueRepresentation, string>>
}

type MemoryWitnessProjection = {
    Operations: Map<NodeId, MemoryWitnessOperation>
    ArrayCopies: Map<NodeId, MemoryArrayCopyWitness>
    Required: Set<NodeId>
    Unresolved: Map<NodeId, string>
}

type SpatialModuleProjection = {
    Hardware: Map<NodeId, HardwareModuleWitness>
    Kernels: Map<NodeId, KernelModuleWitness>
    Required: Set<NodeId>
    MetadataOnly: Set<NodeId>
    ByScope: Map<NodeId, NodeId list>
    CodeRoots: Set<NodeId>
}

type WitnessEmissionProjection = {
    Ordinary: OrdinaryDemandProjection
    Callable: CallableEmissionProjection
    Storage: StorageWitnessProjection
    Boundary: BoundaryEmissionProjection
    Numeric: NumericWitnessProjection
    Memory: MemoryWitnessProjection
    Spatial: SpatialModuleProjection
}

/// Source-authored domains. Consumers retain or re-witness these domains; they
/// never recover dependency boundaries from emitted operations.
[<RequireQualifiedAccess>]
type WitnessRegionKind = Common | ScalarCallable

type WitnessRegion = {
    Identity: string
    Flavor: WitnessRegionKind
    Root: NodeId option
    Anchor: NodeId option
    /// Actual structural breadcrumbs, nearest parent first.
    Path: (NodeId * NodeId list * NodeId list) list
    Members: Set<NodeId>
    Supports: Set<NodeId>
    Fingerprint: string
    Dependencies: Set<string>
}

type WitnessSegmentation = { Version: int; Regions: WitnessRegion list }

/// A source string's view into the BAREWire-owned static byte pool.
type StaticStringEntry = {
    NodeIds: NodeId list
    Content: string
    Offset: int
    Length: int
    StorageLength: int
}

/// One immutable allocation plan shared by obligations and native emission.
/// Offsets are pool-relative; the linker assigns its aligned absolute origin.
type StaticStringPool = {
    Symbol: string
    Bytes: byte list
    Alignment: int
    Size: int
    UsedSize: int
    Entries: StaticStringEntry list
    SpaceName: string
    Capacity: int64
    SpaceAlignment: int
    Granularity: int
    DeclarationNode: NodeId
}

/// Whether the storage of a string literal was materialized in the static string
/// pool. The compiler service states it for every reachable string literal where
/// it lays out the pool.
[<RequireQualifiedAccess>]
type LiteralStorage =
    /// The literal's bytes are the entry at this position of `StaticStringPool.Entries`.
    | Materialized of entry: int
    /// No demanded position reads the literal: the premise states the omission relations
    /// whose omitted actual contains it.
    | NotMaterialized of premise: StoragePremise
