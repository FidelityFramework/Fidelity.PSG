namespace Fidelity.PSG

/// The declared widths of the selected platform. An undeclared width carries the
/// producer's diagnostic; a reader reports it and never supplies a number.
type PlatformWidths = {
    Register: Result<int, string>
    Pointer: Result<int, string>
}

/// The declared physical layout of a borrowed view's schema.
type BorrowedViewLayout = {
    Schema: string
    ElementBits: int
    Range: ValueRange
    Alignment: int
    Access: string
}

/// One borrowed-view operation at its application site.
type BorrowedViewOperation = {
    Site: NodeId
    Operation: string
    View: NodeId
    Arguments: NodeId list
    Layout: Result<BorrowedViewLayout, string>
    Span: Result<MappedSpanModel, string>
}

/// One register access operation at its application site.
type MmioOperation = {
    Site: NodeId
    Operation: string
    Arguments: NodeId list
}

/// Declared access to storage the program does not own.
type ForeignStorageProjection = {
    BorrowedViews: Map<NodeId, BorrowedViewOperation>
    Mmio: Map<NodeId, MmioOperation>
    /// Application sites whose callee is a declared scoped mapping.
    MappedCalls: Set<NodeId>
}

/// One demand relation targeting an explicit demand marker.
/// `Frontier = None` is a relation the producer holds as pending.
type EagerDemandRelation = {
    Sources: NodeId list
    Ordinal: int
    Frontier: EagerFrontier option
    /// Whether the relation belongs to the demand class.
    IsDemand: bool
}

/// Explicit demand markers and the operands they demand.
type ExplicitDemandProjection = {
    Operands: Map<NodeId, NodeId>
    Relations: Map<NodeId, EagerDemandRelation list>
}

/// The codata a revision carries for emission, settled by the producer.
type Codata = {
    Escapes: Map<NodeId, EscapeKind>
    Curry: CurryInfo
    /// Per consumer node, its meets in operand order.
    Meets: Map<NodeId, Meet list>
    /// Per lambda, the meet of its body's last value to the body's width.
    ReturnMeets: Map<NodeId, Meet>
    Closures: Map<NodeId, ClosurePlacement>
    EnvironmentLayouts: Map<NodeId, EnvironmentLayout>
    EnvironmentDestinations: Map<NodeId, NodeId>
    EnvironmentOrigins: Map<NodeId, NodeId>
    LazyLayouts: Map<NodeId, LazyLayout>
    /// Schema origin only, never equality of actual lazy instances.
    LazyOrigins: Map<NodeId, NodeId>
    LazyDestinations: Map<NodeId, NodeId>
    KnownCallables: Map<NodeId, KnownCallable>
    CallableCarriers: Map<NodeId, CallableCarrier>
    CallableJoins: Map<NodeId, CallableJoin>
    CallableFlows: Map<NodeId, CallableFlow>
    MutableCallableStorage: Map<NodeId, MutableCallableStorage>
    ContinuationFrames: Map<NodeId, ContinuationFrame>
    SequenceOrigins: Map<NodeId, NodeId>
    SequenceFlows: Map<NodeId, SequenceFlow>
    SequenceFamilies: Map<NodeId, SequenceFamily>
    SequenceTemplateCopies: Map<NodeId, SequenceTemplateCopy>
    /// Transient activation allocation/reference -> owning continuation.
    ContinuationStorage: Map<NodeId, NodeId>
    /// Exact allocation occurrence -> owned byte region within a parent frame.
    ContinuationRegions: Map<NodeId, ContinuationRegion>
    SequenceInitializers: Map<NodeId, (NodeId * NodeId) list>
    /// Caller-owned destination for a known sequence factory constructor.
    SequenceDestinations: Map<NodeId, NodeId>
    SequenceCurrentReads: Set<NodeId>
    Pins: PinMapping option
    /// The lambda of each declaration root, with the root's flavour.
    DeclarationRootLambdas: Map<NodeId, DeclRoot>
    FunctionPointers: Map<NodeId, FunctionPointerPlan>
    Mmio: Map<NodeId, MmioAccessEvidence>
    ProgramStorage: ProgramStorageInventory
}

/// What identifies a revision and the producer that published it.
type RevisionHeader = {
    /// The version of this contract the revision conforms to.
    Schema: int
    /// The compiler implementation that published the revision.
    Producer: string
}

/// One published revision of the Program Semantic Graph. This value is everything
/// a witness receives. It is immutable and complete at publication: no reader
/// obtains a fact about the program from any other source.
type Revision = {
    Header: RevisionHeader
    Nodes: Map<NodeId, SemanticNode>
    DeclarationRoots: (NodeId * DeclRoot) list
    ModuleClassifications: Map<NodeId, ModuleClassification>
    Platform: PlatformWidths
    StaticStringPool: StaticStringPool option
    Codata: Codata
    Emission: WitnessEmissionProjection
    Foreign: ForeignStorageProjection
    Demand: ExplicitDemandProjection
    /// Every proof obligation the graph carries, in discharge order.
    Obligations: ObligationInfo list
    /// Per obligation node, the ordered sources of each relation that constrains it.
    ObligationSources: Map<NodeId, NodeId list list>
    /// The design-time discharge of `Obligations`, in SMT-LIB, as the producer transcribes it.
    ObligationQuery: string
}

module Revision =
    /// The version of the contract declared by this library.
    [<Literal>]
    let Schema = 1

    let tryNode (id: NodeId) (revision: Revision) : SemanticNode option =
        Map.tryFind id revision.Nodes
