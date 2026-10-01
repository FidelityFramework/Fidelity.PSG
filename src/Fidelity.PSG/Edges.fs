namespace Fidelity.PSG

/// Immutable source types and ordered occurrences of a local demand derivation.
type BindingDemandEvidence = {
    SourceTypes: Map<NodeId, TypeIdentity>
    Participants: Participant list
}

/// Ports of a local evaluation contract. Operand indices identify incidences
/// within the target node, not runtime states or new semantic node identities.
[<RequireQualifiedAccess>]
type EvaluationPort =
    | Entry
    | OperandEntry of int
    | OperandExit of int
    | Ready
    | Exit

[<RequireQualifiedAccess>]
type EvaluationTransfer =
    | Continue
    | WhenTrue
    | WhenFalse
    | Resume

/// A value demand does not re-execute a referenced declaration's initializer.
[<RequireQualifiedAccess>]
type EvaluationAccess =
    | Value
    | Storage

/// Explicitly unsettled local contracts; these are not source diagnostics or
/// permission for a witness to reconstruct missing control semantics.
[<RequireQualifiedAccess>]
type EvaluationResidual =
    | MissingOperand
    | InvalidShape
    | MatchSelection
    | ExceptionFlow
    | CollectionIteration
    | CountedIteration
    | Delegation

/// How an edge participates in the graph's projections.
[<RequireQualifiedAccess>]
type LoopRangeResidual =
    | Guard
    | Step
    | OtherWrites
    | ConditionalUpdate
    | CapturedCell
    | UnknownEffect
    | Reentry
    | NonAdditive
    | MissingBound
    /// The compiler's bounded certificate-construction work was exhausted.
    /// This is not a source numeric width or a representation fallback.
    | ProofResources

type NumericOperationProof = {
    Site: NodeId; Obligation: NodeId; Body: ObligationBody; Participants: Set<NodeId>; Proven: bool
}

/// Source identity exists before numeric admission; demand consumes this row.
type BoundaryDeclaration = { Binding: NodeId; Path: NodeId list; Implementation: NodeId; Formals: NodeId list; Body: NodeId }

/// Immutable observations sufficient for boundary membership, descriptor,
/// alias, scope, incidence, native type and range premises. Other source kinds
/// contribute their full structural/reference incidence, not an ABI guess.
type BoundarySourcePremise = {
    Shape: BoundaryDeclarationFact
    EmbeddedTypes: TypeIdentity list
    ConstructorFacts: (ConstructorIdentity * TypeLayout * int * int * NTUQualifiers option * Map<string, string list>) list
    Reachable: bool
    Range: ValueRange option
    ExternLibrary: string option
    ExternSymbol: string option
    HasExtern: bool
    /// The boundary owner only reads these closed scalar metadata forms.
    Metadata: Map<string, string list * bigint list * NodeId list * TypeIdentity option>
}

type NumericDomain = {
    Premises: Map<NodeId, BoundarySourcePremise>
    Platform: BoundaryPlatformPremise option
    Roots: (NodeId * DeclRoot) list
    Escaping: Map<NodeId, string>
    Layouts: Map<TypeIdentity, SettledLayout>
    Required: Set<NodeId>
    ResultSites: Set<NodeId>
    SourceTypes: Map<NodeId, TypeIdentity>
    Elements: Map<NodeId, SettledSlot>
    ElementTypes: Map<TypeIdentity, SettledSlot>
    DeclaredScalars: Map<NTUKind, SettledSlot>
    OccurrenceRepresentations: Map<NodeId, Result<ValueRepresentation, string>>
    TypeRepresentations: Map<TypeIdentity, Result<ValueRepresentation, string>>
    ElementRanges: Map<TypeIdentity, ValueRange>
    ByteRanges: (NodeId * NodeId list * bigint * bigint * string) list
    ByteReadRanges: (NodeId * NodeId list * bigint * bigint) list
    ByteViews: BoundaryByteView list
    StringExtents: BoundaryStringExtent list
    Values: ScalarCarrier list
    Operations: NumericOperationWitness list
    OperationRequired: Set<NodeId>
    OperationMeets: Map<NodeId, Meet list>
    OperationProofs: NumericOperationProof list
    IndexTransports: NumericIndexTransport list
    IndexRequired: Set<NodeId>
    Unresolved: Map<NodeId, string>
}

[<RequireQualifiedAccess>]
type EdgeClass =
    /// Containment: the source is structurally part of the target.
    /// These are the edges that materialise as SemanticNode.Children.
    | Structural
    /// A non-containment relation the reachability walk must still follow:
    /// VarRef -> its binding, a node's type -> its TypeDef, an intrinsic ->
    /// its implementation, a string literal -> the symbol it names.
    | Reference
    /// Provenance: groups the nodes minted by one enrichment firing.
    | Provenance
    /// An obligation's constraining structure -> the obligation node.
    | Obligation
    /// Suspension, iterator and continuation evidence settled by Baker.
    /// Roles distinguish ownership, enumerated cuts and resume/live identities;
    /// these are neither containment nor executable transfer edges.
    | Suspension
    /// Baker's local evaluation contracts. Composition, dominance and frame
    /// liveness require further saturation; this is not a flattened CFG.
    | Evaluation
    /// Source activation and sharing relations, independent of sequence-local
    /// control composition and of target scheduling or representation.
    | Demand
    /// Joint numeric premises and their recurrence dependency, distinct from
    /// the local interval annotation resulting from range saturation.
    | Range
    /// Baker's complete source declaration, call and proof relations.
    | Boundary
    /// Source-settled hardware/kernel declaration and complete spatial plan.
    | Spatial

type ArrayBoundOperand = { Actual: NodeId; Binding: NodeId; Reference: NodeId }

type ArrayRangeGuard = {
    Requirement: NodeId; Predicate: NodeId; Frontier: NodeId; Continuation: NodeId
    Count: NodeId; Offset: NodeId option; Buffer: NodeId option; Length: NodeId option
    Zero: NodeId; NonnegativeCount: NodeId; NonnegativeOffset: NodeId option
    End: NodeId option; Within: NodeId option
}

type ArrayInitializationConstruction = {
    Buffer: NodeId; Index: NodeId; Initial: NodeId; Loop: NodeId; Guard: NodeId
    Current: NodeId; Write: NodeId; Step: NodeId; Advance: NodeId
}

type ArrayAllocationConstruction = {
    Site: NodeId; Owner: NodeId; Count: ArrayBoundOperand; Default: NodeId option
    Initialization: ArrayInitializationConstruction option
    Guard: ArrayRangeGuard; Participants: Set<NodeId>
}

type ArrayCopyConstruction = {
    Site: NodeId; Source: ArrayBoundOperand; SourceOffset: ArrayBoundOperand
    Destination: NodeId; DestinationOffset: ArrayBoundOperand; Count: ArrayBoundOperand
    Allocation: NodeId option; Index: NodeId option; IndexInitial: NodeId option
    Loop: NodeId option; Guard: NodeId option; Current: NodeId option
    SourceIndex: NodeId option; DestinationIndex: NodeId option
    Read: NodeId option; Write: NodeId option; Step: NodeId option; Advance: NodeId option
    Requirements: ArrayRangeGuard list; Participants: Set<NodeId>
}

type MemoryProof = {
    Site: NodeId; Obligation: NodeId; Body: ObligationBody
    Participants: Set<NodeId>; Proven: bool
}

[<RequireQualifiedAccess>]
type MemoryStringPremise =
    | Snapshot
    | ToBytesSnapshot
    | Copy
    | Storage of lower: bigint * upper: bigint * representation: string
    | Read
    | ReadRange of lower: bigint * upper: bigint
    | Ascii
    | Utf8Constant of byte list
    | ByteView of BoundaryByteView
    | Extent of BoundaryStringExtent

type MemoryStringRelation = {
    Class: EdgeClass
    Premise: MemoryStringPremise
    Ordinal: int
    Sources: NodeId list
    Target: NodeId
}

type MemoryDomain = {
    Premises: Map<NodeId, BoundarySourcePremise>
    Platform: BoundaryPlatformPremise option
    Meets: Map<NodeId, Meet list>
    Guards: (NodeId * NodeId list) list
    Requirements: (int * NodeId * NodeId list) list
    StringRelations: MemoryStringRelation list
    AllocationConstructions: ArrayAllocationConstruction list
    CopyConstructions: ArrayCopyConstruction list
    ArrayCopies: MemoryArrayCopyWitness list
    Proofs: MemoryProof list
    Required: Set<NodeId>
    Operations: (NodeId * MemoryWitnessOperation) list
    Unresolved: Map<NodeId, string>
}

type SpatialProof = {
    Site: NodeId; Obligation: NodeId; Body: ObligationBody
    Participants: Set<NodeId>; Proven: bool
}

type SpatialModuleDomain = {
    Premises: Map<NodeId, BoundarySourcePremise>
    SourceFiles: Map<NodeId, string>
    Platform: BoundaryPlatformPremise option
    Meets: Map<NodeId, Meet list>
    Representations: Map<NodeId, Result<ValueRepresentation, string>>
    Carriers: Map<NodeId, ScalarCarrier>
    NumericOperations: Map<NodeId, NumericOperationWitness>
    FieldRanges: Map<NominalTypeIdentity, Map<string, ValueRange>>
    Pins: PinMapping option
    Required: Set<NodeId>
    Hardware: HardwareModuleWitness list
    Kernels: KernelModuleWitness list
    Proofs: SpatialProof list
    Unresolved: Map<NodeId, string>
}

/// Exact relation observations used by the source lazy/captured string-origin owner.
[<RequireQualifiedAccess>]
type StringOriginRelationKind =
    | Named of string
    | ContinuationCase of int
    | EnvironmentCapture of bool
    | SequenceCaptureInitializer of bool
    | LazyCapture of bool
    | EagerDemand of EagerFrontier
    | BoundaryImplementation of NodeId

type StringOriginRelation = {
    Recorded: bool
    Class: EdgeClass
    Flavor: StringOriginRelationKind
    Ordinal: int
    Sources: NodeId list
    Target: NodeId
}

type BoundaryDomain = {
    Premises: Map<NodeId, BoundarySourcePremise>
    Platform: BoundaryPlatformPremise option
    Meets: Map<NodeId, Meet list>
    Declarations: BoundaryDeclaration list
    Imports: NodeId list
    Calls: NodeId list
    ByteViews: BoundaryByteView list
    StringExtents: BoundaryStringExtent list
    /// Baker's complete relation observation when a lazy/captured string origin was read.
    StringOriginRelations: StringOriginRelation list option
    StringOriginRoots: (NodeId * DeclRoot) list option
    StringComparisons: (NodeId * bool * NodeId list) list
    StringLengthComparisons: (NodeId * bool * NodeId list) list
    StringComparisonReads: MemoryArrayAccessWitness list
    StringComparisonSnapshots: MemoryStringViewWitness list
    StringComparisonCopies: MemoryArrayCopyWitness list
    IntrinsicDeclarations: (NodeId * IntrinsicWriteImport) list
    IntrinsicImports: IntrinsicWriteImport list
    IntrinsicCalls: IntrinsicWriteCall list
    IntrinsicProofs: IntrinsicWriteProof list
    /// Exact immutable pool facts consulted by the borrow proof, including
    /// bytes and declaration authority. Publication may not substitute a pool.
    StringStorage: (string * byte list * int * int * int * string * int64 * int * int * NodeId * (NodeId list * string * int * int * int) list) option
    DeclarationLeaves: Set<NodeId>
    DeclarationOnly: Set<NodeId>
    Links: Set<string>
    Failures: (NodeId * Set<NodeId> * string) list
}

type BoundaryCoverage = {
    Site: NodeId
    Operand: NodeId
    Ordinal: int
    Input: ValueRange
    Destination: ValueRange
    Obligation: NodeId
}

[<RequireQualifiedAccess>]
type BoundaryProofOutcome = Proven | Refuted

/// The role the source plays relative to the target -- the edge label.
/// Generalises Traversal.RegionKind, which named the same thing but was
/// handed to a callback and discarded instead of being stored.
[<RequireQualifiedAccess>]
type EdgeRole =
    | NumericDomain of NumericDomain
    | NumericCarrier of ScalarCarrier
    | NumericProof of BoundaryProofOutcome
    | NumericOperation of NumericOperationWitness
    | NumericOperationProof of NumericOperationProof
    | NumericIndexTransport of NumericIndexTransport
    | MemoryDomain of MemoryDomain
    | MemoryOperation of MemoryWitnessOperation
    | MemoryArrayCopy of MemoryArrayCopyWitness
    | ArrayAllocationConstruction of ArrayAllocationConstruction
    | ArrayCopyConstruction of ArrayCopyConstruction
    | MemoryProof of MemoryProof
    | MemoryAccessGuard
    | SpatialModuleDomain of SpatialModuleDomain
    | HardwareModule of HardwareModuleWitness
    | KernelModule of KernelModuleWitness
    | KernelIngress of KernelIngress
    | SpatialProof of SpatialProof
    | BoundaryDeclaration of BoundaryDeclaration
    | BoundaryDomain of BoundaryDomain
    | BoundaryImport of BoundaryImport
    | BoundaryCall of BoundaryCall
    | BoundaryOperand of BoundaryOperand
    | BoundaryAdaptation of Meet
    | BoundaryCoverage of BoundaryCoverage
    | BoundaryProof of BoundaryProofOutcome
    | StringByteView of BoundaryByteView
    | StringExtent of BoundaryStringExtent
    /// [nodes of the early derivation] -> the borrow site. What was derived for the
    /// borrow before the final demand rows; not a current premise.
    | StringBorrowHistory of BorrowHistory
    /// [site and actual of each early omission] -> the literal. The omissions read for
    /// the literal's storage before the final demand rows; not a current premise.
    | LiteralStorageHistory of StoragePremiseHistory
    | StringComparisonConstruction of negated: bool
    | StringLengthComparison of negated: bool
    | IntrinsicWriteAbi of IntrinsicWriteImport
    | IntrinsicWriteImport of IntrinsicWriteImport
    | IntrinsicWriteCall of IntrinsicWriteCall
    | IntrinsicWriteOperand of NodeId
    | IntrinsicWriteProof of IntrinsicWriteProof
    /// [marker; operand; transparent wrapper path; first-boundary alternatives
    /// and their real formals; callee for Actual] -> the activated frontier.
    /// Ordinal identifies the component/actual in that current owning node.
    | EagerDemand of EagerFrontier
    /// A malformed local marker/wrapper retains its owning unresolved premise.
    | EagerDemandPending
    /// [conversion; input; allocation; complete alias/write/value premises]
    /// -> exact array occurrence. Byte units, not UTF-8 sequence validity.
    | StringByteStorage of lower: bigint * upper: bigint * representation: string
    /// [allocation; array occurrence; complete write/value premises] -> element read.
    | StringByteRead
    /// The exact read enclosure derived from complete encoding storage premises.
    | StringByteRange of lower: bigint * upper: bigint
    /// [original input; fresh copy] -> conversion; copy preserves string immutability.
    | StringByteSnapshot
    /// [immutable string; internal byte view; fresh copy] -> public array conversion.
    | StringToBytesSnapshot
    /// Complete storage range establishes ASCII text.
    | StringAscii
    /// The exact immutable byte sequence passed strict UTF-8 decoding.
    | StringUtf8Constant of bytes: byte list
    /// [owner; guard; induction cell; initial value; limit; step; update; store]
    /// -> loop. Direction and strictness describe the actual comparison.
    | LoopInduction of ascending: bool * inclusive: bool
    /// [loop; induction cell; accumulator initial; store; update; delta]
    /// -> accumulator cell. Both cell and exact update acquire its enclosure.
    | LoopAccumulation
    /// Target: exact current read. Sources begin with producer owner,
    /// generator, input, enumerator, acquisition, guard and consuming loop,
    /// followed by direct support/navigation identities. Full current source
    /// revalidation remains required; this is not a scoped proof-cache key.
    | SequencePullBound
    /// Range-class correspondence for one finite product-model state. Ordinal
    /// is the model label; sourceLabel names an actual outer control occurrence.
    /// Sources are outer producer, inner producer, fresh enumerator, acquisition,
    /// guard, loop and actual control-step origin; target is the consumer current.
    /// The remaining budget belongs to that enumerator. Complete source control
    /// and iterator-census revalidation remain required for the certificate.
    | SequencePullComposition of sourceLabel: int * remainingPulls: bigint
    /// Target: accumulator cell. Sources begin with ordinary lambda, loop,
    /// seed, store, update, delta and current read, then direct support identities.
    /// Complete write/effect authority comes from current source revalidation.
    | SequenceAccumulation
    /// [owner; loop] -> cell whose recurrence remains outside admission.
    | LoopRangePending of LoopRangeResidual
    // structural
    | Callee
    | Argument
    | Parameter
    | Body
    | Scrutinee
    | CaseBinding
    | CaseGuard
    | CaseBody
    | Guard
    | ThenBranch
    | ElseBranch
    | LoopStart
    | LoopFinish
    | Collection
    | Handler
    | Cleanup
    | Element
    | FieldValue
    | CopyFrom
    | Payload
    | ArenaHint
    | AssignTarget
    | AssignValue
    | Subject
    | Index
    | Member
    | Operand
    | InterpolationPart
    /// A child attached by the builder rather than derived from the kind
    /// payload -- a Binding's value, an Intrinsic's arguments.
    | Attached
    // reference
    | Definition
    | TypeDefinition
    | IntrinsicImplementation
    | Symbol
    // provenance
    | EnrichedWith
    /// Ordered startup, its preserved source entry, and the actual execution spine.
    | ProgramInitialization
    /// Source entry and its declaration constrain an unsettled initializer.
    | ProgramInitializationPending of reason: string
    /// [module; source binding; initializer; startup lambda] -> ordered spine.
    | ProgramInitializer
    /// Startup, source entry and exact owned-unit or demanded-value premises
    /// activate this module's implementation unit before the source call.
    | ProgramUnitActivation
    /// [startup binding; source binding; source lambda; startup lambda] -> call.
    | ProgramEntryCall
    /// [startup lambda; spine; initializer] -> runtime value binding.
    | ProgramValueIntent
    /// Runtime value intent joined with the exact writable program designation.
    | ProgramValue
    /// [covering activation; caller activation; callee occurrence; implementation] -> call.
    | ProgramActivationCall
    /// A covering activation and complete finite callable uses cover the implementation.
    | ProgramActivationCoverage
    /// [allocation; covering activation; actual argument; formal; callee lambda]
    /// -> exact complete call. Full formal use remains inside the covering region.
    | SequenceInputBorrow
    /// [allocation; covering activation; callee; every complete target's
    /// implementation, formals, actuals and body] -> invocation. This proves
    /// bounded callee consumption, not a physical calling convention.
    | CallableInvocationBorrow
    /// An elaborated expression's distinct mutually exclusive branch occurrence.
    /// Sources retain the original expression and its original branch body.
    | BranchOccurrence
    /// Direct capture origin: ordered sources [lambda; captured declaration]
    /// produce the hidden formal target. The declaration may itself be a
    /// hidden formal; source tooling follows this specific relation by identity.
    | CaptureOrigin
    /// Exact environment formation inputs; the flag retains shared-cell mode.
    /// [owner; source declaration; initializer] -> environment creation.
    | EnvironmentCapture of isMutable: bool
    | EnvironmentInitializer
    | EnvironmentFormal
    /// [thunk; body; environment; formal; computed; cache; false] -> formation.
    /// This proves source structure, not residence or concurrent force safety.
    | LazyInstance
    /// [formation; captured declaration; actual initializer] -> environment.
    | LazyCapture of isMutable: bool
    /// Exact force participants, validated against the real conditional and
    /// invocation/store/publication sequence before any cached read is admitted.
    | LazyMemoization
    /// [factory; lazy formation; destination formal] -> environment constructor.
    | LazyResultDestination
    /// [factory; constructor; formal; allocation; actual destination] -> call.
    | LazyResultCall
    /// Actual allocation, covering activation, complete uses and retained inputs
    /// jointly cover one lazy instance's storage. Layout remains a separate proof.
    | LazyResidence
    /// Joint source instance, exact slot placement and complete storage uses.
    /// The thunk remains a function value; it is not an environment field.
    | LazyLayout
    /// Complete-use covering activation and retained source cells.
    | EnvironmentResidence
    /// Required reservation at its Baker firing, including rejected proposals.
    /// Target is the obligation; Sources are the participant occurrences in order.
    | EnvironmentReservation of participants: Participant list
    /// Baker's current startup/read-order premises, targeting the obligation.
    | ProgramInitializationOrder of participants: Participant list
    | ProgramInitializationOrderHistory of participants: Participant list
    /// Required caller destination: [factory implementation; closure owner;
    /// destination formal] -> exact EnvironmentCreate constructor.
    | EnvironmentResultDestination
    /// Exact prepared invocation: [factory implementation; constructor;
    /// destination formal; allocation; actual destination] -> call.
    | EnvironmentResultCall
    /// Exact source closure, implementation and formal supplying a child constructor.
    | SequenceCaptureFormation
    /// Original child slot and its eager value/cell initializer; never a new slot identity.
    | SequenceCaptureInitializer of isMutable: bool
    /// Joint environment coverage, actual call and caller-owned child destination.
    | SequenceEnvironmentBorrow
    /// A pending retained-view requirement, never a residence proof. Ordered
    /// [slot; initializer; factory lambda; formal; call; actual;
    /// destination actual; allocation] target the returned sequence constructor.
    /// The call's actual is an eager snapshot at the formal's exact position.
    | SequenceResultCapture
    /// Ordered sources [sequence owner; its generator] constrain the target
    /// Yield/YieldBang site. Ordinal is zero, not a resumption state number.
    | Delimiter
    /// Ordered sources [delegation expression; supplied sequence operand]
    /// produce the target owner-local yield after Baker expands yield!.
    | DelegationOrigin
    /// [immutable enumerator binding; successful pull guard; iteration loop]
    /// admits the target current read at that loop's first body action.
    | IteratorCurrentAdmitted
    /// [enumerator binding; successful pull guard; iteration loop] retains the
    /// current-admission dependency of the target current call's element facts.
    | SequenceElementAdmission
    /// [iterator operand; sequence owner] contributes a finite known origin.
    | SequenceElementOwner
    /// [sequence owner; exact yielded payload] contributes to the target
    /// admitted current call's range fixed point, through its delimiter.
    | SequenceElementPayload
    /// [iterator operand; unknown origin site] prevents finite narrowing.
    | SequenceElementUnknown
    /// [iterator operand; source sequence owner; generator; deferred body]
    /// supplies one possible body's source-cell writes to the target pull.
    | SequencePullBody
    /// [sequence operand; source owner; generator] establishes fresh iterator
    /// formation without invoking that deferred body at the target acquisition.
    | SequenceInitialize
    /// Exact family members, generator/formal/field identities and layout
    /// obligations establish one shared invocation/current-access convention.
    | SequenceFamilyLayout
    /// Source payloads and their owner current identities constrain the common
    /// current representation; this does not admit a current read.
    | SequenceFamilyCurrent
    /// Exact source template and fresh acquisition preserve capture identities
    /// and the uninitialized status of current/internal representation bytes.
    | SequenceTemplateCopy
    /// [operand; unresolved origin site] prevents a closed effect summary for
    /// the target iterator operation, even alongside other known origins.
    | SequenceEffectUnknown
    /// [owner; generator; payload] enumerates the target source cut's state.
    | SuspensionCut of int
    /// [owner; generator; source cut] retains an exact live-across value.
    | SuspensionLiveAcross
    /// [owner; generator; source cut] selects the generated resume entry;
    /// state zero has only owner/generator because it precedes every cut.
    | SuspensionResume of int
    /// [owner; generator; generated entry; source cut when positive] selects
    /// the actual first dispatch action after pass-through control is skipped.
    | SuspensionResumeAction of int
    /// [owner; generator; state slot] selects the completed-entry body.
    | SuspensionCompleted
    /// [owner; operand] constrains a container's indexed operand demand.
    | EvaluationOperand of EvaluationAccess
    /// Port transfer within the target container. Sources retain the owner
    /// and the operands named by the two ports; identities never hide in beta.
    | EvaluationFlow of EvaluationPort * EvaluationPort * EvaluationTransfer
    /// [owner; captured declaration] constrains deferred value formation.
    | EvaluationCapture
    /// [owner; generator] selects that generator's own body as a local root.
    | EvaluationRoot
    /// [owner; resident related sites] constrains an unsettled local contract.
    | EvaluationPending of EvaluationResidual
    | ContinuationCase of int
    /// Ordered match requirement frontier. Ordinal 0 retains the exact boolean
    /// pattern test and selected decision; ordinal 1 retains a terminal boolean
    /// condition (a source guard or a typed literal equality).
    | MatchRequirement
    | ContinuationDefault
    | FrameSlot
    /// Exact source-value identity retained by continuation realization.
    | ContinuationValue
    /// [owner; generator; actual storage root; source slot; writer; value; ...]
    /// authorizes a generated FrameRead, including its complete slot writer set.
    /// The root is the generator formal or its exact activation-local storage;
    /// immutable captures have no writers. Current storage uses and each actual
    /// writer's value correspondence must validate before retaining identity.
    | ContinuationSlotAccess
    | ContinuationRegion
    | ContinuationBorrow
    /// Source value, destination, discriminant and selected case initialization.
    | AggregateCopy
    /// Successful current read, owned snapshot and its finite activation uses.
    | AggregateSnapshot
    /// [source allocation; covering activation; captured declaration;
    /// capturing generator] proves the target sequence template's complete
    /// bounded use is covered by its captured source allocation's residence.
    | SequenceTemplateBorrow
    /// [allocation; covering entry; program binding; exact read; generator;
    /// use occurrence; complete startup/order/declaration support] proves the
    /// target constructor's bounded program read. Ordinal is the source
    /// initializer ordinal; the current target initializer must follow it.
    | SequenceProgramBorrow
    /// [allocation; covering activation; owner; generator; storage root;
    /// retained slot; writer; complete current access support] proves the
    /// target FrameRead's bounded use after validating every writer/read and
    /// excluding escaped or metadata-captured storage. A persistent formal
    /// slot additionally retains its live-across/cut and current acquisition
    /// correspondence to an exact iterator region owned by that frame.
    | SequenceSlotBorrow
    // declared platform (BAREWire docs/11: cross-applied with the code it governs)
    /// A declared memory space or buffer schema constrains the value that
    /// resides in it: source = the declaration node, target = the value.
    | Resides
    /// The structure an obligation constrains -> the obligation node.
    | Constrains
    /// [source declaration; promoted code binding] retains the original
    /// definition of one rewritten callable reference occurrence.
    | CallableReferenceOrigin
    /// [owning captured value; original declaration] -> the same source VarRef
    /// occurrence rewritten to environment access. Generated initializer/cache
    /// accesses do not carry this source-navigation relation.
    | CaptureReferenceOrigin
    /// Complete finite recurrence participants: owner, loop/guard/induction,
    /// seeds, actual ordered stores/RHS values, and demand/ordering authorities.
    /// The target is one actual cell or intermediate covered by the same proof.
    | LoopLinearRecurrence
    /// [original callable; physical implementation; environment extraction;
    /// ordered original arguments] -> the exact rewritten source invocation.
    | EnvironmentInvocation
    /// Actual sequence template allocation, owner/generator/formal and one
    /// program initializer with exact family/layout and writable-space inputs.
    /// This grants template residence, never acquisition or current validity.
    | SequenceProgramStorage
    /// Historical specialization: frozen [source declaration; source node;
    /// original clone declaration; original clone node; requesting occurrences]
    /// -> current replacement. Only the target follows subsequent fold-in.
    /// Snapshots describe an applied derivation, not current admission facts.
    | SchemeSpecialization
    /// Current finite lazy effect premises, including actual formation/call
    /// multiplicity, memoization protocol, all writes and original cell type.
    | LazyEffectRange
    /// Exact closed implementation and unused logical formal, followed by all
    /// current absence, type, invocation and hidden-convention participants.
    | OrdinaryUnusedFormal
    /// Exact invocation/formal/actual correspondence for an omitted physical
    /// operand. Direct explicit eager demand remains independently required.
    | OrdinaryUnusedActual
    | OrdinaryBindingDemand of BindingDemandEvidence
    | OrdinaryBindingDemandPending of reason: string * evidence: BindingDemandEvidence
    | OrdinaryBindingDemandHistory of BindingDemandEvidence
    /// Complete rooted activation census and typed affine transitions for a
    /// finite program cell. The arithmetic certificate supplies no lifetime.
    | FiniteCellRange

/// One directed relation. Sources retain ordered participant occurrences;
/// structural projections may be single-source while joint facts are n-ary.

type Hyperedge = {
    /// I_f -- ordered occurrences that produce or constrain the target.
    Sources: NodeId list
    /// t_f -- what they produce or constrain.
    Target: NodeId
    /// beta: which projections this edge belongs to.
    Class: EdgeClass
    /// beta: the role the sources play.
    Role: EdgeRole
    /// beta: position among same-role siblings (argument 0, 1, ...); 0 if unique.
    Ordinal: int
}
