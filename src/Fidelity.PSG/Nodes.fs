namespace Fidelity.PSG

/// A part of an interpolated string
[<RequireQualifiedAccess>]
type InterpolatedPart =
    /// A literal string segment
    | StringPart of string
    /// An expression hole (the {expr} parts)
    | ExprPart of NodeId

/// Module that provides the intrinsic function
/// Used by Alex to dispatch to appropriate emission logic without string matching
[<RequireQualifiedAccess>]
type IntrinsicModule =
    | Sys           // System calls (write, read, exit, nanosleep, etc.)
    | NativeDefault // Default value generation (zeroed)
    | String        // String operations (concat2, contains, etc.)
    | Array         // Array operations (zeroCreate, length, get, set)
    | Math          // Math functions
    | Unchecked     // Unchecked arithmetic
    | Operators     // Built-in operators (op_Addition, op_LessThan, etc.)
    | Parse         // String parsing (int, float - NTU string→numeric conversion)
    | Format        // Value formatting (string - NTU numeric→string conversion)
    | Convert       // Type conversions (float, int, int64, byte, etc. - numeric↔numeric)
    | Crypto        // Cryptographic operations (sha1, base64Encode, base64Decode)
    | Bits          // Bit manipulation and byte order (htons, ntohs, float↔int bits)
    | DateTime      // DateTime operations (now, utcNow, today, toString, components)
    | TimeSpan      // TimeSpan operations (fromMilliseconds, fromSeconds, components)
    | FnPtr         // Function pointer operations (fromSymbol, invoke, ofFunction)
    | Mmio          // Opaque exact-width volatile register access
    | BorrowedView  // Declared mapped-storage access; no address constructors
    | Lazy          // Lazy values (create, force, isValueCreated)
    | Seq           // Sequence generation (seq { }, toArray, toList, etc.)
    | SeqEnumerator // Sequence enumerator operations (moveNext, current) - PRD-15/16
    | Arena         // Arena allocation (fromPointer, alloc, allocAligned, remaining, reset)
    | Platform      // Platform info (wordSize, sizeof)
    // PRD-13a: Core Collections
    | Map           // Immutable map operations (empty, add, tryFind, containsKey, values, keys, etc.)
    | Set           // Immutable set operations (empty, add, contains, remove, union, intersect)
    | List          // Immutable list operations (head, tail, length, map, filter, fold, etc.)
    | Option        // Option operations (map, bind, defaultValue, isSome, isNone)
    | Result        // Result operations (map, bind, mapError, isOk, isError, defaultValue)

/// Category of intrinsic - guides how Alex should emit it
[<RequireQualifiedAccess>]
type IntrinsicCategory =
    | Platform      // Emits as platform-specific syscall (Sys.*, Console.*)
    | Memory        // Emits as memory operation (MemRef.load, store, alloca)
    | Arithmetic    // Emits as arith dialect ops (op_Addition, etc.)
    | Comparison    // Emits as comparison ops (op_LessThan, etc.)
    | Bitwise       // Emits as bitwise ops (op_BitwiseAnd, etc.)
    | Conversion    // Emits as type conversion (int, float, etc.)
    | StringOp      // Emits as string manipulation (concat2, etc.)
    | Pure          // Emits as pure MLIR (no side effects, NativeDefault.zeroed)
    | Reactive      // Emits as reactive signal operations (Signal.*, Effect.*, Memo.*)

/// Rich metadata for compiler intrinsics
type IntrinsicInfo = {
    /// The module providing this intrinsic
    Module: IntrinsicModule
    /// The operation name within the module (e.g., "write", "get", "concat2")
    Operation: string
    /// Category guiding emission strategy
    Category: IntrinsicCategory
    /// Original full name for error messages/debugging (e.g., "Sys.write")
    FullName: string
}

/// Context in which a Lambda operates, affecting how captures are extracted at runtime.
[<RequireQualifiedAccess>]
type LambdaContext =
    /// Standard closure: extract captures from {code_ptr, cap0, cap1, ...} at indices 1, 2, ...
    | RegularClosure
    /// Lazy thunk: extract captures from {computed, value, code_ptr, cap0, cap1, ...} at indices 3, 4, ...
    | LazyThunk
    /// Sequence generator context
    | SeqGenerator

/// How a node should be emitted during code generation.
[<RequireQualifiedAccess>]
type EmissionStrategy =
    /// Standard inline emission: emit this node as encountered during traversal.
    | Inline
    /// Separate function: this node's parent handles its emission specially.
    /// captureCount: Number of captures in the enclosing Lambda/SeqExpr.
    | SeparateFunction of captureCount: int
    /// Module-level value binding: emit at start of main function.
    | MainPrologue

/// Declaration root flavor — what makes a binding the "top" of a design.
/// Platform-agnostic: the pipeline routes based on DeclRoot kind.
[<RequireQualifiedAccess>]
type DeclRoot =
    | EntryPoint        // CPU: [<EntryPoint>] or name="main" — OS calls this
    | HardwareModule    // FPGA: [<HardwareModule>] — this IS the circuit
    | KernelModule      // NPU: [<KernelModule>] — compute kernel dispatched to AIE tiles

/// Classification of module members for code generation.
type ModuleClassification = {
    Name: string
    ModuleInit: NodeId list
    Definitions: NodeId list
    DeclarationRoot: (NodeId * DeclRoot) option
}

/// Patterns in match expressions
[<RequireQualifiedAccess>]
type Pattern =
    | Const of NativeLiteral
    | Var of name: string * ty: TypeIdentity
    | Wildcard
    | Tuple of elements: Pattern list
    | Union of caseName: string * tagIndex: int * payload: Pattern option * unionType: TypeIdentity
    | Record of fields: (string * Pattern) list * recordType: TypeIdentity
    | Array of elements: Pattern list
    | Or of Pattern * Pattern
    | And of Pattern * Pattern
    | As of Pattern * name: string
    | Null
    | IsType of ty: TypeIdentity
    | Exception of exnType: TypeIdentity * bindName: string option

/// A case in a match expression
type MatchCase = {
    /// The pattern to match
    Pattern: Pattern
    /// PatternBinding NodeIds for variables bound by this pattern.
    PatternBindings: NodeId list
    /// Optional guard expression
    Guard: NodeId option
    /// The body to execute if matched
    Body: NodeId
}

/// An arm in a case elimination — enriched by Baker with concrete bindings.
/// Pattern carries the structural info (Union tag index, payload type).
/// Bindings are fully resolved (DUEliminate + Binding via letBindAt).
type CaseArm = {
    /// The pattern (carries Union tag index and payload type info)
    Pattern: Pattern
    /// NodeIds of binding nodes created by extractPatternBindings
    Bindings: NodeId list
    /// Optional guard expression
    Guard: NodeId option
    /// The body expression
    Body: NodeId
}

/// The exponent relation required by a numeric operation. These laws concern
/// dimensions; they do not assert numeric range, precision or nonzero divisors.
[<RequireQualifiedAccess>]
type DimensionalRule =
    | Product
    | Quotient
    | SameDimension
    | Comparison

/// What an obligation asserts. Every constant is a literal fixed at saturation;
/// the two dispatches transcribe, never compute.
type MappedSpanModel = {
    PointerBits: int
    MaximumExtent: bigint
    ElementBytes: int
    BaseAlignment: int
    ElementAlignment: int
}

/// Numeric premises of an admitted monotone loop, normalized to increasing
/// coordinates. Original source identities and direction stay in F.
type FiniteLoopTripModel = {
    InitialLower: bigint
    LimitUpper: bigint
    MinimumStep: bigint
    Inclusive: bool
    MaximumIterations: bigint
}

/// One exact continuation occurrence and its remaining successful-pull budget.
/// Baker retains the complete source/control correspondence separately.
type FiniteSequencePullStep = {
    Label: int
    Suspend: bool
    Successors: int list
    Remaining: bigint
}

/// A nonnegative potential bounds successful suspensions along every retained
/// path. This is a pull-count bound, not a claim that evaluation terminates.
type FiniteSequencePullModel = {
    Entry: int
    MaximumPulls: bigint
    Steps: FiniteSequencePullStep list
}

/// An additive enclosure across all iteration prefixes, including the initial
/// state and the final write. This is independent of any physical carrier.
type AdditiveLoopInvariantModel = {
    MaximumIterations: bigint
    InitialLower: bigint
    InitialUpper: bigint
    DeltaLower: bigint
    DeltaUpper: bigint
    Lower: bigint
    Upper: bigint
}

/// One checked square-and-optional-multiply step. Matrices and exponents are
/// mathematical integers, independent of any selected runtime representation.
type RecurrencePowerStep = {
    Odd: bool
    Exponent: bigint
    Matrix: bigint list list
}

/// A finite nonnegative linear enclosure. Source incidence separately proves
/// the actual ordered updates and coefficient bounds. The certificate proves
/// every prefix fits the final monotone upper trajectory, including final stores.
type FiniteLinearRecurrenceModel = {
    MaximumIterations: bigint
    InitialLower: bigint list
    InitialUpper: bigint list
    CoefficientLower: bigint list list
    CoefficientUpper: bigint list list
    Powers: RecurrencePowerStep list
    Lower: bigint list
    Upper: bigint list
}

[<RequireQualifiedAccess>]
type ObligationBody =
    /// Finite program initialization phases supplied by Baker. This arithmetic
    /// checks order only; source incidence and lowering preservation are separate.
    | ProgramInitializationOrder of initializerOrdinal: int * initializerCount: int * useOrdinals: int list
    | FiniteLoopTrip of FiniteLoopTripModel
    | FiniteSequencePull of FiniteSequencePullModel
    | AdditiveLoopInvariant of AdditiveLoopInvariantModel
    /// The additive/index step after successful native mapping guards establish
    /// a finite byte extent. Native allocation provenance and stride*rows
    /// arithmetic are explicit premises, not conclusions of this QF_LIA slice.
    | MappedElementSpan of model: MappedSpanModel
    /// Exact integer literal enclosed by the range already analysed on its node.
    | IntegerLiteralRange of value: bigint * lower: bigint * upper: bigint
    /// The analysed integer range fits the representation actually selected
    /// from the platform declaration; this does not assert physical placement.
    | IntegerRepresentationCoverage of lower: bigint * upper: bigint * minimum: bigint * maximum: bigint
    /// Every admitted divisor is distinct from zero.
    | IntegerDivisorNonzero of lower: bigint * upper: bigint
    /// Native shifts require an exact nonnegative count below the operation width.
    | IntegerShiftCount of lower: bigint * upper: bigint * operationBits: int
    /// Exact source partition and bounded repeated transaction schedule.
    | SpatialKernelPartition of elements: bigint * grain: bigint * columns: int * slices: (int * bigint * bigint) list * fifoDepth: int * iterations: bigint
    /// Dimensional positions in an ordinary call: instantiated signature versus
    /// actual arguments/result. A missing side is an incompatible type shape,
    /// never an invented dimensionless value. Paths include partial results.
    | ApplicationDimensions of comparisons: (string * Dimension option * Dimension option) list
    /// Exact source-real literal and the singleton enclosure it seeds.
    | RealLiteralRange of value: ExactRational * lower: ExactRational * upper: ExactRational
    /// Finite-bound coverage against the actual representation declaration.
    /// This is a range obligation, not a rounding or optimal-selection claim.
    | RealRepresentationCoverage of lower: ExactRational * upper: ExactRational * minimum: ExactRational * maximum: ExactRational
    /// Actual operand/result dimensions from the saturated graph. Free measure
    /// variables retain their identities as formal generators; the solver
    /// checks each coefficient, including axes absent from another operand.
    /// Comparisons have no numeric result dimension (None).
    | DimensionalRelation of rule: DimensionalRule * left: Dimension * right: Dimension * result: Dimension option
    /// storage = len + 1 (the NUL byte is reserved at allocation)
    | StorageReservation of len: int * storage: int
    /// view = len AND view < storage (the terminator is never written)
    | ViewContainment of view: int * len: int * storage: int
    /// final storage byte is 0x00
    | NulSentinel of lastByte: int
    /// consecutive layout of the given storages is pairwise disjoint, spans
    /// exactly `span` bytes, and -- where a declared space bounds it -- the
    /// span fits the space's capacity. `capacity` is None when no declaration
    /// was found to cite.
    | ConsecutiveLayout of storages: int list * span: int * capacity: int64 option
    /// Concrete BAREWire placements in the exact byte pool emitted by Composer.
    /// Every alignment, extent and capacity is checked, never assumed.
    | StaticStorageLayout of slots: (int * int * int) list * usedSize: int * allocationSize: int * poolAlignment: int * capacity: int64 * spaceAlignment: int * granularity: int
    /// Exact ordered continuation slots, including alignment padding. This
    /// establishes layout only, not allocation lifetime or a memory budget.
    /// The empty transient activation layout has extent zero and alignment one.
    | ContinuationLayout of slots: (int * int * int) list * extent: int * alignment: int
    /// Proposed individual environment extent in declared writable space. Missing
    /// premises refute coverage; this proves neither lifetime nor aggregate capacity.
    | EnvironmentStorageReservation of extent: int option * alignment: int option * capacity: int64 option * spaceAlignment: int option * granularity: int option
    /// String.concat2 copy discipline: for ANY operand lengths a, b >= 0
    /// (pinned where the operand is a literal), the two copy windows [0,a) and
    /// [a,a+b) lie within the (a+b)-byte allocation.
    | ConcatCopyBound of leftLen: int option * rightLen: int option
    /// A declared buffer's capacity is positive.
    | CapacityPositive of capacity: int64
    /// A declared buffer's capacity is at most its declared space's capacity.
    | CapacityFits of capacity: int64 * spaceCapacity: int64
    /// The count handed to a reader is the declared capacity, which sizes the
    /// allocation the same declaration governs (count <= allocation).
    | InputBufferBound of count: int64 * allocation: int64
    /// Every possible immutable origin supplies this same invocation's count
    /// and logical extent. Storage includes the sentinel, the read excludes it.
    | StringBorrowBound of origins: (bigint * bigint * bigint) list
    /// For any successful read of r bytes, 1 <= r <= capacity, the trimmed copy
    /// of r - 1 bytes is within bound.
    | InputCopyBound of capacity: int64 * bound: int64
    | FiniteLinearRecurrence of FiniteLinearRecurrenceModel
    /// Every prefix of finitely many signed additive effects. Source evidence
    /// separately binds each (maximum executions, exact delta) contribution to
    /// current typed stores and actual memoization-instance activation counts.
    | FiniteAdditiveEffects of initial: bigint * contributions: (bigint * bigint) list * lower: bigint * upper: bigint

/// The obligation record carried by an Obligation node.
type ObligationInfo = {
    /// Stable anchor name: the identity that travels through both dispatches
    Id: string
    /// The family (callsheet vocabulary): "storage-reservation", "buffer-capacity", ...
    Kind: string
    /// SMT-LIB logic fragment: "QF_LIA" or "QF_BV"
    Logic: string
    /// Human-readable statement (ledger and demo surface)
    Statement: string
    /// Origin. A program site is file:line:col; a declaration is
    /// `<description id>:<declaration name>` (BAREWire Platform/Obligations.fs).
    Source: string
    /// External rule cross-references (CWE ids)
    Refs: string list
    Body: ObligationBody
}

/// Kind of type definition
type TypeDefKind =
    | RecordDef of fields: (string * TypeIdentity) list
    | UnionDef of cases: (string * (string option * TypeIdentity) list) list
    | ClassDef
    | InterfaceDef
    | StructDef
    | EnumDef of cases: (string * NativeLiteral) list  // Uses NativeLiteral, not NativeLiteral
    | AbbreviationDef of target: TypeIdentity

/// Kind of member
type MemberKind =
    | Method
    | Property
    | Field
    | Constructor
    | Event

/// The kind of semantic node - what syntactic/semantic construct it represents
[<RequireQualifiedAccess>]
type SemanticKind =
    | Binding of name: string * isMutable: bool * isRecursive: bool * declRoot: DeclRoot option
    | Application of func: NodeId * args: NodeId list
    | Lambda of parameters: (string * TypeIdentity * NodeId) list * body: NodeId * captures: CaptureInfo list * enclosingFunction: string option * context: LambdaContext
    | Literal of value: NativeLiteral
    | VarRef of name: string * definition: NodeId option
    | Match of scrutinee: NodeId * cases: MatchCase list
    /// Structural elimination (catamorphism) — Baker-enriched form of Match.
    /// Preserves the fold structure: constructor index → (bindings, body).
    /// No DUGetTag, comparison, or IfThenElse nodes — those are elision concerns.
    | CaseElimination of scrutinee: NodeId * arms: CaseArm list
    | Sequential of nodes: NodeId list
    | WhileLoop of guard: NodeId * body: NodeId
    /// Baker-settled finite continuation selection. Each child is a complete
    /// region; the witness pulls those regions without discovering successors.
    | ContinuationDispatch of selector: NodeId * cases: (int * NodeId) list * otherwise: NodeId
    /// Typed access to a slot whose identity and layout belong to a settled
    /// continuation frame. The slot reference is not an initializer demand.
    | FrameRead of frame: NodeId * slot: NodeId
    /// Borrow the typed cell view, retaining its frame's lifetime obligation.
    | FrameBorrow of frame: NodeId * slot: NodeId
    | FrameWrite of frame: NodeId * slot: NodeId * value: NodeId
    /// Transient activation storage, separate from the persistent suspension
    /// frame. Its exact slots and extent are settled on the owning continuation.
    | ContinuationStorage of owner: NodeId
    /// Internal caller-owned destination for one sequence factory result.
    /// Allocation does not initialize the frame; the factory constructor does.
    | ContinuationAllocate of owner: NodeId
    /// Uninitialized owned aggregate backing at a proven activation occurrence.
    | AggregateStorage of source: NodeId
    /// Initialize a case in an explicit typed destination; returns unit.
    | DUInitialize of destination: NodeId * caseName: string * caseIndex: int * payload: NodeId option
    /// A logical callable retains its implementation separately from its
    /// actual environment value. The implementation body remains deferred.
    | ClosureValue of implementation: NodeId * environment: NodeId
    /// Formation snapshots already evaluated captures at this occurrence.
    /// Slot identities are provenance, never demands to reevaluate declarations.
    | EnvironmentCreate of owner: NodeId * initializers: (NodeId * NodeId) list
    /// Caller-owned storage for one returned callable environment; initialization
    /// remains at the original formation frontier in the factory.
    | EnvironmentAllocate of owner: NodeId
    | EnvironmentReference of callable: NodeId
    | EnvironmentRead of environment: NodeId * slot: NodeId
    | EnvironmentBorrow of environment: NodeId * slot: NodeId
    | EnvironmentWrite of environment: NodeId * slot: NodeId * value: NodeId
    | ForLoop of var: string * start: NodeId * finish: NodeId * isUp: bool * body: NodeId
    | ForEach of var: string * formal: NodeId * collection: NodeId * body: NodeId
    | IfThenElse of guard: NodeId * thenBranch: NodeId * elseBranch: NodeId option
    /// Always-active source invariant. The reached condition is demanded once;
    /// false terminates with this diagnostic, rather than returning a value.
    | Require of condition: NodeId * diagnostic: string
    | TryWith of body: NodeId * handler: NodeId
    | TryFinally of body: NodeId * cleanup: NodeId
    | RecordExpr of fields: (string * NodeId) list * copyFrom: NodeId option
    | UnionCase of caseName: string * caseIndex: int * payload: NodeId option
    /// Extract tag from a DU value (returns i8 or i16 depending on case count)
    | DUGetTag of duValue: NodeId * duType: TypeIdentity
    /// Type-safe payload extraction via case eliminator (pointer bitcast + typed extraction)
    | DUEliminate of duValue: NodeId * caseIndex: int * caseName: string * payloadType: TypeIdentity
    /// Construct a DU value in the specified arena (or implicit arena if None)
    | DUConstruct of caseName: string * caseIndex: int * payload: NodeId option * arenaHint: NodeId option
    | TupleExpr of elements: NodeId list
    | ArrayExpr of elements: NodeId list
    /// Internal region-owned storage. Its source constructor owns initialization.
    | ArrayAllocate of count: NodeId
    | ListExpr of elements: NodeId list
    | FieldGet of expr: NodeId * fieldName: string
    /// Baker's read-only view; public String.toBytes remains a copying operation.
    | StringByteBorrow of source: NodeId
    | FieldSet of expr: NodeId * fieldName: string * value: NodeId
    | IndexGet of expr: NodeId * index: NodeId
    | IndexSet of expr: NodeId * index: NodeId * value: NodeId
    | NamedIndexedPropertySet of expr: NodeId * propName: string * index: NodeId * value: NodeId
    | TypeAnnotation of expr: NodeId * annotatedType: TypeIdentity
    | Upcast of expr: NodeId * targetType: TypeIdentity
    | Downcast of expr: NodeId * targetType: TypeIdentity
    | TypeTest of expr: NodeId * testType: TypeIdentity
    | AddressOf of expr: NodeId * isByref: bool
    | CellAddress of binding: NodeId
    | ElementAddress of buffer: NodeId * index: NodeId
    | FieldAddress of receiver: NodeId * field: string
    | Reborrow of reference: NodeId
    | Deref of expr: NodeId
    | Set of target: NodeId * value: NodeId
    | PlatformBinding of name: string
    | Intrinsic of info: IntrinsicInfo
    | TraitCall of memberName: string * constrainedTypes: TypeIdentity list * arg: NodeId
    | Quote of expr: NodeId * isTyped: bool
    | ObjectExpr of interfaceType: TypeIdentity * members: NodeId list
    | ModuleDef of name: string * members: NodeId list
    | TypeDef of name: string * kind: TypeDefKind * members: NodeId list
    | MemberDef of name: string * kind: MemberKind * body: NodeId option
    | InterpolatedString of parts: InterpolatedPart list
    | PatternBinding of name: string
    | LazyExpr of body: NodeId * captures: CaptureInfo list
    | LazyForce of lazyValue: NodeId
    /// Explicit shallow demand. Owning elaboration retains the activated
    /// frontier and sharing identity; this is not a recursive force operation.
    | EagerExpr of operand: NodeId
    /// Canonical explicit lazy value: code and the actual memoization instance
    /// remain separate. The environment never contains a function address.
    | LazyValue of thunk: NodeId * environment: NodeId
    /// Only computed=false and exact capture inputs are initialized here.
    /// The typed cached-result declaration has no initial value.
    | LazyEnvironment of owner: NodeId * initializers: (NodeId * NodeId) list
    /// Caller-owned raw storage. The constructor initializes computed/captures;
    /// allocation alone supplies neither initialization nor lifetime evidence.
    | LazyAllocate of owner: NodeId
    | LazyEnvironmentReference of lazyValue: NodeId
    | LazyRead of environment: NodeId * slot: NodeId
    | LazyBorrow of environment: NodeId * slot: NodeId
    | LazyWrite of environment: NodeId * slot: NodeId * value: NodeId
    | SeqExpr of body: NodeId * captures: CaptureInfo list
    | Yield of value: NodeId
    | YieldBang of seq: NodeId
    | TupleGet of tuple: NodeId * index: int
    | Error of message: string
    /// A proof obligation as a graph citizen. Its constraining structure is
    /// the source set of its hyperedge in F; it is never on the emission spine.
    | Obligation of ObligationInfo

/// Explicit demand is conditional on activation of this exact frontier.
/// These cases do not mark an enclosing deferred computation as a root.
[<RequireQualifiedAccess>]
type EagerFrontier =
    | Binding
    | Actual
    | Component
    | Expression
