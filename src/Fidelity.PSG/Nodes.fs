namespace Fidelity.PSG

/// An original array operand and its single immutable binding/reference.
/// Copy witnesses retain this same source-authored account.
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
    | LibraryExport     // Retained public source binding; grants no activation or ABI

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

/// Ports identify actual local source incidences, never runtime addresses.
[<RequireQualifiedAccess>]
type EvaluationPort =
    | Entry
    | OperandEntry of int
    | OperandExit of int
    | Ready
    | Exit
    | FailureExit

[<RequireQualifiedAccess>]
type EvaluationTransfer =
    | Continue
    | WhenTrue
    | WhenFalse
    | Resume
    /// The original shallow CaseElimination selects its actual ordinal.
    | WhenCase of int
    | WhenOtherCases of int list

[<RequireQualifiedAccess>]
type EvaluationAccess = Value | Storage

[<RequireQualifiedAccess>]
type EvaluationResidual =
    | MissingOperand | InvalidShape | MatchSelection | ExceptionFlow
    | CollectionIteration | CountedIteration | Delegation

/// A conversion alternative over opaque native results. Origin labels are
/// static source identities, never native pointer bits.
type ResourceConversionArm = {
    NativeNonNull: bool
    CaseOrdinal: int
    PayloadOrigin: NodeId option
}

type ResourceConversionModel = {
    Acquisition: NodeId
    Declaration: NodeId
    Import: NodeId
    OptionType: TypeIdentity
    HandleType: TypeIdentity
    Core: NodeId
    PointerBits: int
    SelectedPointerBits: int
    HandleBytes: int
    HandleAlignment: int
    TagBits: int
    TagBytes: int
    NoneCase: int
    SomeCase: int
    CaseCount: int
    PayloadOffset: int
    OptionBytes: int
    OptionAlignment: int
    Arms: ResourceConversionArm list
}

/// Finite source selection and native-choice plan. Formations are source
/// identities, never native addresses. Target realization remains separate.
[<RequireQualifiedAccess>]
type OptionalEntryPlanChoice = PendingAbsence | ClosedEntry

type OptionalEntryPlanArm = {
    CaseOrdinal: int
    Choice: OptionalEntryPlanChoice
    Formation: NodeId option
}

[<RequireQualifiedAccess>]
type OptionalEntryAbsencePlanChoice = AbsentEntry | RequiresClosedEntry

type OptionalEntryAbsencePlanArm = { CaseOrdinal: int; Choice: OptionalEntryAbsencePlanChoice }

/// Frozen projection of the selected project's parsed memory policy. Model is
/// diagnostic provenance; only Baker's admitted retirement grants allocation.
type ProjectMemoryPolicy = { ProjectPath: string; SourceVersion: string; Model: string }

/// One source-owned application instance retires after this exact receiver.
/// Uses includes the application, ordered immutable transports and receiver.
type CallableAggregateResultRetirement = {
    Application: NodeId
    Caller: NodeId
    Construction: NodeId
    Actual: NodeId
    Receiver: NodeId
    Policy: ProjectMemoryPolicy
    Uses: NodeId list
}

type OptionalEntryAbsenceArgumentConversionModel = {
    Call: NodeId
    Parameter: int
    Actual: NodeId
    Construction: NodeId
    SourceCase: int
    Absence: NodeId
    Arms: OptionalEntryAbsencePlanArm list
    ResultRetirement: CallableAggregateResultRetirement option
}

type OptionalEntryArgumentConversionModel = {
    Call: NodeId
    Parameter: int
    Actual: NodeId
    Construction: NodeId
    SourceCase: int
    Payload: NodeId
    Formation: NodeId
    Invocation: NodeId
    Arms: OptionalEntryPlanArm list
    ResultRetirement: CallableAggregateResultRetirement option
}

/// Observations of the existing evaluation owner's rows, not another flow
/// producer. Their complete ordered census is a current boundary premise.
[<RequireQualifiedAccess>]
type ResourceEvaluationRole =
    | Root
    | Operand of EvaluationAccess
    | Flow of EvaluationPort * EvaluationPort * EvaluationTransfer
    | Pending of EvaluationResidual

type ResourceEvaluationRelation = {
    Role: ResourceEvaluationRole
    Ordinal: int
    Sources: NodeId list
    Target: NodeId
}

[<RequireQualifiedAccess>]
type ResourceFlowEvent =
    | Acquisition
    | OptionAlias of source: NodeId
    | HandleAlias of source: NodeId
    | Payload of source: NodeId
    | Release of actual: NodeId * declaration: NodeId

type ResourceFlowPoint = {
    Label: int
    Site: NodeId
    /// Original operand ordinals from the retained root. Shared source nodes
    /// can be demanded at distinct occurrences without cross-connecting them.
    Context: int list
    Port: EvaluationPort
    Event: ResourceFlowEvent option
}

[<RequireQualifiedAccess>]
type ResourceFlowConnection = Local | OperandEntry | OperandExit

type ResourceFlowEdge = {
    From: int
    To: int
    Relation: int
    Connection: ResourceFlowConnection
    Transfer: EvaluationTransfer
}

type ResourceFlowCaseArm = {
    Ordinal: int option
    Body: NodeId
    BooleanResult: bool option
}

type ResourceFlowCase = {
    Site: NodeId
    Subject: NodeId
    Domain: int list
    Arms: ResourceFlowCaseArm list
}

/// One arbitrary path through the complete finite source contract. Unknown
/// feasibility/cycles are Pending; these stored events are not host pass flags.
type ResourceCleanupModel = {
    Acquisition: NodeId
    Declaration: NodeId
    Release: NodeId
    Conversion: NodeId
    ConversionModel: ResourceConversionModel
    Entry: int
    Points: ResourceFlowPoint list
    Relations: ResourceEvaluationRelation list
    Edges: ResourceFlowEdge list
    Cases: ResourceFlowCase list
    LiteralGuards: (NodeId * bool) list
    Exits: int list
}

/// Mathematical transcription of stored finite resource evidence. This owner
/// reads no program graph and supplies no resource or execution authority.
[<RequireQualifiedAccess>]
module ResourceProof =
    [<RequireQualifiedAccess>]
    type Sort = Boolean | Integer

    /// One typed logical vocabulary shared by SMT-LIB and passive dialect
    /// transcribers. No consumer parses strings or reconstructs this formula.
    [<RequireQualifiedAccess>]
    type Expr =
        | Boolean of bool
        | Integer of bigint
        | Variable of string
        | Not of Expr
        | And of Expr list
        | Or of Expr list
        | Implies of Expr * Expr
        | Equal of Expr * Expr
        | LessThan of Expr * Expr
        | LessOrEqual of Expr * Expr
        | Multiply of Expr * Expr
        | Modulo of Expr * Expr
        | Add of Expr list
        | IfThenElse of Expr * Expr * Expr

    type Projection = {
        Declarations: (string * Sort) list
        ParticipantRoles: (string * string) list
        Premises: Expr
        Conclusion: Expr
        Alternatives: Expr list
    }

    let private integer = Expr.Integer
    let private number (value: int) = integer (bigint value)
    let private node value = integer (bigint (NodeId.value value))
    let private boolean = Expr.Boolean
    let private andAlso = Expr.And
    let private orElse = Expr.Or
    let private equal left right = Expr.Equal(left, right)
    let private nonnegative value = Expr.LessOrEqual(number 0, number value)
    let private positive value = Expr.LessThan(number 0, number value)
    let private implies left right = Expr.Implies(left, right)
    let private notTerm = Expr.Not
    let private nonnullName = "resource_nonnull"
    let private nonnull = Expr.Variable nonnullName
    let private resourceCaseName = "resource_case"
    let private resourceCase = Expr.Variable resourceCaseName

    /// A single sort reader for both output transcribers. Ill-sorted or
    /// undeclared terms are refused rather than assigned a consumer default.
    let sortOf declarations expression =
        let variables = Map.ofList declarations
        let rec read = function
            | Expr.Boolean _ -> Ok Sort.Boolean
            | Expr.Integer _ -> Ok Sort.Integer
            | Expr.Variable name -> variables.TryFind name |> Option.map Ok |> Option.defaultValue (Error(sprintf "Resource proof variable '%s' is undeclared." name))
            | Expr.Not value -> require Sort.Boolean [value] Sort.Boolean
            | Expr.And values | Expr.Or values -> require Sort.Boolean values Sort.Boolean
            | Expr.Implies(left, right) -> require Sort.Boolean [left; right] Sort.Boolean
            | Expr.LessThan(left, right) | Expr.LessOrEqual(left, right) -> require Sort.Integer [left; right] Sort.Boolean
            | Expr.Multiply(left, right) | Expr.Modulo(left, right) -> require Sort.Integer [left; right] Sort.Integer
            | Expr.Add values -> require Sort.Integer values Sort.Integer
            | Expr.Equal(left, right) ->
                read left |> Result.bind (fun expected -> require expected [right] Sort.Boolean)
            | Expr.IfThenElse(condition, yes, no) ->
                require Sort.Boolean [condition] Sort.Boolean
                |> Result.bind (fun _ -> read yes)
                |> Result.bind (fun expected -> require expected [no] expected)
        and require expected values result =
            values |> List.fold (fun state value ->
                state |> Result.bind (fun _ -> read value |> Result.bind (fun actual ->
                    if actual = expected then Ok result else Error "Resource proof expression has incompatible logical sorts."))) (Ok result)
        if variables.Count <> declarations.Length then Error "Resource proof declarations are duplicated."
        else read expression

    let rec smtLib = function
        | Expr.Boolean true -> "true"
        | Expr.Boolean false -> "false"
        | Expr.Integer value when value.Sign < 0 -> sprintf "(- %O)" (-value)
        | Expr.Integer value -> string value
        | Expr.Variable name -> name
        | Expr.Not value -> sprintf "(not %s)" (smtLib value)
        | Expr.And [] -> "true"
        | Expr.Or [] -> "false"
        | Expr.And values -> sprintf "(and %s)" (values |> List.map smtLib |> String.concat " ")
        | Expr.Or values -> sprintf "(or %s)" (values |> List.map smtLib |> String.concat " ")
        | Expr.Add [] -> "0"
        | Expr.Add [value] -> smtLib value
        | Expr.Add values -> sprintf "(+ %s)" (values |> List.map smtLib |> String.concat " ")
        | Expr.Implies(left, right) -> sprintf "(=> %s %s)" (smtLib left) (smtLib right)
        | Expr.Equal(left, right) -> sprintf "(= %s %s)" (smtLib left) (smtLib right)
        | Expr.LessThan(left, right) -> sprintf "(< %s %s)" (smtLib left) (smtLib right)
        | Expr.LessOrEqual(left, right) -> sprintf "(<= %s %s)" (smtLib left) (smtLib right)
        | Expr.Multiply(left, right) -> sprintf "(* %s %s)" (smtLib left) (smtLib right)
        | Expr.Modulo(left, right) -> sprintf "(mod %s %s)" (smtLib left) (smtLib right)
        | Expr.IfThenElse(condition, yes, no) -> sprintf "(ite %s %s %s)" (smtLib condition) (smtLib yes) (smtLib no)

    let declarations projection =
        projection.Declarations |> List.map (fun (name, sort) ->
            sprintf "(declare-fun %s () %s)" name (match sort with Sort.Boolean -> "Bool" | Sort.Integer -> "Int"))

    let rec conjuncts = function
        | Expr.And [] -> [Expr.Boolean true]
        | Expr.And values -> values |> List.collect conjuncts
        | other -> [other]

    let rec freeVariables = function
        | Expr.Boolean _ | Expr.Integer _ -> Set.empty
        | Expr.Variable name -> Set.singleton name
        | Expr.Not value -> freeVariables value
        | Expr.And values | Expr.Or values | Expr.Add values -> values |> List.map freeVariables |> Set.unionMany
        | Expr.Implies(left, right) | Expr.Equal(left, right)
        | Expr.LessThan(left, right) | Expr.LessOrEqual(left, right)
        | Expr.Multiply(left, right) | Expr.Modulo(left, right) ->
            Set.union (freeVariables left) (freeVariables right)
        | Expr.IfThenElse(condition, yes, no) ->
            Set.unionMany [freeVariables condition; freeVariables yes; freeVariables no]

    let participantRoles (projection: Projection) =
        projection.ParticipantRoles

    let participantVariables (projection: Projection) =
        projection.ParticipantRoles
        |> List.map snd
        |> Set.ofList
        |> Set.toList
        |> List.sort

    let missingParticipantVariables (projection: Projection) =
        let premiseVars = freeVariables projection.Premises
        let conclusionVars = freeVariables projection.Conclusion
        participantVariables projection
        |> List.filter (fun name -> not (premiseVars.Contains name && conclusionVars.Contains name))

    let conversionParticipantRoles =
        [ "native_nonnull", nonnullName
          "case_ordinal", resourceCaseName
          "none_case", "resource_none_case"
          "some_case", "resource_some_case"
          "acquisition", "resource_acquisition_origin"
          "payload_origin", "resource_payload_origin"
          "payload_offset", "resource_payload_offset" ]

    let ofConversion (model: ResourceConversionModel) : Result<Projection, string> =
        let maximumTag = if model.TagBits >= 0 && model.TagBits <= 64 then (1I <<< model.TagBits) - 1I else -1I
        let caseValid ordinal = ordinal >= 0 && bigint ordinal <= maximumTag && ordinal < model.CaseCount
        if model.TagBits <= 0 || model.TagBits > 64 || model.TagBytes <= 0 || model.TagBits <> 8 * model.TagBytes then
            Error "The finite resource profile requires an established tag width of at most 64 bits."
        elif model.PointerBits <= 0 || model.PointerBits <> model.SelectedPointerBits || model.HandleBytes <= 0 || model.HandleAlignment <= 0 || model.PointerBits <> 8 * model.HandleBytes then
            Error "The finite resource profile requires positive handle bytes and alignment matching the selected pointer width."
        elif model.OptionBytes <= 0 || model.OptionAlignment <= 0 || model.OptionBytes % model.OptionAlignment <> 0 || model.OptionAlignment % model.HandleAlignment <> 0 then
            Error "The finite resource profile requires an aligned option layout."
        elif model.CaseCount <> 2 || model.NoneCase = model.SomeCase || not (caseValid model.NoneCase) || not (caseValid model.SomeCase) then
            Error "The finite resource profile requires distinct None and Some case ordinals within the two-case tag representation."
        else
            let noneCaseName = "resource_none_case"
            let noneCase = Expr.Variable noneCaseName
            let someCaseName = "resource_some_case"
            let someCase = Expr.Variable someCaseName
            let acquisitionOriginName = "resource_acquisition_origin"
            let acquisitionOrigin = Expr.Variable acquisitionOriginName
            let payloadOriginName = "resource_payload_origin"
            let payloadOrigin = Expr.Variable payloadOriginName
            let payloadOffsetName = "resource_payload_offset"
            let payloadOffset = Expr.Variable payloadOffsetName
            let armPremises = model.Arms |> List.map (fun arm ->
                let condition = if arm.NativeNonNull then nonnull else notTerm nonnull
                let originValue =
                    match arm.PayloadOrigin with
                    | Some origin -> node origin
                    | None -> number (if arm.NativeNonNull then -1 else 0)
                implies condition (andAlso [
                    equal resourceCase (number arm.CaseOrdinal)
                    equal payloadOrigin originValue ]))
            let premises =
                andAlso
                    (armPremises
                     @ [ equal noneCase (number model.NoneCase)
                         equal someCase (number model.SomeCase)
                         equal acquisitionOrigin (node model.Acquisition)
                         equal payloadOffset (number model.PayloadOffset) ])
            let alignmentClauses =
                if model.HandleAlignment = 1 then
                    []
                else
                    [ equal (Expr.Modulo(payloadOffset, number model.HandleAlignment)) (number 0) ]
            let conclusion =
                andAlso (
                    [
                        Expr.LessOrEqual(number 0, resourceCase)
                        Expr.LessOrEqual(resourceCase, integer maximumTag)
                        Expr.LessThan(resourceCase, number model.CaseCount)
                        equal resourceCase (Expr.IfThenElse(nonnull, someCase, noneCase))
                        equal payloadOrigin (Expr.IfThenElse(nonnull, acquisitionOrigin, number 0))
                        Expr.LessOrEqual(number model.TagBytes, payloadOffset)
                        Expr.LessOrEqual(Expr.Add [payloadOffset; number model.HandleBytes], number model.OptionBytes)
                    ]
                    @ alignmentClauses
                )
            Ok { Declarations =
                     [ nonnullName, Sort.Boolean
                       resourceCaseName, Sort.Integer
                       noneCaseName, Sort.Integer
                       someCaseName, Sort.Integer
                       acquisitionOriginName, Sort.Integer
                       payloadOriginName, Sort.Integer
                       payloadOffsetName, Sort.Integer ]
                 ParticipantRoles = conversionParticipantRoles
                 Premises = premises
                 Conclusion = conclusion
                 Alternatives = [notTerm nonnull; nonnull] }

    let ofCleanup (model: ResourceCleanupModel) : Result<Projection, string> =
        let points = model.Points |> List.map (fun point -> point.Label, point) |> Map.ofList
        let cases = model.Cases |> List.map (fun case -> case.Site, case) |> Map.ofList
        let literals = Map.ofList model.LiteralGuards
        let origins =
            model.Points |> List.choose (fun point -> point.Event |> Option.map (fun event -> point.Site, event))
            |> List.distinct |> Map.ofList
        let knownOrigins = origins |> Map.add model.Acquisition ResourceFlowEvent.Acquisition
        let originSites =
            knownOrigins
            |> Map.toList
            |> List.filter (fun (_, event) ->
                match event with
                | ResourceFlowEvent.Release _ -> false
                | _ -> true)
        let originSiteMap = Map.ofList originSites
        let invalid message = Error("The finite resource cleanup profile is incomplete: " + message)
        let relation index = model.Relations |> List.tryItem index
        let findOperand site ordinal =
            model.Relations |> List.choose (fun row ->
                match row.Role, row.Sources with
                | ResourceEvaluationRole.Operand EvaluationAccess.Value, [_; value]
                    when row.Target = site && row.Ordinal = ordinal -> Some value
                | _ -> None)
            |> function [value] -> Some value | _ -> None
        let siteOfOrigin = function
            | ResourceFlowEvent.OptionAlias source | ResourceFlowEvent.HandleAlias source
            | ResourceFlowEvent.Payload source | ResourceFlowEvent.Release(source, _) -> Some source
            | ResourceFlowEvent.Acquisition -> None
        let sourceKnown = knownOrigins |> Map.forall (fun _ event ->
            siteOfOrigin event |> Option.forall originSiteMap.ContainsKey)
        let rec hasOrigin seen site =
            if site = model.Acquisition then true
            elif Set.contains site seen then false
            else originSiteMap.TryFind site |> Option.bind siteOfOrigin
                 |> Option.exists (hasOrigin (Set.add site seen))
        // The source owner refuses ambiguous merges. This reader also refuses
        // a model that assigns different lineage events to one original site.
        let eventsConsistent =
            model.Points |> List.choose (fun point -> point.Event |> Option.map (fun event -> point.Site, event))
            |> List.groupBy fst |> List.forall (fun (_, events) -> events |> List.map snd |> List.distinct |> List.length = 1)
        let rec correlated seen site =
            if site = model.Acquisition then true
            elif Set.contains site seen then false
            else
                match knownOrigins.TryFind site with
                | Some(ResourceFlowEvent.OptionAlias source) -> correlated (Set.add site seen) source
                | _ -> false
        let caseShape (case: ResourceFlowCase) =
            correlated Set.empty case.Subject && not case.Arms.IsEmpty &&
            case.Domain.Length = (List.distinct case.Domain).Length &&
            (case.Domain |> List.sort) = ([model.ConversionModel.NoneCase; model.ConversionModel.SomeCase] |> List.sort) &&
            (case.Arms |> List.choose _.Ordinal |> List.forall (fun ordinal -> List.contains ordinal case.Domain)) &&
            (case.Arms |> List.choose _.Ordinal |> fun ordinals -> ordinals.Length = (List.distinct ordinals).Length) &&
            (case.Arms |> List.mapi (fun index arm -> arm.Ordinal.IsSome || index = case.Arms.Length - 1) |> List.forall id)
        let selectedCase (case: ResourceFlowCase) =
            model.ConversionModel.Arms |> List.map (fun arm ->
                let condition = if arm.NativeNonNull then nonnull else notTerm nonnull
                condition, number arm.CaseOrdinal)
        let caseIs (case: ResourceFlowCase) ordinal =
            selectedCase case |> List.map (fun (condition, value) -> andAlso [condition; equal value (number ordinal)]) |> orElse
        let caseArmCondition case index =
            let arm = case.Arms[index]
            match arm.Ordinal with
            | Some ordinal -> caseIs case ordinal
            | None ->
                case.Arms |> List.take index |> List.choose _.Ordinal
                |> List.map (caseIs case >> notTerm) |> andAlso
        let guard site =
            match literals.TryFind site, cases.TryFind site with
            | Some value, None -> Some(boolean value)
            | None, Some case when case.Arms |> List.forall (fun arm -> arm.BooleanResult.IsSome) ->
                case.Arms |> List.mapi (fun index arm -> andAlso [caseArmCondition case index; boolean arm.BooleanResult.Value]) |> orElse |> Some
            | _ -> None
        let transfer row transfer =
            match transfer with
            | EvaluationTransfer.Continue -> Some(boolean true)
            | EvaluationTransfer.WhenTrue | EvaluationTransfer.WhenFalse ->
                findOperand row.Target 0 |> Option.bind guard
                |> Option.map (fun expression -> if transfer = EvaluationTransfer.WhenTrue then expression else notTerm expression)
            | EvaluationTransfer.WhenCase ordinal -> cases.TryFind row.Target |> Option.map (fun case -> caseIs case ordinal)
            | EvaluationTransfer.WhenOtherCases ordinals ->
                cases.TryFind row.Target |> Option.map (fun case -> ordinals |> List.map (caseIs case >> notTerm) |> andAlso)
            | EvaluationTransfer.Resume -> None
        let transfers = model.Edges |> List.map (fun edge ->
            relation edge.Relation |> Option.bind (fun row ->
                match edge.Connection with
                | ResourceFlowConnection.Local -> transfer row edge.Transfer
                | _ -> Some(boolean true)))
        let unknownRows = model.Relations |> List.exists (fun row ->
            match row.Role with
            | ResourceEvaluationRole.Pending _ | ResourceEvaluationRole.Operand EvaluationAccess.Storage -> true
            | _ -> false)
        let acquisitionPoints = model.Points |> List.filter (fun point -> point.Event = Some ResourceFlowEvent.Acquisition)
        let failureExits = model.Points |> List.filter (fun point -> point.Port = EvaluationPort.FailureExit) |> List.map _.Label
        let roots = model.Relations |> List.filter (fun row -> row.Role = ResourceEvaluationRole.Root)
        let actualExits =
            failureExits @ (roots |> List.collect (fun row -> model.Points |> List.filter (fun point -> point.Site = row.Target && point.Context.IsEmpty && point.Port = EvaluationPort.Exit) |> List.map _.Label))
            |> List.distinct |> List.sort
        let exactPointCheck site context port label =
            match points.TryFind label with
            | Some point -> point.Site = site && point.Context = context && point.Port = port
            | None -> false
        let edgeCorrespondenceValid =
            model.Edges |> List.forall (fun edge ->
                match relation edge.Relation, points.TryFind edge.From, points.TryFind edge.To with
                | Some row, Some fromPoint, Some toPoint ->
                    match edge.Connection, row.Role, row.Sources with
                    | ResourceFlowConnection.Local, ResourceEvaluationRole.Flow(fromPort, toPort, actualTransfer), _ ->
                        exactPointCheck row.Target fromPoint.Context fromPort edge.From &&
                        exactPointCheck row.Target fromPoint.Context toPort edge.To &&
                        edge.Transfer = actualTransfer
                    | ResourceFlowConnection.OperandEntry, ResourceEvaluationRole.Operand EvaluationAccess.Value, [_; child] ->
                        exactPointCheck row.Target fromPoint.Context (EvaluationPort.OperandEntry row.Ordinal) edge.From &&
                        exactPointCheck child (fromPoint.Context @ [row.Ordinal]) EvaluationPort.Entry edge.To &&
                        edge.Transfer = EvaluationTransfer.Continue
                    | ResourceFlowConnection.OperandExit, ResourceEvaluationRole.Operand EvaluationAccess.Value, [_; child] ->
                        exactPointCheck child (toPoint.Context @ [row.Ordinal]) EvaluationPort.Exit edge.From &&
                        exactPointCheck row.Target toPoint.Context (EvaluationPort.OperandExit row.Ordinal) edge.To &&
                        edge.Transfer = EvaluationTransfer.Continue
                    | _ -> false
                | _ -> false)
        let occurrences = model.Points |> List.map (fun point -> point.Site, point.Context) |> List.distinct
        let relationCoverageValid =
            model.Relations |> List.mapi (fun relationIndex row ->
                match row.Role with
                | ResourceEvaluationRole.Root ->
                    row.Ordinal = 0 && exactPointCheck row.Target [] EvaluationPort.Entry model.Entry
                | ResourceEvaluationRole.Flow _ | ResourceEvaluationRole.Operand EvaluationAccess.Value ->
                    occurrences |> List.filter (fst >> (=) row.Target) |> List.forall (fun (_, context) ->
                        let connections = match row.Role with ResourceEvaluationRole.Flow _ -> [ResourceFlowConnection.Local] | _ -> [ResourceFlowConnection.OperandEntry; ResourceFlowConnection.OperandExit]
                        connections |> List.forall (fun connection ->
                            model.Edges |> List.filter (fun edge ->
                                edge.Relation = relationIndex && edge.Connection = connection &&
                                (if connection = ResourceFlowConnection.OperandExit then points[edge.To].Context else points[edge.From].Context) = context)
                            |> List.length = 1))
                | _ -> false) |> List.forall id
        let eventPortAndBindingValid =
            model.Points |> List.forall (fun point ->
                match point.Event with
                | None -> true
                | Some ResourceFlowEvent.Acquisition -> point.Port = EvaluationPort.Exit && point.Site = model.Acquisition
                | Some(ResourceFlowEvent.OptionAlias _) | Some(ResourceFlowEvent.Payload _) | Some(ResourceFlowEvent.HandleAlias _) ->
                    point.Port = EvaluationPort.Exit
                | Some(ResourceFlowEvent.Release(_, declaration)) ->
                    point.Port = EvaluationPort.Exit && declaration = model.Release)
        if points.Count <> model.Points.Length || not (points.ContainsKey model.Entry) || model.Points.IsEmpty then invalid "the evaluation point census is missing or duplicated."
        elif cases.Count <> model.Cases.Length || not (model.Cases |> List.forall caseShape) then invalid "an Option case is unknown, ambiguous or unrelated to this conversion."
        elif literals.Count <> model.LiteralGuards.Length then invalid "a guard has conflicting literal premises."
        elif not sourceKnown || not eventsConsistent || not (knownOrigins |> Map.forall (fun site event ->
            match event with ResourceFlowEvent.Release _ -> true | _ -> hasOrigin Set.empty site)) then invalid "handle lineage is missing or merged."
        elif unknownRows || transfers |> List.exists Option.isNone then invalid "an actual flow relation or guard is unresolved."
        elif model.Edges |> List.exists (fun edge -> not(points.ContainsKey edge.From && points.ContainsKey edge.To) || edge.From >= edge.To) then invalid "an endpoint is absent or evaluation is cyclic."
        elif model.Exits.IsEmpty || model.Exits |> List.exists (points.ContainsKey >> not) then invalid "the exit census is absent."
        elif model.Acquisition <> model.ConversionModel.Acquisition || model.Declaration <> model.ConversionModel.Declaration ||
             acquisitionPoints.Length <> 1 || roots.Length <> 1 ||
             actualExits <> (model.Exits |> List.distinct |> List.sort) ||
             model.Exits.Length <> (List.distinct model.Exits).Length ||
             (model.Edges |> List.exists (fun edge -> edge.To = model.Entry)) ||
             not edgeCorrespondenceValid || not relationCoverageValid || not eventPortAndBindingValid then
            invalid "the cleanup graph structure or event census is inconsistent."
        else
            ofConversion model.ConversionModel |> Result.map (fun conversion ->
                let reached label = Expr.Variable(sprintf "resource_reached_%d" label)
                let before label = Expr.Variable(sprintf "resource_live_before_%d" label)
                let after label = Expr.Variable(sprintf "resource_live_after_%d" label)
                let taken index = Expr.Variable(sprintf "resource_edge_%d" index)
                let origin site = Expr.Variable(sprintf "resource_origin_%d" (NodeId.value site))
                let incoming label = model.Edges |> List.mapi (fun index edge -> index, edge) |> List.filter (fun (_, edge) -> edge.To = label)
                let outgoing label = model.Edges |> List.mapi (fun index edge -> index, edge) |> List.filter (fun (_, edge) -> edge.From = label)
                let exactlyOne expressions =
                    expressions |> List.map (fun expression -> Expr.IfThenElse(expression, number 1, number 0))
                    |> Expr.Add |> fun sum -> equal sum (number 1)
                let originPremises = originSites |> List.choose (fun (site, event) ->
                    match event with
                    | ResourceFlowEvent.Acquisition -> Some(equal (origin site) (node site))
                    | ResourceFlowEvent.Release _ -> None
                    | _ -> siteOfOrigin event |> Option.map (fun source -> equal (origin site) (origin source)))
                let pathPremises = model.Points |> List.collect (fun point ->
                    let incoming = incoming point.Label |> List.map (fst >> taken)
                    let outgoing = outgoing point.Label |> List.map (fst >> taken)
                    let transition =
                        match point.Event with
                        | Some ResourceFlowEvent.Acquisition -> equal (after point.Label) nonnull
                        | Some(ResourceFlowEvent.Release _) -> equal (after point.Label) (boolean false)
                        | _ -> equal (after point.Label) (before point.Label)
                    [if point.Label = model.Entry then yield reached point.Label; yield notTerm (before point.Label)
                     else yield equal (reached point.Label) (orElse incoming)
                     yield implies (reached point.Label) (if List.contains point.Label model.Exits then notTerm(orElse outgoing) else exactlyOne outgoing)
                     if point.Label <> model.Entry then yield implies (reached point.Label) (exactlyOne incoming)
                     yield implies (reached point.Label) transition])
                let edgePremises = model.Edges |> List.mapi (fun index edge ->
                    implies (taken index) (andAlso [reached edge.From; reached edge.To; transfers[index].Value; equal (after edge.From) (before edge.To)]))
                let acquisitionReached = acquisitionPoints |> List.map (fun point -> reached point.Label) |> orElse
                let pointSafety = model.Points |> List.map (fun point ->
                    let baseSafety =
                        [ implies (before point.Label) nonnull
                          implies (after point.Label) nonnull ]
                        @ (if List.contains point.Label model.Exits then [notTerm (after point.Label)] else [])
                    let eventReq =
                        match point.Event with
                        | None | Some(ResourceFlowEvent.OptionAlias _) -> []
                        | Some ResourceFlowEvent.Acquisition -> [notTerm (before point.Label)]
                        | Some(ResourceFlowEvent.Payload source) | Some(ResourceFlowEvent.HandleAlias source) ->
                            [before point.Label; nonnull; equal (origin source) (node model.Acquisition); after point.Label]
                        | Some(ResourceFlowEvent.Release(actual, _)) ->
                            [before point.Label; equal (origin actual) (node model.Acquisition); notTerm (after point.Label)]
                    implies (reached point.Label) (andAlso (baseSafety @ eventReq)))
                let edgeSafety = model.Edges |> List.mapi (fun index edge ->
                    implies (taken index) (andAlso [implies (after edge.From) nonnull; implies (before edge.To) nonnull]))
                let originSafety = originSites |> List.map (fun (site, _) ->
                    implies nonnull (equal (origin site) (node model.Acquisition)))
                let conclusion =
                    (conversion.Conclusion :: pointSafety @ edgeSafety @ originSafety)
                    |> andAlso
                let declarations =
                    conversion.Declarations @ (model.Points |> List.collect (fun point ->
                        [sprintf "resource_reached_%d" point.Label, Sort.Boolean
                         sprintf "resource_live_before_%d" point.Label, Sort.Boolean
                         sprintf "resource_live_after_%d" point.Label, Sort.Boolean]))
                    @ (model.Edges |> List.mapi (fun index _ -> sprintf "resource_edge_%d" index, Sort.Boolean))
                    @ (originSites |> List.map (fun (site, _) -> sprintf "resource_origin_%d" (NodeId.value site), Sort.Integer))
                let participantRoles =
                    conversion.ParticipantRoles
                    @ (model.Points |> List.collect (fun point ->
                        [ sprintf "point_%d_reached" point.Label, sprintf "resource_reached_%d" point.Label
                          sprintf "point_%d_live_before" point.Label, sprintf "resource_live_before_%d" point.Label
                          sprintf "point_%d_live_after" point.Label, sprintf "resource_live_after_%d" point.Label ]))
                    @ (model.Edges |> List.mapi (fun index _ -> sprintf "edge_%d" index, sprintf "resource_edge_%d" index))
                    @ (originSites |> List.map (fun (site, _) -> sprintf "origin_%d" (NodeId.value site), sprintf "resource_origin_%d" (NodeId.value site)))
                { Declarations = declarations
                  ParticipantRoles = participantRoles
                  Premises = andAlso(conversion.Premises :: originPremises @ pathPremises @ edgePremises @ [acquisitionReached])
                  Conclusion = conclusion
                  Alternatives = conversion.Alternatives })

    /// Ordered probes retain the same claim anchor as an unused declaration,
    /// exactly as the existing conditional foreign-result premise probe.
    let anchoredPremisesQueries identity projection =
        projection.Alternatives |> List.map (fun alternative ->
            ["(set-logic QF_LIA)"] @ declarations projection @
            [sprintf "(assert %s)" (smtLib projection.Premises)
             sprintf "(assert %s)" (smtLib alternative)
             sprintf "(declare-fun %s () Bool)" identity
             "(check-sat)"] |> String.concat "\n")

    let anchoredNonVacuityQueries identity projection =
        let participants = participantVariables projection |> String.concat ", "
        conjuncts projection.Conclusion
        |> List.mapi (fun index clause ->
            let clauseText = smtLib clause
            let query =
                [ sprintf "; clause %d: %s" index clauseText
                  sprintf "; participants: %s" participants
                  "(set-logic QF_LIA)" ]
                @ declarations projection
                @ [ sprintf "(assert (not %s))" clauseText
                    sprintf "(declare-fun %s () Bool)" identity
                    "(check-sat)" ]
                |> String.concat "\n"
            index, clauseText, query)

    let anchoredNonVacuityQuery identity projection =
        ["(set-logic QF_LIA)"] @ declarations projection @
        [sprintf "(assert (not %s))" (smtLib projection.Conclusion)
         sprintf "(declare-fun %s () Bool)" identity
         "(check-sat)"] |> String.concat "\n"

    let refutation identity projection =
        declarations projection @
        [sprintf "(assert %s)" (smtLib projection.Premises)
         sprintf "(assert (= %s %s))" identity (smtLib projection.Conclusion)
         sprintf "(assert (not %s))" identity]

/// Finite source Option-to-choice correspondence, never a native address law.
/// The target pathway must independently realize the retained entry identity.
module OptionalEntryArgumentProof =
    /// The same finite conversion citizen binds its source-owned retirement
    /// and captured policy version. These constants grant no policy by parsing.
    let private withRetirement call actual construction retirement (projection:ResourceProof.Projection) : Result<ResourceProof.Projection, string> =
        match retirement with
        | None -> Ok projection
        | Some (row:CallableAggregateResultRetirement) ->
            let complete =
                row.Receiver=call && row.Actual=actual && row.Construction=construction &&
                row.Application<>row.Receiver && List.tryHead row.Uses=Some row.Application && List.tryLast row.Uses=Some row.Receiver &&
                List.contains row.Actual row.Uses && List.distinct row.Uses=row.Uses &&
                row.Policy.ProjectPath<>"" && row.Policy.SourceVersion<>"" && row.Policy.Model<>""
            if not complete then
                Error "The optional entry aggregate result retirement account is incomplete."
            else
                let integer value = ResourceProof.Expr.Integer value
                let number value = integer(bigint(NodeId.value value))
                let text (value:string) = value |> Seq.fold(fun total c->total*65537I+bigint(int c+1)) 0I |> integer
                let fields =
                    ["application",number row.Application;"caller",number row.Caller;"construction",number row.Construction
                     "actual",number row.Actual;"receiver",number row.Receiver
                     "policy_path",text row.Policy.ProjectPath;"policy_version",text row.Policy.SourceVersion;"policy_model",text row.Policy.Model] @
                    (row.Uses |> List.mapi(fun ordinal use' -> $"use_{ordinal}",number use'))
                let bindings = fields |> List.map(fun(name,value)->ResourceProof.Expr.Equal(ResourceProof.Expr.Variable("optional_retirement_"+name),value))
                let retirementBounds =
                    fields |> List.map(fun(name,value)->ResourceProof.Expr.LessOrEqual(value,ResourceProof.Expr.Variable("optional_retirement_"+name)))
                let retirementClause =
                    ResourceProof.Expr.Implies(
                        ResourceProof.Expr.And retirementBounds,
                        ResourceProof.Expr.Not(ResourceProof.Expr.Equal(ResourceProof.Expr.Variable "optional_retirement_application", ResourceProof.Expr.Variable "optional_retirement_receiver")))
                Ok { projection with
                        Declarations=projection.Declarations @ (fields |> List.map(fun(name,_)->"optional_retirement_"+name,ResourceProof.Sort.Integer))
                        ParticipantRoles=projection.ParticipantRoles @ (fields |> List.map(fun(name,_)->"retirement_"+name,"optional_retirement_"+name))
                        Premises=ResourceProof.Expr.And(projection.Premises::bindings)
                        Conclusion=ResourceProof.Expr.And [projection.Conclusion; retirementClause] }

    let project (model: OptionalEntryArgumentConversionModel) : Result<ResourceProof.Projection, string> =
        let number (value: int) = ResourceProof.Expr.Integer(bigint value)
        let equal left right = ResourceProof.Expr.Equal(left, right)
        let all values = ResourceProof.Expr.And values
        let sourceCase = ResourceProof.Expr.Variable "optional_entry_case"
        // This term denotes only an immutable source formation identity.
        let formation = ResourceProof.Expr.Variable "optional_entry_formation"
        let identity value = number (NodeId.value value)
        let selected = model.Arms |> List.map (fun arm ->
            ResourceProof.Expr.IfThenElse(equal sourceCase (number arm.CaseOrdinal), number 1, number 0))
        let armPremises = model.Arms |> List.map (fun arm ->
            let armFormation =
                match arm.Formation with
                | Some entry -> identity entry
                | None -> number 0
            ResourceProof.Expr.Implies(equal sourceCase (number arm.CaseOrdinal), equal formation armFormation))
        let arm0 = model.Arms |> List.tryFind (fun arm -> arm.CaseOrdinal = 0)
        let arm1 = model.Arms |> List.tryFind (fun arm -> arm.CaseOrdinal = 1)
        match model.Arms.Length, arm0, arm1 with
        | 2, Some { Choice = OptionalEntryPlanChoice.PendingAbsence; Formation = None }, Some { Choice = OptionalEntryPlanChoice.ClosedEntry; Formation = Some _ } ->
            withRetirement model.Call model.Actual model.Construction model.ResultRetirement {
                Declarations = ["optional_entry_case", ResourceProof.Sort.Integer; "optional_entry_formation", ResourceProof.Sort.Integer]
                ParticipantRoles = ["source_case", "optional_entry_case"; "formation", "optional_entry_formation"]
                Premises = all (equal sourceCase (number model.SourceCase) :: armPremises)
                Conclusion = all [
                    ResourceProof.Expr.LessOrEqual(number 1, sourceCase)
                    equal (ResourceProof.Expr.Add selected) (number 1)
                    equal formation (ResourceProof.Expr.IfThenElse(equal sourceCase (number 1), identity model.Formation, number 0))
                ]
                // Only Some is source-feasible in this tranche. Both table arms
                // remain mandatory in the conclusion; None grants no admission.
                Alternatives = [equal sourceCase (number 1)]
            }
        | _ -> Error "The optional entry conversion plan requires exact None and Some arms."


    /// Conditional finite source correspondence. The account-bound Boolean is
    /// an external binding hypothesis, never compiler-proved foreign behavior.
    let projectAbsence (model: OptionalEntryAbsenceArgumentConversionModel) : Result<ResourceProof.Projection, string> =
        let number (value: int) = ResourceProof.Expr.Integer(bigint value)
        let equal left right = ResourceProof.Expr.Equal(left, right)
        let all values = ResourceProof.Expr.And values
        let sourceCase = ResourceProof.Expr.Variable "optional_entry_absence_case"
        let choice = ResourceProof.Expr.Variable "optional_entry_absence_choice"
        let promiseName = sprintf "optional_entry_absence_accepted_%d" (NodeId.value model.Absence)
        let promise = ResourceProof.Expr.Variable promiseName
        let selected = model.Arms |> List.map (fun arm ->
            ResourceProof.Expr.IfThenElse(equal sourceCase (number arm.CaseOrdinal), number 1, number 0))
        let armPremises = model.Arms |> List.map (fun arm ->
            let armChoice =
                match arm.Choice with
                | OptionalEntryAbsencePlanChoice.AbsentEntry -> number 0
                | OptionalEntryAbsencePlanChoice.RequiresClosedEntry -> number 1
            ResourceProof.Expr.Implies(equal sourceCase (number arm.CaseOrdinal), equal choice armChoice))
        let arm0 = model.Arms |> List.tryFind (fun arm -> arm.CaseOrdinal = 0)
        let arm1 = model.Arms |> List.tryFind (fun arm -> arm.CaseOrdinal = 1)
        match model.Arms.Length, arm0, arm1 with
        | 2, Some { Choice = OptionalEntryAbsencePlanChoice.AbsentEntry }, Some { Choice = OptionalEntryAbsencePlanChoice.RequiresClosedEntry } ->
            withRetirement model.Call model.Actual model.Construction model.ResultRetirement {
                Declarations =
                    [ "optional_entry_absence_case", ResourceProof.Sort.Integer
                      "optional_entry_absence_choice", ResourceProof.Sort.Integer
                      promiseName, ResourceProof.Sort.Boolean ]
                ParticipantRoles =
                    [ "source_case", "optional_entry_absence_case"
                      "choice", "optional_entry_absence_choice"
                      "absence", promiseName ]
                Premises = all ([equal sourceCase (number model.SourceCase); promise] @ armPremises)
                Conclusion = all [
                    equal (ResourceProof.Expr.Add selected) (number 1)
                    equal choice (ResourceProof.Expr.IfThenElse(all [equal sourceCase (number 0); promise], number 0, number 1))
                ]
                Alternatives = [equal sourceCase (number 0)]
            }
        | _ -> Error "The optional entry absence conversion plan requires exact AbsentEntry and RequiresClosedEntry arms."

/// Arithmetic for a complete local snapshot whose copy and allocation use the
/// same source count. The producer supplies that incidence; this projection
/// neither discovers equality nor substitutes a range endpoint for the count.
module SnapshotBorrowProof =
    let participantRoles =
        [ "count", "snapshot_count"
          "snapshot", "snapshot_copy_extent"
          "copy", "snapshot_copy_extent"
          "allocation", "snapshot_allocation_capacity"
          "minimum", "snapshot_count"
          "maximum", "snapshot_count" ]

    let ofBounds (count: NodeId) (snapshot: NodeId) (copy: NodeId) (allocation: NodeId) minimum maximum elementBytes allocationCapacity : Result<ResourceProof.Projection, string> =
        if minimum < 0I || maximum < minimum then
            Error "A snapshot borrow requires a finite nonnegative count domain."
        elif elementBytes <= 0I || allocationCapacity < 0I then
            Error "A snapshot borrow requires positive element bytes and a nonnegative allocation capacity."
        elif ([count; snapshot; copy; allocation] |> Set.ofList |> Set.count) <> 4 then
            Error "A snapshot borrow requires distinct count, snapshot, copy and allocation participants."
        else
            let countVar = ResourceProof.Expr.Variable "snapshot_count"
            let copyExtentVar = ResourceProof.Expr.Variable "snapshot_copy_extent"
            let capacityVar = ResourceProof.Expr.Variable "snapshot_allocation_capacity"
            let lower = ResourceProof.Expr.Integer minimum
            let upper = ResourceProof.Expr.Integer maximum
            let zero = ResourceProof.Expr.Integer 0I
            let elemBytes = ResourceProof.Expr.Integer elementBytes
            let allocCap = ResourceProof.Expr.Integer allocationCapacity
            Ok {
                Declarations =
                    [ "snapshot_count", ResourceProof.Sort.Integer
                      "snapshot_copy_extent", ResourceProof.Sort.Integer
                      "snapshot_allocation_capacity", ResourceProof.Sort.Integer ]
                ParticipantRoles = participantRoles
                Premises =
                    ResourceProof.Expr.And
                        [ ResourceProof.Expr.LessOrEqual(lower, countVar)
                          ResourceProof.Expr.LessOrEqual(countVar, upper)
                          ResourceProof.Expr.Equal(copyExtentVar, ResourceProof.Expr.Multiply(countVar, elemBytes))
                          ResourceProof.Expr.Equal(capacityVar, allocCap) ]
                Conclusion =
                    ResourceProof.Expr.And
                        [ ResourceProof.Expr.LessOrEqual(zero, countVar)
                          ResourceProof.Expr.LessOrEqual(copyExtentVar, capacityVar) ]
                Alternatives = [ResourceProof.Expr.Boolean true]
            }

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

/// Source-declared external behavior. This is a hypothesis, never a proof of
/// foreign execution or a stable identity for a claim across incarnations.
[<RequireQualifiedAccess>]
type ForeignResultBound = Constant of bigint | Argument of int

[<RequireQualifiedAccess>]
type ForeignResultProofRole = LogicalCoverage | AbiNarrowing

type ForeignResultHypothesis = {
    Quote: NodeId
    Declaration: NodeId
    Identity: string
    Version: string
    Source: string
    Lower: ForeignResultBound
    Upper: ForeignResultBound
}

type ForeignResultArgument = { Index: int; Node: NodeId; Enclosure: ValueRange }

type ForeignResultApplication = {
    Declaration: NodeId
    Call: NodeId
    /// Existing ordered source-call coordinate, not a set or a durable anchor.
    Context: NodeId list
    /// None retains a missing contract; it supplies no behavioral default.
    Hypothesis: ForeignResultHypothesis option
    Arguments: ForeignResultArgument list
}

type ForeignResultCoverageModel = {
    Application: ForeignResultApplication
    Role: ForeignResultProofRole
    ResultRange: ValueRange
    Destination: ValueRange
    DestinationDeclaration: NodeId option
    Abi: NodeId option
    /// Selected target ABI enclosure, independent of the behavior hypothesis.
    AbiRange: ValueRange
    /// Source-issued premise provenance. Absence permits a fresh check but
    /// cannot authorize retaining code that consumed a prior discharge.
    AbiIdentity: string option
    DestinationIdentity: string option
}

/// One mathematical transcription of the stored conditional coverage model.
/// Formatting backends consume this predicate; none discovers a program range.
[<RequireQualifiedAccess>]
module ForeignResultCoverage =
    [<RequireQualifiedAccess>]
    type Term =
        | Constant of bigint
        | Argument of int
        | Result
        | HypothesisLower
        | HypothesisUpper
        | AbiLower
        | AbiUpper
        | ResultLower
        | ResultUpper
        | DestinationLower
        | DestinationUpper

    [<RequireQualifiedAccess>]
    type Predicate =
        | LessOrEqual of Term * Term
        | And of Predicate list
        | Implies of Predicate * Predicate

    type Projection =
        {
            Arguments: int list
            ParticipantRoles: (string * string) list
            Premises: Predicate
            Totality: Predicate
            Claim: Predicate
            Conclusion: Predicate
        }

    let argumentName index = sprintf "foreign_arg_%d" index

    let baseParticipantRoles =
        [
            "hypothesis_lower", "foreign_hypothesis_lower"
            "hypothesis_upper", "foreign_hypothesis_upper"
            "abi_lower", "foreign_abi_lower"
            "abi_upper", "foreign_abi_upper"
            "result_lower", "foreign_result_lower"
            "result_upper", "foreign_result_upper"
            "destination_lower", "foreign_destination_lower"
            "destination_upper", "foreign_destination_upper"
            "result", "foreign_result"
        ]

    let private equalTerm left right =
        Predicate.And
            [
                Predicate.LessOrEqual(left, right)
                Predicate.LessOrEqual(right, left)
            ]

    let private enclosure term =
        function
        | ValueRange.Empty ->
            Ok(
                Predicate.And
                    [
                        Predicate.LessOrEqual(Term.Constant 1I, term)
                        Predicate.LessOrEqual(term, Term.Constant 0I)
                    ]
            )
        | ValueRange.Bounded(lower, upper) ->
            Ok(
                Predicate.And
                    [
                        Predicate.LessOrEqual(Term.Constant lower, term)
                        Predicate.LessOrEqual(term, Term.Constant upper)
                    ]
            )
        | _ -> Error "Foreign result coverage has no established finite enclosure"

    let private rangeEndpoints lowerTerm upperTerm =
        function
        | ValueRange.Empty ->
            Ok(
                Predicate.And
                    [
                        equalTerm lowerTerm (Term.Constant 1I)
                        equalTerm upperTerm (Term.Constant 0I)
                    ]
            )
        | ValueRange.Bounded(lower, upper) ->
            Ok(
                Predicate.And
                    [
                        equalTerm lowerTerm (Term.Constant lower)
                        equalTerm upperTerm (Term.Constant upper)
                    ]
            )
        | _ -> Error "Foreign result coverage has no established finite enclosure"

    let private abiEndpoints =
        function
        | ValueRange.Bounded(lower, upper) when lower <= upper ->
            Ok(
                Predicate.And
                    [
                        equalTerm Term.AbiLower (Term.Constant lower)
                        equalTerm Term.AbiUpper (Term.Constant upper)
                    ]
            )
        | ValueRange.Bounded _ -> Error "Foreign result coverage has an empty ABI enclosure"
        | _ -> Error "Foreign result coverage has no established finite ABI enclosure"

    /// Pointer and other irrelevant actuals stay in Application provenance but
    /// are not invented as integer variables. Only endpoint actuals enter D.
    let project lower upper arguments resultRange destination abiRange =
        let bound =
            function
            | ForeignResultBound.Constant value -> Term.Constant value
            | ForeignResultBound.Argument index -> Term.Argument index

        let required =
            [ lower; upper ]
            |> List.choose (function
                | ForeignResultBound.Argument index -> Some index
                | _ -> None)
            |> List.distinct
            |> List.sort

        let actuals = Map.ofList arguments

        let domains =
            required
            |> List.map (fun index ->
                match actuals.TryFind index with
                | Some range -> enclosure (Term.Argument index) range
                | None -> Error(sprintf "Foreign result hypothesis names absent argument %d" index))
            |> List.fold
                (fun state item ->
                    state
                    |> Result.bind (fun held -> item |> Result.map (fun value -> value :: held)))
                (Ok [])
            |> Result.map List.rev

        if actuals.Count <> List.length arguments then
            Error "Foreign result actual argument indices are duplicated"
        else
            domains
            |> Result.bind (fun domains ->
                abiEndpoints abiRange
                |> Result.bind (fun abi ->
                    rangeEndpoints Term.ResultLower Term.ResultUpper resultRange
                    |> Result.bind (fun resultEndpoints ->
                        rangeEndpoints Term.DestinationLower Term.DestinationUpper destination
                        |> Result.map (fun destinationEndpoints ->
                            let domain = Predicate.And domains

                            let endpoints =
                                Predicate.And
                                    [
                                        equalTerm Term.HypothesisLower (bound lower)
                                        equalTerm Term.HypothesisUpper (bound upper)
                                        abi
                                        resultEndpoints
                                        destinationEndpoints
                                    ]

                            let resultBounds =
                                Predicate.And
                                    [
                                        Predicate.LessOrEqual(bound lower, Term.Result)
                                        Predicate.LessOrEqual(Term.Result, bound upper)
                                        Predicate.LessOrEqual(Term.HypothesisLower, Term.Result)
                                        Predicate.LessOrEqual(Term.Result, Term.HypothesisUpper)
                                        Predicate.LessOrEqual(Term.AbiLower, Term.Result)
                                        Predicate.LessOrEqual(Term.Result, Term.AbiUpper)
                                    ]

                            let premises = Predicate.And [ domain; endpoints; resultBounds ]
                            // This must hold for every actual tuple in D. A single
                            // feasible tuple cannot hide a contradictory interval.
                            let argumentTotality =
                                [
                                    match lower with
                                    | ForeignResultBound.Argument index ->
                                        yield Predicate.LessOrEqual(Term.Argument index, Term.HypothesisUpper)
                                    | _ -> ()
                                    match upper with
                                    | ForeignResultBound.Argument index ->
                                        yield Predicate.LessOrEqual(Term.HypothesisLower, Term.Argument index)
                                    | _ -> ()
                                ]

                            let totality =
                                Predicate.And(
                                    [
                                        Predicate.LessOrEqual(Term.HypothesisLower, Term.HypothesisUpper)
                                        Predicate.LessOrEqual(Term.HypothesisLower, Term.AbiUpper)
                                        Predicate.LessOrEqual(Term.AbiLower, Term.HypothesisUpper)
                                    ]
                                    @ argumentTotality
                                )

                            let claim =
                                Predicate.And
                                    [
                                        Predicate.LessOrEqual(Term.ResultLower, Term.Result)
                                        Predicate.LessOrEqual(Term.Result, Term.ResultUpper)
                                        Predicate.LessOrEqual(Term.DestinationLower, Term.Result)
                                        Predicate.LessOrEqual(Term.Result, Term.DestinationUpper)
                                    ]

                            let participantRoles =
                                (required |> List.map (fun index -> sprintf "argument_%d" index, argumentName index))
                                @ baseParticipantRoles

                            {
                                Arguments = required
                                ParticipantRoles = participantRoles
                                Premises = premises
                                Totality = totality
                                Claim = claim
                                Conclusion = Predicate.And [ totality; claim ]
                            }))))

    let ofModel model =
        match model.Application.Hypothesis with
        | None -> Error "Foreign result behavior contract is missing"
        | Some _ when model.Abi.IsNone -> Error "Foreign result coverage has no actual ABI premise"
        | Some hypothesis ->
            project
                hypothesis.Lower
                hypothesis.Upper
                (model.Application.Arguments
                 |> List.map (fun actual -> actual.Index, actual.Enclosure))
                model.ResultRange
                model.Destination
                model.AbiRange

    let termName =
        function
        | Term.Constant value when value.Sign < 0 -> sprintf "(- %O)" (-value)
        | Term.Constant value -> string value
        | Term.Argument index -> argumentName index
        | Term.Result -> "foreign_result"
        | Term.HypothesisLower -> "foreign_hypothesis_lower"
        | Term.HypothesisUpper -> "foreign_hypothesis_upper"
        | Term.AbiLower -> "foreign_abi_lower"
        | Term.AbiUpper -> "foreign_abi_upper"
        | Term.ResultLower -> "foreign_result_lower"
        | Term.ResultUpper -> "foreign_result_upper"
        | Term.DestinationLower -> "foreign_destination_lower"
        | Term.DestinationUpper -> "foreign_destination_upper"

    let declaredTerms projection =
        (projection.Arguments |> List.map Term.Argument)
        @ [
            Term.HypothesisLower
            Term.HypothesisUpper
            Term.AbiLower
            Term.AbiUpper
            Term.ResultLower
            Term.ResultUpper
            Term.DestinationLower
            Term.DestinationUpper
            Term.Result
        ]

    let rec smtLib =
        function
        | Predicate.LessOrEqual(left, right) -> sprintf "(<= %s %s)" (termName left) (termName right)
        | Predicate.And [] -> "true"
        | Predicate.And predicates -> predicates |> List.map smtLib |> String.concat " " |> sprintf "(and %s)"
        | Predicate.Implies(premise, conclusion) -> sprintf "(=> %s %s)" (smtLib premise) (smtLib conclusion)

    let declarations projection =
        declaredTerms projection
        |> List.map (fun item -> sprintf "(declare-fun %s () Int)" (termName item))

    let refutationPremises projection =
        match projection.Premises with
        | Predicate.And [ domain; endpoints; resultBounds ] ->
            Predicate.And [ domain; endpoints; Predicate.Implies(projection.Totality, resultBounds) ]
        | premises -> premises

    let refutation identity projection =
        declarations projection
        @ [
            sprintf "(assert %s)" (smtLib (refutationPremises projection))
            sprintf "(assert (= %s %s))" identity (smtLib projection.Conclusion)
            sprintf "(assert (not %s))" identity
        ]

    let premisesQuery projection =
        [ "(set-logic QF_LIA)" ]
        @ declarations projection
        @ [ sprintf "(assert %s)" (smtLib projection.Premises); "(check-sat)" ]
        |> String.concat "\n"

    /// The unused Boolean declaration binds a query to its claim inventory; it
    /// contributes no assumption to the integer premise-satisfiability check.
    let anchoredPremisesQuery identity projection =
        premisesQuery projection
        |> fun query -> query.Replace("(check-sat)", sprintf "(declare-fun %s () Bool)\n(check-sat)" identity)

    let rec conjuncts =
        function
        | Predicate.And [] -> []
        | Predicate.And predicates -> predicates |> List.collect conjuncts
        | other -> [ other ]

    let private termVariables =
        function
        | Term.Constant _ -> Set.empty
        | variable -> Set.singleton (termName variable)

    let rec freeVariables =
        function
        | Predicate.LessOrEqual(left, right) -> Set.union (termVariables left) (termVariables right)
        | Predicate.And predicates -> predicates |> List.map freeVariables |> Set.unionMany
        | Predicate.Implies(premise, conclusion) -> Set.union (freeVariables premise) (freeVariables conclusion)

    let participantRoles projection =
        projection.ParticipantRoles

    let participantVariables projection =
        projection.ParticipantRoles
        |> List.map snd
        |> Set.ofList
        |> Set.toList
        |> List.sort

    let missingParticipantVariables projection =
        let premiseVars = freeVariables projection.Premises
        let conclusionVars = freeVariables projection.Conclusion
        let totalityVars = freeVariables projection.Totality
        let claimVars = freeVariables projection.Claim
        let totalityRequired =
            Set.ofList (
                (projection.Arguments |> List.map argumentName)
                @ [
                    "foreign_hypothesis_lower"
                    "foreign_hypothesis_upper"
                    "foreign_abi_lower"
                    "foreign_abi_upper"
                ]
            )
        let claimRequired =
            Set.ofList
                [
                    "foreign_result_lower"
                    "foreign_result_upper"
                    "foreign_destination_lower"
                    "foreign_destination_upper"
                    "foreign_result"
                ]
        participantVariables projection
        |> List.filter (fun name ->
            not (premiseVars.Contains name && conclusionVars.Contains name)
            || (totalityRequired.Contains name && not (totalityVars.Contains name))
            || (claimRequired.Contains name && not (claimVars.Contains name)))

    let anchoredNonVacuityQueries identity projection =
        let participants = participantVariables projection |> String.concat ", "
        conjuncts projection.Conclusion
        |> List.mapi (fun index clause ->
            let clauseText = smtLib clause
            let query =
                [ sprintf "; clause %d: %s" index clauseText
                  sprintf "; participants: %s" participants
                  "(set-logic QF_LIA)" ]
                @ declarations projection
                @ [ sprintf "(assert (not %s))" clauseText
                    sprintf "(declare-fun %s () Bool)" identity
                    "(check-sat)" ]
                |> String.concat "\n"
            index, clauseText, query)

    let nonVacuityQuery projection =
        [ "(set-logic QF_LIA)" ]
        @ declarations projection
        @ [ sprintf "(assert (not %s))" (smtLib projection.Conclusion); "(check-sat)" ]
        |> String.concat "\n"

    let anchoredNonVacuityQuery identity projection =
        nonVacuityQuery projection
        |> fun query -> query.Replace("(check-sat)", sprintf "(declare-fun %s () Bool)\n(check-sat)" identity)

/// Current source incidence and existing ledger citizens. Pending evidence is
/// distinguishable from established incidence, neither is a solver discharge.
type ForeignResultUse = {
    Application: ForeignResultApplication
    Participants: ParticipantEvidence
    Claims: (ForeignResultProofRole * NodeId) list
}

/// Model for zero-copy explicit-count read-only buffer extent bounds.
type ZeroCopyBufferExtentModel = {
    Call: NodeId
    Declaration: NodeId
    Parameter: int
    CountParameter: int
    Buffer: NodeId
    Count: NodeId
    MinimumCount: bigint
    MaximumCount: bigint
    ExtentCapacity: bigint
    ElementBytes: int
    CountCoverage: NodeId
}

/// Retention discipline for a borrowed read-only buffer crossing.
[<RequireQualifiedAccess>]
type BufferRetentionMode =
    | DuringCall
    | RetainedUntilOwner of ownerParameter: int * releaseOrdinal: int

/// Model proving storage residence dominates all retained foreign accesses until retirement.
type BufferRetentionDominationModel = {
    Call: NodeId
    Declaration: NodeId
    Buffer: NodeId
    Residence: NodeId
    Mode: BufferRetentionMode
    AcquireOrder: int
    RetirementOrders: int list
}

/// Crossing realization mode for a legacy uncounted NUL-terminated foreign path.
[<RequireQualifiedAccess>]
type UncountedPathStagingMode =
    | StaticImageZeroCopy of poolEntry: int
    | CallScopedStaged of stagingBuffer: NodeId * capacity: int

/// Model proving zero interior 0x00 bytes and trailing 0x00 at byte length.
type UncountedPathTerminationModel = {
    Call: NodeId
    Declaration: NodeId
    Parameter: int
    Source: NodeId
    Mode: UncountedPathStagingMode
    ByteLength: bigint
    RequiresNoInteriorNul: bool
    RequiresTrailingNul: bool
}

/// Model proving non-owning borrowed result views respect NULL->None at the boundary
/// and every read occurs before owner invalidation or companion measurement.
type BorrowedResultViewScopeModel = {
    Call: NodeId
    Declaration: NodeId
    Owner: NodeId
    View: NodeId
    CallOrder: int
    InvalidationOrders: int list
    ReadOrders: int list
    NullToNoneBoundary: bool
}

/// Foreign choice of one Option<'Buffer> arm strictly at the call boundary.
[<RequireQualifiedAccess>]
type BufferAbsencePlanChoice =
    | AbsentNull
    | RequiresNonNullBuffer

/// One arm of an immutable Option<'Buffer> absence conversion plan.
type BufferAbsencePlanArm = {
    CaseOrdinal: int
    Choice: BufferAbsencePlanChoice
}

/// Model converting interior Option<'Buffer> (`None -> 0` strictly at call boundary).
type BufferAbsenceArgumentConversionModel = {
    Call: NodeId
    Parameter: int
    Actual: NodeId
    Construction: NodeId
    SourceCase: int
    Absence: NodeId
    Arms: BufferAbsencePlanArm list
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
    /// Source-checked count/allocation incidence plus nonnegativity of that
    /// actual count over its finite domain. Arithmetic alone does not establish
    /// the incidence; bounds never stand for actual executed extents.
    | SnapshotBorrowBound of count: NodeId * snapshot: NodeId * copy: NodeId * allocation: NodeId * minimum: bigint * maximum: bigint * elementBytes: bigint * allocationCapacity: bigint
    /// For any successful read of r bytes, 1 <= r <= capacity, the trimmed copy
    /// of r - 1 bytes is within bound.
    | InputCopyBound of capacity: int64 * bound: int64
    | FiniteLinearRecurrence of FiniteLinearRecurrenceModel
    /// Every prefix of finitely many signed additive effects. Source evidence
    /// separately binds each (maximum executions, exact delta) contribution to
    /// current typed stores and actual memoization-instance activation counts.
    | FiniteAdditiveEffects of initial: bigint * contributions: (bigint * bigint) list * lower: bigint * upper: bigint
    /// Conditional coverage under the external execution hypothesis. Unknown
    /// inputs retain the claim but cannot supply a discharged projection.
    | ForeignResultCoverage of ForeignResultCoverageModel
    | ResourceConversion of ResourceConversionModel
    | ResourceCleanup of ResourceCleanupModel
    /// An admitted unresolved requirement remains in the ledger, with no solver
    /// term or discharge. Publication and artifact readiness are separate gates.
    | Pending of reasons: string list
    /// Source-plan correspondence only; the target artifact must realize it.
    | OptionalEntryArgumentConversion of OptionalEntryArgumentConversionModel
    | OptionalEntryAbsenceArgumentConversion of OptionalEntryAbsenceArgumentConversionModel
    /// Zero-copy read-only buffer, uncounted path, borrowed result view, and buffer absence models.
    | ZeroCopyBufferExtent of ZeroCopyBufferExtentModel
    | BufferRetentionDomination of BufferRetentionDominationModel
    | UncountedPathTermination of UncountedPathTerminationModel
    | BorrowedResultViewScope of BorrowedResultViewScopeModel
    | BufferAbsenceArgumentConversion of BufferAbsenceArgumentConversionModel

[<RequireQualifiedAccess>]
module ObligationBody =
    /// Published participant roles named by an obligation body and the
    /// formula variables that carry each role in its proof projection.
    let participantRoles = function
        | ObligationBody.SnapshotBorrowBound _ ->
            SnapshotBorrowProof.participantRoles
        | ObligationBody.ResourceConversion model ->
            match ResourceProof.ofConversion model with
            | Ok projection -> projection.ParticipantRoles
            | Error _ -> ResourceProof.conversionParticipantRoles
        | ObligationBody.ResourceCleanup model ->
            match ResourceProof.ofCleanup model with
            | Ok projection -> projection.ParticipantRoles
            | Error _ -> ResourceProof.conversionParticipantRoles
        | ObligationBody.OptionalEntryArgumentConversion model ->
            match OptionalEntryArgumentProof.project model with
            | Ok projection -> projection.ParticipantRoles
            | Error _ -> [ "source_case", "optional_entry_case"; "formation", "optional_entry_formation" ]
        | ObligationBody.OptionalEntryAbsenceArgumentConversion model ->
            match OptionalEntryArgumentProof.projectAbsence model with
            | Ok projection -> projection.ParticipantRoles
            | Error _ ->
                [ "source_case", "optional_entry_absence_case"
                  "choice", "optional_entry_absence_choice"
                  "absence", sprintf "optional_entry_absence_accepted_%d" (NodeId.value model.Absence) ]
        | ObligationBody.ForeignResultCoverage model ->
            match ForeignResultCoverage.ofModel model with
            | Ok projection -> projection.ParticipantRoles
            | Error _ -> ForeignResultCoverage.baseParticipantRoles
        | _ -> []

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
