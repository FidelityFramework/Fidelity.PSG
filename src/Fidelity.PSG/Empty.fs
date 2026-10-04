namespace Fidelity.PSG

/// The published form of a program with nothing in it. A reader or a producer that
/// assembles a revision starts from these values and states only what it holds.
[<RequireQualifiedAccess>]
module Empty =

    let ordinary : OrdinaryDemandProjection =
        { Parameters = Map.empty; Calls = Map.empty; DeferredOnly = Set.empty; Inactivity = Map.empty }

    let callable : CallableEmissionProjection =
        { Branches = CallableBranchAuthority.empty
          Contracts = Map.empty; Carriers = Map.empty; Joins = Map.empty; Flows = Map.empty; MutableStorage = Map.empty
          AggregateSlots = Map.empty; AggregateValues = Map.empty; AggregateDependencies = Map.empty
          ValueShapes = Map.empty; SignatureData = Map.empty; Calls = Map.empty; Transports = Map.empty
          Declarations = Map.empty; Symbols = Map.empty; IntrinsicAliases = Set.empty
          DirectCallees = Map.empty; ForeignCalls = Set.empty; MutableRetentions = Set.empty
          ProgramInstances = Map.empty; VoidCallbacks = Set.empty; VoidPointers = Set.empty; NativeEntries = Map.empty
          FunctionBindings = Set.empty; DefinitionOnlyBindings = Set.empty; DefinitionOnlyLambdas = Set.empty
          Arguments = Map.empty; AliasTargets = Map.empty; TakesEnvironment = Set.empty
          UnitNodes = Set.empty; ClosedData = Set.empty; Supports = Map.empty }

    let programStorage : ProgramStorageInventory =
        { Entries = Map.empty; Reservations = Map.empty; Unresolved = Map.empty }

    let storage : StorageWitnessProjection =
        { Lazies = Map.empty; LazyOccurrences = Map.empty; LazyValues = Set.empty; DefinitionOnlyThunks = Set.empty
          LazyPrograms = Map.empty; Sequences = Map.empty; SequenceCopies = Map.empty; SequencePrograms = Map.empty
          Startup = None; SlotAuthorities = Set.empty; Requirements = Map.empty
          PatternRequirements = Map.empty; ProgramStorage = programStorage
          LiteralPoolAnchors = []; EnvironmentReservations = Map.empty; EnvironmentFactoryResults = Map.empty
          EnvironmentResidences = Map.empty; ProgramInitializationOrders = Map.empty }

    let boundary : BoundaryEmissionProjection =
        { Imports = Map.empty; ByScope = Map.empty; Calls = Map.empty; ByteViews = Map.empty
          StringExtents = Map.empty; IntrinsicWriteImports = Map.empty; IntrinsicWrites = Map.empty
          IntrinsicWriteProofs = Map.empty; DeclarationLeaves = Set.empty; DeclarationOnly = Set.empty
          Links = Set.empty }

    let numeric : NumericWitnessProjection =
        { Values = Map.empty; Operations = Map.empty; OperationRequired = Set.empty
          IndexTransports = Map.empty; Required = Set.empty; ResultSites = Set.empty
          Unresolved = Map.empty; SourceTypes = Map.empty; Layouts = Map.empty
          Elements = Map.empty; ElementTypes = Map.empty; DeclaredScalars = Map.empty
          OccurrenceRepresentations = Map.empty; TypeRepresentations = Map.empty }

    let memory : MemoryWitnessProjection =
        { Operations = Map.empty; ArrayCopies = Map.empty; Required = Set.empty; Unresolved = Map.empty }

    let spatial : SpatialModuleProjection =
        { Hardware = Map.empty; Kernels = Map.empty; Required = Set.empty
          MetadataOnly = Set.empty; ByScope = Map.empty; CodeRoots = Set.empty }

    let emission : WitnessEmissionProjection =
        { Ordinary = ordinary; Callable = callable; Storage = storage; Boundary = boundary
          Numeric = numeric; Memory = memory; Spatial = spatial }
