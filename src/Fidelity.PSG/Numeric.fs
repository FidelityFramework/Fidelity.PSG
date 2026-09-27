namespace Fidelity.PSG

/// Exact source-real value, independent of the hosted floating-point approximation.
/// Construct through ExactRational.create to reduce the fraction and keep its denominator positive.
type ExactRational = {
    Numerator: bigint
    Denominator: bigint
}

/// Platform-resolved width dimensions — NTU-native vocabulary.
/// These are NOT named after C types. Farscape maps C types to these dimensions;
/// the NTU doesn't know or care about C.
///
/// A width dimension is a name the platform description declares
/// (ntu-dimensional-architecture.md §7.1); these two cases are the spellings the
/// language's own seals (`int`, `nativeint`) name, and `WidthDimension.name` is
/// the one place that spelling meets the declared name. `PlatformContext.Dimensions`
/// is keyed by the declared name, so a fabric binding may declare dimensions the
/// language has no spelling for.
[<RequireQualifiedAccess>]
type WidthDimension =
    /// Address width — the description's `Pointer` declaration
    | Pointer
    /// Machine register / natural computational word width — the description's `Register` declaration
    | Register

module WidthDimension =
    /// The name the platform description declares for this dimension.
    let name (dimension: WidthDimension) =
        match dimension with
        | WidthDimension.Pointer -> "Pointer"
        | WidthDimension.Register -> "Register"

/// How the width of a numeric type is determined.
[<RequireQualifiedAccess>]
type NTUWidth =
    /// Known at all times: 8, 16, 32, 64, 128 bits
    | Fixed of bits: int
    /// Platform-dependent, resolved by CCS at saturation via PlatformContext; Alex reads the result
    | Resolved of WidthDimension

/// The analysed range of an integer value (Dimensional_Range_Design.md §1; width-inference.md
/// §2, §3). The range is a coeffect beside the type (§0.1 item 7; Horizon_Requirements.md C3): the
/// width is derived from it on read and is never stored beside it. The forms:
///   `Bounded (lo, hi)`  a finite interval, the one form with a width;
///   `Above lo`, `Below hi`  a half-line: the working form the fixpoint's widening leaves when one
///                       endpoint keeps growing (§1.2), unobservable if it survives the narrowing;
///   `Unbounded`         no bound either way, unobservable (§1.3, CCS8011);
///   `Empty`             the join of no values at all, the least element: a record field no
///                       reachable expression constructs. Its width is the minimum, one bit.
/// The endpoints are exact integers (CS-11): arithmetic on analysed ranges never overflows (§0.1
/// item 6), so a product that leaves 64 bits is a bounded range the coverage check can name
/// (CCS8012, §4.2) rather than an unobservable one, and a declared representation's range (a
/// 64-bit unsigned unit's `[0, 2^64 - 1]`) is representable as declared. A half-line arises only
/// from the widening, never from arithmetic.
/// `Range`, `Width` and `Empty` are not spellings of the language (§0.1 items 1, 5): nothing in a
/// program names a width, and no value of this type is ever written by a program.
[<RequireQualifiedAccess>]
type ValueRange =
    | Empty
    | Bounded of lo: bigint * hi: bigint
    | Above of lo: bigint
    | Below of hi: bigint
    | Unbounded

/// Readings of a published range. These project the stored endpoints; none of them
/// analyses a program or selects a representation.
[<RequireQualifiedAccess>]
module ValueRange =

    /// An endpoint of the interval: finite, or the infinity a widening leaves.
    [<RequireQualifiedAccess>]
    type Endpoint =
        | NegInf
        | Finite of bigint
        | PosInf

    /// The endpoints of a non-empty range.
    let endpoints (r: ValueRange) : (Endpoint * Endpoint) option =
        match r with
        | ValueRange.Empty -> None
        | ValueRange.Bounded (lo, hi) -> Some (Endpoint.Finite lo, Endpoint.Finite hi)
        | ValueRange.Above lo -> Some (Endpoint.Finite lo, Endpoint.PosInf)
        | ValueRange.Below hi -> Some (Endpoint.NegInf, Endpoint.Finite hi)
        | ValueRange.Unbounded -> Some (Endpoint.NegInf, Endpoint.PosInf)


    /// Whether every value of the range is non-negative: the range spends no sign bit (§3).
    /// Vacuously true of the empty range.
    let isNonNegative (r: ValueRange) : bool =
        match r with
        | ValueRange.Empty -> true
        | ValueRange.Bounded (lo, _) | ValueRange.Above lo -> lo.Sign >= 0
        | ValueRange.Below _ | ValueRange.Unbounded -> false

/// NTU (Native Type Universe) type kinds.
/// Numeric types are parameterized by width — 3 kinds replace 16 discrete variants.
/// Type identity: NTUint(Fixed 32) ≠ NTUint(Resolved Register) even if same width on LP64.
[<RequireQualifiedAccess>]
type NTUKind =
    //-----------------------------------------------------------------------
    // Parameterized numeric types (width as dimension)
    //-----------------------------------------------------------------------

    /// Signed integer of any width
    /// Fixed 8/16/32/64 or Resolved Register/Pointer
    | NTUint of NTUWidth

    /// Unsigned integer of any width
    /// Fixed 8/16/32/64 or Resolved Register/Pointer
    | NTUuint of NTUWidth

    /// IEEE floating point of any width
    /// Fixed 32 or Fixed 64 (extensible to Fixed 128 for long double)
    | NTUfloat of NTUWidth

    //-----------------------------------------------------------------------
    // Pointer types (width = Pointer, implicit)
    //-----------------------------------------------------------------------

    /// Native pointer type (pointer-sized)
    | NTUptr

    /// Function pointer type (pointer-sized)
    /// Used for callbacks to top-level functions (no closures)
    | NTUfnptr

    /// Size type (unsigned, pointer-width) — array lengths, memory sizes
    | NTUsize

    /// Pointer difference type (signed, pointer-width)
    | NTUdiff

    //-----------------------------------------------------------------------
    // Special types
    //-----------------------------------------------------------------------

    /// UTF-8 encoded string (fat pointer: ptr + length)
    | NTUstring

    /// Boolean (1 byte)
    | NTUbool

    /// Unicode code point (UTF-32, 4 bytes)
    | NTUchar

    /// Unit type (zero-sized)
    | NTUunit

    /// Decimal (128-bit)
    | NTUdecimal

    /// Lazy computation (thunk with memoization)
    /// PRD-14: Foundation of the Lazy Stack
    | NTUlazy

    /// Sequence/generator (resumable computation producing values on demand)
    /// PRD-15: Simple Sequence Expressions
    | NTUseq

    //-----------------------------------------------------------------------
    // Collection types (PRD-13a: Core Collections)
    //-----------------------------------------------------------------------

    /// Mutable contiguous array (fat pointer: ptr + length)
    /// C-04: Type constructor arity = 1
    | NTUarray

    /// Bounded foreign storage, valid only during its declared mapping scope.
    /// The nominal schema selects its physical elements; it is not an array.
    | NTUborrowedview

    /// Immutable singly-linked list
    /// PRD-13a: Core Collections
    | NTUlist

    /// Immutable key-value map (balanced BST)
    /// PRD-13a: Core Collections
    | NTUmap

    /// Immutable set (balanced BST)
    /// PRD-13a: Core Collections
    | NTUset

    //-----------------------------------------------------------------------
    // Compound value types (platform-independent fixed size)
    //-----------------------------------------------------------------------

    /// UUID (128-bit, RFC 4122)
    /// Platform entropy source for generation (getrandom/BCryptGenRandom)
    | NTUuuid

    /// DateTime - ticks since epoch (64-bit)
    /// Platform clock resolution via quotations
    | NTUdatetime

    /// TimeSpan - duration in ticks (64-bit)
    | NTUtimespan

    //-----------------------------------------------------------------------
    // Posit numeric types (Gustafson Type III Unum)
    //-----------------------------------------------------------------------

    /// Posit number: tapered-precision floating point.
    /// Width determines storage size (8/16/32/64 bits).
    /// es = exponent field size (0-3), determines dynamic range vs precision tradeoff.
    /// Type identity: NTUposit(Fixed 32, 2) ≠ NTUfloat(Fixed 32) — different numeric semantics.
    /// CPU: software decode/encode or AVX-512 vectorized.
    /// FPGA: dedicated hardware pipeline via CIRCT (PACoGen-style).
    | NTUposit of NTUWidth * es: int

/// Memory space qualifier for substrate-aware type placement.
/// These do NOT affect type identity — `int @Global` and `int @Shared`
/// are the same NTU type with different placement. Qualifiers inform
/// code generation and BAREWire inter-substrate transfer strategy.
[<RequireQualifiedAccess>]
type NTUMemorySpace =
    /// Substrate chooses (escape analysis on CPU, compiler on GPU)
    | Default
    /// Function-local (universal concept across substrates)
    | Stack
    /// Main memory / VRAM / HBM
    | Global
    /// Explicitly managed cache (GPU shared mem, NPU tile mem)
    | Shared
    /// Per-thread/per-PE (GPU registers, NPU private mem)
    | Private
    /// HSA unified (CPU↔GPU↔NPU on Strix Halo — zero-copy)
    | Coherent
    /// Cross-device (FPGA BRAM from CPU perspective)
    | External
    /// MMIO (volatile access from BAREWire patterns)
    | Peripheral

/// Access pattern qualifier for cache-aware compilation.
/// Informs cache bypass strategy on CPU, coalescing on GPU,
/// and AXI stream vs memory-mapped on FPGA.
[<RequireQualifiedAccess>]
type NTUAccessPattern =
    /// Regular read/write
    | Normal
    /// Sequential, don't cache (non-temporal on CPU, coalesced on GPU)
    | Streaming
    /// MMIO / peripheral
    | Volatile
    /// Immutable view (enables sharing without coherency cost)
    | ReadOnly
    /// Producer-only (enables GPU write-combine)
    | WriteOnly

/// Bundle of placement qualifiers for substrate-aware compilation.
/// Attached to TypeLayout, not type identity.
type NTUQualifiers = {
    MemorySpace: NTUMemorySpace option
    AccessPattern: NTUAccessPattern option
}

/// One numeric representation the platform description declares (plan D8; the
/// `Representation` record of BAREWire's `Platform/Description.fs` and of the
/// Contracts twin, read structurally at saturation). Every tag is the declared
/// string; the range bounds are exact decimal text.
type NumericRepresentation = {
    Name: string
    /// "native" | "emulated" | "unavailable"
    Capability: string
    /// "int" | "uint" | "ieee" | "posit" | "fixed"
    Family: string
    Bits: int
    MinMagnitude: string
    MaxMagnitude: string
    /// "wrap" | "saturate" | "exact"
    Boundary: string
}

/// Runtime model — what execution environment services are available.
/// This is a capability coeffect: what the computation requires from
/// its environment. Comes from the platform binding's [platform] section.
/// See DTS+DMM paper Section 3.1.
[<RequireQualifiedAccess>]
type RuntimeModel =
    /// C library available (CPU console apps)
    | Libc
    /// Direct syscalls only, no libc (CPU standalone)
    | Freestanding
    /// No OS, hardware target (FPGA, MCU)
    | Bare
    /// AMD GPU runtime
    | ROCm
    /// AMD NPU runtime
    | XDNA

/// Compute substrate kind for multi-substrate compilation.
/// Each fidproj targets a single substrate; the fidsln orchestrates across them.
[<RequireQualifiedAccess>]
type SubstrateKind =
    /// CPU target (Zen 5, ARM, RISC-V) → MLIR → LLVM → native
    | CPU
    /// GPU target (RDNA 3.5, etc.) → MLIR → GPU/AMDGPU → ROCm
    | GPU
    /// NPU target (XDNA 2, etc.) → MLIR → MLIR-AIE → AI Engine runtime
    | NPU
    /// FPGA target (Xilinx, etc.) → MLIR → CIRCT → handshake → hw/comb/seq → SV
    | FPGA

/// The declared return bound of a platform endpoint (Dimensional_Range_Design.md,
/// ruling 2 of CS-12; BAREWire docs/11): the least value the return takes (`Floor`,
/// the errno floor on Linux) and the name of the parameter the return is at most
/// (`AtMost`, `"count"` for read and write). Read from the description's Contract
/// (`Floor`, `AtMost`) by PlatformResolution; the compiler holds no such number.
type ReturnBound = {
    Floor: bigint
    AtMost: string
}

