namespace Fidelity.PSG

/// Distinguishes type parameters from measure parameters and carrier parameters.
/// In Clef, measures work on ANY type (not just numerics like in .NET F#).
[<RequireQualifiedAccess>]
type TypeParamKind =
    /// Regular type parameter: 'T
    | Type
    /// Measure parameter: [<Measure>] 'u
    /// Measures on non-numeric types enable memory region tracking, access control, etc.
    | Measure
    /// Carrier parameter (design a.2): the numeric kind an operator scheme quantifies over,
    /// `κ` in `κ<'u> -> κ<'u> -> κ<'u>`. The carrier variable is the numeric constraint (c.1):
    /// it binds only to a numeric carrier, so a non-numeric operand fails to unify with it.
    | Carrier

/// Kind of byref
[<RequireQualifiedAccess>]
type ByrefKind =
    | In      // inref<T> - read-only
    | Out     // outref<T> - write-only
    | InOut   // byref<T> - read-write

/// The identity of a nominal declaration. Display names and declaration order do not
/// identify types; the checker admits one declaration at this module/name pair.
type NominalTypeIdentity = { Module: ModulePath; Name: string }

/// An immutable snapshot of constructor identity, including native kinds and argument sorts.
/// Layout/placement qualifiers are intentionally absent: they do not change type identity.
type ConstructorIdentity = {
    Declaration: NominalTypeIdentity
    Parameters: TypeParamKind list
    NativeKind: NTUKind option
}

[<RequireQualifiedAccess>]
type CarrierIdentity =
    | Constructor of ConstructorIdentity
    | Variable of TypeParamId * TypeParamKind

/// Stable map keys contain no inference cells. A later substitution produces a new key;
/// it cannot mutate the key already attached to a previous graph snapshot.
[<RequireQualifiedAccess>]
type TypeIdentity =
    | Application of ConstructorIdentity * TypeIdentity list
    | Numeric of CarrierIdentity * Dimension
    | Measure of Dimension
    | Variable of TypeParamId * TypeParamKind
    | Function of TypeIdentity * TypeIdentity
    | Tuple of bool * TypeIdentity list
    | AnonymousRecord of bool * (string * TypeIdentity) list
    | Union of ConstructorIdentity * (string * int * (string option * TypeIdentity) list) list
    | Forall of (TypeParamId * TypeParamKind) list * TypeIdentity
    | Byref of ByrefKind * TypeIdentity
    | NativePointer of TypeIdentity
    | Lazy of TypeIdentity
    | Sequence of TypeIdentity
    | Enumerator of TypeIdentity
    | List of TypeIdentity
    | Map of TypeIdentity * TypeIdentity
    | Set of TypeIdentity
    | Error of string

/// Literal value representation, typed by NTU.
/// Consolidates literal representation with the Native Type Universe.
/// The NTUKind specifies which numeric type (int8, int32, float64, etc.).
[<RequireQualifiedAccess>]
type NativeLiteral =
    /// Integer literal with NTU kind specifying width/signedness
    /// Covers: int8, uint8, int16, uint16, int32, uint32, int64, uint64, nativeint, unativeint
    | Int of value: int64 * kind: NTUKind
    /// Unsigned integer literal (for values > int64.MaxValue)
    | UInt of value: uint64 * kind: NTUKind
    /// Floating point literal with NTU kind (float32 or float64)
    | Float of value: float * kind: NTUKind
    /// String literal (UTF-8)
    | String of string
    /// Boolean literal
    | Bool of bool
    /// Character literal (UTF-32 code point)
    | Char of char
    /// Unit literal
    | Unit
    /// Decimal literal (128-bit)
    | Decimal of decimal
    /// Embedded byte array
    | ByteArray of byte[]
    /// Embedded uint16 array (for some string encodings)
    | UInt16Array of uint16[]

/// Information about a variable captured by a lambda (closure).
/// Capture analysis is performed during CCS type checking as part of scope resolution.
/// MLKit-style flat closures: immutable bindings captured by value, mutable by reference.
type CaptureInfo = {
    /// Name of the captured variable
    Name: string
    /// Type of the captured variable
    Type: TypeIdentity
    /// Whether the captured variable is mutable (determines ByRef vs ByValue capture)
    IsMutable: bool
    /// NodeId of the binding that defines this variable (for SSA lookup in Alex)
    SourceNodeId: NodeId option
}

/// Readings of a published type identity.
[<RequireQualifiedAccess>]
module TypeIdentity =
    /// Whether the identity is that of the unit type.
    let isUnit (identity: TypeIdentity) =
        match identity with
        | TypeIdentity.Application ({ NativeKind = Some NTUKind.NTUunit }, []) -> true
        | _ -> false
