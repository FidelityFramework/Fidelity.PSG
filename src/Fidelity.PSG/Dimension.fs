namespace Fidelity.PSG

/// A declared base measure, `[<Measure>] type m`. Identity is the declaration, module-qualified.
/// `Module` is the declaring module's path (the same shape as NativeTypes.ModulePath, spelled out
/// here so that this file precedes NativeTypes.fs with no dependency on it).
type BaseMeasure = { Name: string; Module: string list }

/// A measure inference variable. `_` mints an anonymous one, `'u` a named one.
/// Its kind is Measure: it is a type parameter of the measure sort and never of the type sort.
/// Identity is the `Id` and nothing else: equality, hashing and ordering exclude the name, so the
/// map keys, the lookup partition in `resolve` and the removal in `solveDim` all see one variable
/// however it is presented (design (b.4) step 4 renames survivors without changing their identity).
[<CustomEquality; CustomComparison>]
type MeasureVar =
    { Id: int; Name: string option }

    override this.Equals(other: obj) =
        match other with
        | :? MeasureVar as v -> this.Id = v.Id
        | _ -> false

    override this.GetHashCode() = this.Id

    interface System.IComparable with
        member this.CompareTo(other: obj) =
            match other with
            | :? MeasureVar as v -> compare this.Id v.Id
            | _ -> invalidArg "other" "MeasureVar compared with a value of another type"

/// A point of Z^B (+) Z^M in canonical form: no stored exponent is zero.
/// Both maps empty is the measure 1. Constructed only through `Dimension.mk`; no other code
/// builds this record, so structural equality is dimensional equality.
type Dimension = { Bases: Map<BaseMeasure, int>; Vars: Map<MeasureVar, int> }

