namespace Fidelity.PSG

/// Explicit resource bounds for one complete revision snapshot.
type BinaryLimits = {
    MaxBytes: int
    MaxCollectionLength: int
    MaxDepth: int
    MaxStringBytes: int
    MaxBigIntegerBytes: int
    MaxValues: int
}

/// Representation failures do not settle or repair the program represented.
[<RequireQualifiedAccess>]
type BinaryError =
    | InvalidLimits of field: string
    | LimitExceeded of limit: string * offset: int
    | Malformed of offset: int * reason: string
    | UnsupportedFormat of actual: uint32
    | SchemaMismatch of expected: int * actual: int
    | ContractMismatch
    | InvalidRevision of IntegrityViolation list
