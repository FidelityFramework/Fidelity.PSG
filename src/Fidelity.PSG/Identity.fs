namespace Fidelity.PSG

/// A position in source code (line, column)
[<Struct>]
type Position = { Line: int; Column: int }

/// A range in source code
[<Struct>]
type SourceRange = {
    File: string
    Start: Position
    End: Position
}

/// A path to a module (e.g., ["Alloy"; "Core"; "Memory"])
type ModulePath = string list

/// Identity of a node within one published revision. The producer assigns it;
/// a reader compares identities and never constructs one.
[<Struct>]
type NodeId = NodeId of int

module NodeId =
    /// The identity's number, for diagnostics and for value names derived from a node.
    let value (NodeId id) = id

/// Identity of a quantified type, measure or carrier parameter.
type TypeParamId = int
