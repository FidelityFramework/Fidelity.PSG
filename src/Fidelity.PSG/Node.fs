namespace Fidelity.PSG

/// A node of a published revision. Every field is a settled value: the type is a
/// frozen identity, and no field holds a checker cell, a deferred computation or a callback.
type SemanticNode = {
    Id: NodeId
    Kind: SemanticKind
    Range: SourceRange
    /// The node's type, frozen at publication with every substitution applied.
    Type: TypeIdentity
    Children: NodeId list
    Parent: NodeId option
    IsReachable: bool
    EmissionStrategy: EmissionStrategy
    /// The analysed range of an integer value. `None`: not a numeric node, or not analysed.
    ValueRange: ValueRange option
    /// Anchor names of the obligations this node is a source of, in obligation-node order.
    ObligationAnchors: string list
}
