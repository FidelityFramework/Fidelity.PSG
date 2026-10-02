namespace Fidelity.PSG

/// A source-selected position account. Positions are sparse original ordinals;
/// omitted declaration members have neither identities nor bodies in this account.
type SourcePortAccount = {
    Extent: int
    Stamp: string
    Positions: Map<int, NodeId>
}

/// A declaration container needed for positional correspondence, without its
/// retained SemanticNode or its inactive member inventory.
type SourceContextHeader = {
    Identity: NodeId
    Name: string
    Ports: Map<OccurrencePort, SourcePortAccount>
}

[<RequireQualifiedAccess>]
type SourceBindingClass = Formal | ImmutableValue | MutableCell

/// Baker's account for one resolved reference occurrence. Storage intent and
/// admitted physical authority remain distinct; neither is inferred by a reader.
type BindingUseContract = {
    Binding: NodeId
    Name: string
    Class: SourceBindingClass
    IsProgramSlotIntent: bool
    HasProgramSlotAuthority: bool
    IsFunctionBinding: bool
    IsCallableDeclaration: bool
    IsPartialApplication: bool
}

[<RequireQualifiedAccess>]
type SourceEntryReason = ExecutableRoot | DetachedDefinition | BoundaryScope | SpatialRoot

/// The source specifies both an entry and its actual occurrence. A receiver
/// never finds entries by enumerating library or module members.
type SourceWitnessEntry = {
    Focus: NodeId
    Reason: SourceEntryReason
    Context: OccurrenceBreadcrumb list
}

/// Immutable traversal and resolved-use rows written by Baker. These are data
/// readings, not a graph selection algorithm or a source authority callback.
type WitnessSourceReadings = {
    Entries: SourceWitnessEntry list
    Ports: Map<NodeId * OccurrencePort, SourcePortAccount>
    Children: Map<NodeId, ChildDisposition list>
    Contexts: Map<NodeId, OccurrenceBreadcrumb list list>
    ContextHeaders: Map<NodeId, SourceContextHeader>
    BindingUses: Map<NodeId, BindingUseContract>
}

[<RequireQualifiedAccess>]
module WitnessSourceReadings =
    let empty =
        { Entries = []; Ports = Map.empty; Children = Map.empty; Contexts = Map.empty
          ContextHeaders = Map.empty; BindingUses = Map.empty }
