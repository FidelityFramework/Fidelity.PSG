namespace Fidelity.PSG

/// The role of one occurrence in a relation over nodes.
[<RequireQualifiedAccess>]
type ParticipantRole =
    | DemandBinding | DemandCell | DemandInitializer | DemandAlias | DemandUse
    | DemandScope | DemandFrontier | DemandStatement | DemandPremise
    | InitializationBinding | InitializationValue | InitializationSpine | InitializationEntry
    | InitializationUse | InitializationScope | InitializationParent | InitializationPhase
    | InitializationCaller | InitializationCallee | InitializationPremise
    /// Environment reservation occurrences; grouped by allocation, except factory
    /// correspondence grouped by its actual call. Ordinals retain source order.
    | EnvironmentAllocation | EnvironmentBinding | EnvironmentInitializer
    | EnvironmentOwner | EnvironmentImplementation | EnvironmentFormal
    | EnvironmentConstructor | EnvironmentFactory | EnvironmentCall | EnvironmentDestination
    | EnvironmentLayoutProof | EnvironmentSpace | EnvironmentDeclarationInput | EnvironmentAuthorityInput
    /// The node at which the relation is stated.
    | Site
    /// The string operand of the site.
    | Source
    /// The node that identifies the string's extent: a formal or a string literal.
    | ExtentSource
    /// The platform's declaration of the byte representation.
    | RepresentationDeclaration
    /// A reference, an immutable binding, a type annotation or a callee path on the way
    /// to an origin or a formal.
    | Path
    /// A formal reached on that way.
    | Formal
    /// A demanded call of a formal; the ordinal is the formal's position at the call.
    | ReachingCall
    /// The actual that the demanded call supplies at that position.
    | ReachingActual
    /// A call of a formal inside an omitted actual; the ordinal is the formal's position.
    | OmittedCall
    /// The actual of the omitted call at that position.
    | OmittedCallActual
    /// The call of an omission relation whose omitted actual contains the omitted call;
    /// the ordinal is the omitted position.
    | OmissionSite
    /// The omitted actual of an omission relation, in the group of the omission's site and
    /// at its ordinal.
    | OmittedActual
    /// A lambda the call resolves to.
    | Callee
    /// The body of that lambda, in the group of the lambda.
    | CalleeBody
    /// An argument of the resolved call, in the group of the call; the ordinal is its position.
    | CalleeArgument
    /// A parameter that remains for the call, in the group of the call; the ordinal is its position.
    | CalleeParameter
    /// A node of the formal's closed ingress: its callers, dependencies and calls.
    | Ingress
    /// A string literal whose length is a static origin of the extent.
    | Origin
    /// A node of the local comparison or length construction that owns the site.
    | Construction
    /// The source origin recipe consumed this exact lazy force protocol.
    | LazyStringOrigin
    /// The source origin recipe consumed this exact scoped immutable environment read.
    | CapturedStringOrigin

/// One occurrence in a relation: the node, its role, its ordinal within the role (an
/// argument or parameter position; 0 for a role without positions) and its group. The
/// group is the row's site for the row's own occurrences, the call of an input for the
/// occurrences of that input and for the arguments and parameters of its call, the omission's
/// site for an omitted actual, a callee for its body, and the formal for the formal's ingress.
type Participant = { Node: NodeId; Role: ParticipantRole; Ordinal: int; Group: NodeId }

/// What the compiler service derived before the final demand rows. Its OmissionSite and
/// OmittedActual occurrences name the demand rows it read, each by site, ordinal and actual.
type EarlyDerivation = { Derived: Participant list }

/// The participants of a relation with the status of that evidence. A pending relation
/// states its early derivation, which is not a participant list of the relation.
[<RequireQualifiedAccess>]
type ParticipantEvidence =
    | Pending of EarlyDerivation
    | Established of Participant list

/// The early derivation of the string borrow at a site, apart from the current row.
type BorrowHistory = { Site: NodeId; Early: EarlyDerivation }

/// One omission relation of ordinary demand: the call, the ordinal of the actual
/// that the call does not enter, and that actual.
type OrdinaryOmission = {
    Site: NodeId
    Ordinal: int
    Actual: NodeId
}

/// The premise of a string literal whose storage was not materialized: the omission
/// relations whose omitted actual contains it. A pending premise states the omissions read
/// before the final demand rows.
[<RequireQualifiedAccess>]
type StoragePremise =
    | Pending of OrdinaryOmission list
    | Established of OrdinaryOmission list

/// The omissions read for a string literal before the final demand rows, apart from its
/// current premise.
type StoragePremiseHistory = { Literal: NodeId; Early: OrdinaryOmission list }
