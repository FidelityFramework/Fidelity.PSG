/// Revisions assembled from contract values, for tests of the contract itself.
module Fidelity.PSG.Tests.Build

open Fidelity.PSG

let range : SourceRange =
    { File = "contract-test.clef"; Start = { Line = 1; Column = 0 }; End = { Line = 1; Column = 0 } }

let private constructor name kind : ConstructorIdentity =
    { Declaration = { Module = []; Name = name }; Parameters = []; NativeKind = Some kind }

let unitType = TypeIdentity.Application(constructor "unit" NTUKind.NTUunit, [])
let boolType = TypeIdentity.Application(constructor "bool" NTUKind.NTUbool, [])

/// One node, with the children given and no parent.
let node (number: int) (kind: SemanticKind) (children: int list) : SemanticNode =
    { Id = NodeId number
      Kind = kind
      Range = range
      Type = unitType
      Children = List.map NodeId children
      Parent = None
      IsReachable = true
      EmissionStrategy = EmissionStrategy.Inline
      ValueRange = None
      ObligationAnchors = [] }

/// A revision that holds the nodes given and nothing else. It states no row for them.
let bare (nodes: SemanticNode list) : Revision =
    { Revision.empty "contract-test" with Nodes = nodes |> List.map (fun held -> held.Id, held) |> Map.ofList }

/// The rows the compiler service publishes for every node it holds, stated for the
/// nodes of the revision given: each node is data, is its own alias target and is
/// its own support, and each reachable node has a source type and a representation.
let covered (revision: Revision) : Revision =
    let held = revision.Nodes |> Map.toList
    let reachable = held |> List.filter (fun (_, node) -> node.IsReachable)
    let form : Result<ValueRepresentation, string> = Ok(ValueRepresentation.Scalar SettledSlot.Bool)
    let callable =
        { revision.Emission.Callable with
            ValueShapes = held |> List.map (fun (id, _) -> id, CallableValueShape.Data id) |> Map.ofList
            AliasTargets = held |> List.map (fun (id, _) -> id, id) |> Map.ofList
            Supports = held |> List.map (fun (id, _) -> id, Set.singleton id) |> Map.ofList }
    let numeric =
        { revision.Emission.Numeric with
            SourceTypes = reachable |> List.map (fun (id, node) -> id, node.Type) |> Map.ofList
            OccurrenceRepresentations = reachable |> List.map (fun (id, _) -> id, form) |> Map.ofList }
    { revision with Emission = { revision.Emission with Callable = callable; Numeric = numeric } }

/// A revision that holds the nodes given, with the rows published for every node.
let revision (nodes: SemanticNode list) : Revision =
    covered (bare nodes)

/// A binding with one literal child, each naming the other.
let bindingWithLiteral : Revision =
    let literal = { node 2 (SemanticKind.Literal(NativeLiteral.Bool true)) [] with Parent = Some (NodeId 1); Type = boolType }
    let binding = { node 1 (SemanticKind.Binding("value", false, false, None)) [ 2 ] with Type = boolType }
    revision [ binding; literal ]
