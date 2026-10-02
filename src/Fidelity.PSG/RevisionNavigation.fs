namespace Fidelity.PSG

/// Passive comparisons of Baker's positional accounts. These readings never
/// search a retained graph, infer an entry or authorize a proof or an artifact.
[<RequireQualifiedAccess>]
module RevisionNavigation =
    let private knownPosition (revision: Revision) identity =
        match revision.Nodes.TryFind identity, revision.SourceReadings.ContextHeaders.TryFind identity with
        | Some body, _ when body.Id = identity && body.IsReachable -> true
        | None, Some header when header.Identity = identity -> true
        | _ -> false

    /// A root is an explicitly stored empty path. Returning the declared anchor
    /// does not make that identity an executable body.
    let checkContext (revision: Revision) focus (path: OccurrenceBreadcrumb list) =
        let readings = revision.SourceReadings
        let rec check (child: NodeId) (seen: Set<NodeId>) (remaining: OccurrenceBreadcrumb list) =
            match remaining with
            | [] ->
                match readings.Contexts.TryFind child with
                | Some roots when List.contains [] roots -> Ok child
                | _ -> Error "Source occurrence path terminates before an explicitly declared root."
            | frame :: rest ->
                if seen |> Set.contains frame.Parent then Error "Source occurrence path contains a repeated ancestor."
                elif not (knownPosition revision frame.Parent) then Error "Source occurrence parent has no live body or context header."
                else
                    match readings.Ports.TryFind(frame.Parent, frame.Port) with
                    | None -> Error "Source occurrence port account is absent."
                    | Some port when port.Extent <> frame.Extent || port.Stamp <> frame.Stamp ->
                        Error "Source occurrence port extent or stamp differs from its declared account."
                    | Some port when System.String.IsNullOrWhiteSpace port.Stamp || frame.Ordinal < 0 || frame.Ordinal >= port.Extent ->
                        Error "Source occurrence has an invalid port stamp or original ordinal."
                    | Some port when port.Positions.TryFind frame.Ordinal <> Some child ->
                        Error "Source occurrence is absent from its declared original port position."
                    | Some port ->
                        let original =
                            match frame.Port, revision.Nodes.TryFind frame.Parent with
                            | OccurrencePort.StructuralChild, Some parent ->
                                if parent.Children.Length <> port.Extent || (parent.Children |> List.tryItem frame.Ordinal) <> Some child then
                                    Error "Source occurrence structural position disagrees with its live parent body."
                                else Ok ()
                            | OccurrencePort.StructuralChild, None ->
                                Error "A declaration context header cannot stand in for a structural parent body."
                            | OccurrencePort.ModuleDeclaration, _ ->
                                match readings.ContextHeaders.TryFind frame.Parent with
                                | Some header when header.Ports.TryFind frame.Port <> Some port ->
                                    Error "Source declaration context header disagrees with its port account."
                                | _ -> Ok ()
                        original |> Result.bind (fun () -> check frame.Parent (seen.Add frame.Parent) rest)
        if not (knownPosition revision focus) then Error "Source occurrence focus has no live body or context header."
        else
            match readings.Contexts.TryFind focus with
            | None -> Error "Source occurrence context inventory is absent."
            | Some paths when not (List.contains path paths) -> Error "The whole occurrence path is not in the source context inventory."
            | Some _ -> check focus (Set.singleton focus) path

    /// The original child position and Baker's stored disposition are required.
    /// Omission is read without loading the child's body. Imported traversal
    /// requires its own exact resident scope and is not guessed from local data.
    let tryLocalChild (revision: Revision) parent ordinal =
        match revision.Nodes.TryFind parent, revision.SourceReadings.Children.TryFind parent with
        | None, _ -> Error "Source structural parent body is absent."
        | _, None -> Error "Source structural child disposition account is absent."
        | Some body, Some dispositions when dispositions.Length <> body.Children.Length ->
            Error "Source structural child disposition account is incomplete."
        | Some body, Some dispositions ->
            match List.tryItem ordinal dispositions, List.tryItem ordinal body.Children with
            | Some disposition, Some child when disposition.Ordinal = ordinal ->
                match disposition.Traversal with
                | ChildTraversal.EnterLocal declared when declared <> child ->
                    Error "Source local child disposition names another original child."
                | ChildTraversal.EnterLocal declared ->
                    match revision.Nodes.TryFind declared with
                    | Some selected when selected.Id = declared && selected.IsReachable -> Ok declared
                    | _ -> Error "Source local child has no live resident body."
                | ChildTraversal.EnterImported _ -> Error "Imported child traversal requires its exact authorized resident scope."
                | ChildTraversal.SourceOmitted _ -> Error "The source omitted this original child position."
            | _ -> Error "Source structural child original ordinal is absent or inconsistent."
