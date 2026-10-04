namespace Fidelity.PSG

/// Structural checks of source-authored rows only. No origin, lifetime,
/// representation or calling convention is inferred by this reader.
module internal CallableAggregateIntegrity =
    let check (revision: Revision) : (string * NodeId * string) list =
        let callable = revision.Emission.Callable
        let failure rule site message = "Emission.Callable.Aggregates." + rule, site, message
        let exact site role ordinal group node participants =
            let expected = { Node = node; Role = role; Ordinal = ordinal; Group = group }
            if participants |> List.filter ((=) expected) |> List.length = 1 then []
            else [failure "I5" site "A required typed participant is absent or repeated."]
        let vector site participants =
            [ if participants |> List.exists (fun (p: Participant) -> p.Ordinal < 0) then
                  yield failure "I5" site "A participant has a negative ordinal."
              if (List.distinct participants).Length <> participants.Length then
                  yield failure "I5" site "A row repeats an identical participant occurrence."
              for participant in participants do
                  let present =
                      match participant.Role with
                      | ParticipantRole.AggregateSlot -> callable.AggregateSlots.ContainsKey participant.Node
                      | ParticipantRole.AggregateDeclaration ->
                          callable.AggregateSlots.TryFind participant.Group
                          |> Option.bind (fun slot ->
                              if participant.Ordinal < 0 then None
                              else List.tryItem participant.Ordinal slot.DeclarationFacts)
                          |> Option.exists (fun fact -> fact.Identity = participant.Node)
                      | ParticipantRole.CallableContract -> callable.Contracts.ContainsKey participant.Node
                      | ParticipantRole.CallableCarrier -> callable.Carriers.ContainsKey participant.Node
                      | ParticipantRole.CallableLifetime
                      | ParticipantRole.Source -> revision.CurrentClaims.ContainsKey participant.Node || revision.Nodes.ContainsKey participant.Node
                      | _ -> revision.Nodes.ContainsKey participant.Node
                  if not present then yield failure "I5" site "A participant lacks its exact published row or source occurrence."
                  if not (revision.Nodes.ContainsKey participant.Group || callable.AggregateSlots.ContainsKey participant.Group || callable.Contracts.ContainsKey participant.Group) then
                      yield failure "I5" site "A participant has no exact source or relation group." ]
        let sourceType id =
            revision.Nodes.TryFind id |> Option.map _.Type
            |> Option.orElseWith (fun () -> revision.Emission.Numeric.SourceTypes.TryFind id)
        let rec componentAt path representation =
            match path, representation with
            | [], ValueRepresentation.CallableComponent(slot, data) -> Some(slot, data)
            | CallableAggregatePathStep.RecordField ordinal :: rest, ValueRepresentation.Record(fields, _) ->
                fields |> List.tryItem ordinal |> Option.bind (snd >> componentAt rest)
            | CallableAggregatePathStep.UnionPayload(caseOrdinal, payloadOrdinal) :: rest, ValueRepresentation.Union(cases, _) ->
                cases |> List.tryItem caseOrdinal |> Option.bind (fun (_, payloads) -> List.tryItem payloadOrdinal payloads)
                |> Option.bind (componentAt rest)
            | _ -> None
        let rec dataOnly = function
            | ValueRepresentation.CallableComponent _ -> false
            | ValueRepresentation.Scalar(SettledSlot.Pointer _ | SettledSlot.Opaque _) -> false
            | ValueRepresentation.Scalar _ | ValueRepresentation.Tag _ -> true
            | ValueRepresentation.Buffer(_, element) -> dataOnly element
            | ValueRepresentation.Record(fields, _) -> fields |> List.forall (snd >> dataOnly)
            | ValueRepresentation.Union(cases, _) -> cases |> List.forall (snd >> List.forall dataOnly)
        let representation row =
            revision.Emission.Numeric.OccurrenceRepresentations.TryFind row.Aggregate
            |> Option.orElseWith (fun () ->
                callable.AggregateSlots.TryFind row.Slot
                |> Option.bind (fun slot -> revision.Emission.Numeric.TypeRepresentations.TryFind slot.AggregateType))
        let nominalConstructor = function
            | TypeIdentity.Application(constructor, _) | TypeIdentity.Union(constructor, _) -> Some constructor
            | _ -> None
        let slotChecks (slot: CallableAggregateSlot) =
            [ yield! vector slot.Identity slot.Participants
              yield! exact slot.Identity ParticipantRole.AggregateSlot 0 slot.Identity slot.Identity slot.Participants
              let declarationParticipants =
                  slot.DeclarationFacts |> List.mapi (fun ordinal fact ->
                      { Node = fact.Identity; Role = ParticipantRole.AggregateDeclaration
                        Ordinal = ordinal; Group = slot.Identity })
              if (slot.Participants |> List.filter (fun p -> p.Role = ParticipantRole.AggregateDeclaration)) <> declarationParticipants then
                  yield failure "I5" slot.Identity "The ordered declaration facts differ from their exact slot-owned incidence."
              for fact in slot.DeclarationFacts do
                  if nominalConstructor fact.DeclaredType |> Option.isNone then
                      yield failure "I5" slot.Identity "A declaration fact lacks its exact nominal type identity."
              match slot.Contract with
              | Ok contract -> yield! exact slot.Identity ParticipantRole.CallableContract 0 slot.Identity contract slot.Participants
              | Error _ ->
                  if slot.Participants |> List.exists (fun p -> p.Role = ParticipantRole.CallableContract) then
                      yield failure "I4" slot.Identity "A pending all-absent slot invents a receiving contract participant."
              for declaration in Option.toList slot.Declaration do
                  yield! exact slot.Identity ParticipantRole.AggregateDeclaration 0 slot.Identity declaration slot.Participants
                  match slot.DeclarationFacts with
                  | fact :: _ when fact.Identity = declaration ->
                      if nominalConstructor fact.DeclaredType <> nominalConstructor slot.AggregateType then
                          yield failure "I5" slot.Identity "The root declaration metadata belongs to a different nominal aggregate."
                      match slot.Path, fact.Definition with
                      | CallableAggregatePathStep.RecordField ordinal :: _, CallableAggregateDeclarationDefinition.RecordDef fields
                          when ordinal >= 0 && ordinal < fields.Length -> ()
                      | CallableAggregatePathStep.UnionPayload(caseOrdinal, payloadOrdinal) :: _, CallableAggregateDeclarationDefinition.UnionDef cases
                          when caseOrdinal >= 0 && payloadOrdinal >= 0 &&
                               (cases |> List.tryItem caseOrdinal |> Option.exists (fun (_, fields) -> payloadOrdinal < fields.Length)) -> ()
                      | _ -> yield failure "I5" slot.Identity "The component path has no corresponding declared field or payload position."
                  | _ -> yield failure "I5" slot.Identity "The root declaration has no exact first metadata fact."
              if slot.Path.IsEmpty || (slot.Path |> List.exists (function
                  | CallableAggregatePathStep.RecordField ordinal -> ordinal < 0
                  | CallableAggregatePathStep.UnionPayload(caseOrdinal, payloadOrdinal) -> caseOrdinal < 0 || payloadOrdinal < 0)) then
                  yield failure "I5" slot.Identity "An aggregate slot has no resolved nonnegative field/payload path."
              match slot.Contract with
              | Ok identity when not (callable.Contracts.ContainsKey identity) ->
                  yield failure "I4" slot.Identity "The receiving contract identity has no published contract row."
              | _ -> () ]
        let carrierChecks site (carrier: CallableCarrier) =
            [ if not (revision.Nodes.ContainsKey carrier.Formation) ||
                 not (revision.Nodes.ContainsKey carrier.Implementation || callable.Symbols.ContainsKey carrier.Implementation) then
                  yield failure "I3" site "A carrier lacks its current formation or implementation declaration."
              if Option.isSome carrier.Environment <> Option.isSome carrier.EnvironmentValue then
                  yield failure "I3" site "The carrier's exact environment occurrence and convention disagree."
              if carrier.Kind = CallableKind.NativeEntry && Option.isSome carrier.Environment then
                  yield failure "I3" site "A native entry carries an ordinary closure environment."
              match carrier.Contract with
              | Error _ -> yield failure "I4" site "An aggregate alternative refers to a pending callable contract."
              | Ok identity ->
                  match callable.Contracts.TryFind identity with
                  | None -> yield failure "I4" site "An aggregate carrier has no exact receiving contract row."
                  | Some contract ->
                      if contract.Identity <> identity || contract.Kind <> carrier.Kind ||
                         contract.ParameterTypes <> (carrier.Parameters |> List.map (fun (_, ty, _) -> ty)) ||
                         contract.OmittedParameters <> (carrier.Parameters |> List.indexed |> List.choose (fun (ordinal, (_, _, formal)) -> if carrier.OmittedParameters.Contains formal then Some ordinal else None)) ||
                         sourceType carrier.Result <> Some contract.ResultType then
                          yield failure "I4" site "The carrier differs from the published contract's kind or signature."
                      let physicalParameters =
                          carrier.Parameters |> List.indexed |> List.filter (fun (_, (_, _, formal)) -> not (carrier.OmittedParameters.Contains formal))
                      if List.map fst contract.ParameterRepresentations <> List.map fst physicalParameters ||
                         (physicalParameters |> List.exists (fun (ordinal, (_, _, formal)) ->
                             revision.Emission.Numeric.OccurrenceRepresentations.TryFind formal <>
                             (contract.ParameterRepresentations |> List.tryFind (fst >> (=) ordinal) |> Option.map (snd >> Ok)))) ||
                         revision.Emission.Numeric.OccurrenceRepresentations.TryFind carrier.Result <> Some(Ok contract.ResultRepresentation) then
                          yield failure "I4" site "The source-settled physical parameter or result representations differ from the receiving convention."
                      match carrier.Environment, contract.EnvironmentBytes with
                      | None, None -> ()
                      | Some environment, Some bytes ->
                          match revision.Codata.EnvironmentLayouts.TryFind environment.Owner with
                          | Some layout when layout.Formal = environment.Formal && layout.Implementation = carrier.Implementation && layout.Bytes = bytes -> ()
                          | _ -> yield failure "I3" site "The carrier differs from its exact environment layout."
                      | _ -> yield failure "I3" site "The contract and carrier disagree on explicit environment absence."
              if (Option.isSome carrier.Environment || carrier.Kind = CallableKind.NativeEntry) && carrier.Lifetime.IsEmpty then
                  yield failure "I3" site "A retained environment or native entry has no lifetime participants."
              yield! vector site carrier.Lifetime ]
        let valueChecks (row: CallableAggregateValue) =
            let site = row.Occurrence
            let exactRow role ordinal node = exact site role ordinal site node row.Participants
            [ yield! vector site row.Participants
              yield! exactRow ParticipantRole.AggregateValue 0 site
              yield! exactRow ParticipantRole.AggregateSource 0 row.Aggregate
              yield! exactRow ParticipantRole.AggregateSlot 0 row.Slot
              for ordinal, input in List.indexed row.FormationInputs do
                  yield! exactRow ParticipantRole.AggregateInput ordinal input
              for value in Option.toList row.Value do yield! exactRow ParticipantRole.AggregateWrite 0 value
              for frontier in Option.toList row.Frontier do yield! exactRow ParticipantRole.AggregateReadFrontier 0 frontier
              match row.Operation, row.Frontier with
              | CallableAggregateOperation.Snapshot, None -> yield failure "I5" site "A stored read has no snapshot frontier."
              | _ -> ()
              if row.Bytes < 0 || row.Alignment <= 0 then yield failure "I1" site "Component storage has no admitted extent and alignment."
              match callable.AggregateSlots.TryFind row.Slot with
              | None -> yield failure "I5" site "The component's resolved slot row is absent."
              | Some slot ->
                  if slot.Path |> List.exists (function CallableAggregatePathStep.UnionPayload _ -> true | _ -> false) then
                      if row.Tag.IsNone then yield failure "I5" site "A callable union payload has no current constructor/tag evidence."
                  match representation row with
                  | Some(Ok held) ->
                      match componentAt slot.Path held with
                      | Some(identity, data) when identity = slot.Identity && dataOnly data -> ()
                      | _ -> yield failure "I1" site "The callable field/payload is absent or represented as ordinary code data."
                  | _ -> yield failure "I1" site "The aggregate has no published component representation."
                  let count = row.Alternatives.Length
                  let callableCase = slot.Path |> List.tryPick (function
                      | CallableAggregatePathStep.UnionPayload(caseOrdinal, _) -> Some caseOrdinal
                      | _ -> None)
                  match slot.Contract with
                  | Error _ when count <> 0 -> yield failure "I4" site "A present callable payload has no settled receiving contract."
                  | _ -> ()
                  if (row.Alternatives |> List.map _.Ordinal) <> [0 .. count - 1] ||
                     (row.Alternatives |> List.map _.Carrier |> List.distinct |> List.length) <> count then
                      yield failure "I2" site "Alternatives do not cover each selector ordinal exactly once."
                  match count, row.Selector, row.Tag with
                  | 0, None, Some tag when
                      (callableCase |> Option.exists ((<>) tag.CaseOrdinal)) ||
                      (tag.Payload.IsNone && tag.PayloadOrdinal.IsNone) -> ()
                  | 0, _, _ -> yield failure "I2" site "Only an absent union payload may have no alternatives; it has no selector."
                  | _, Some selector, _ ->
                      if selector.Lower <> 0 || selector.UpperExclusive <> count then
                          yield failure "I2" site "The logical selector range differs from the exact alternative count."
                      match selector.Storage, selector.Slot, selector.ByteOffset with
                      | None, None, None when count = 1 -> ()
                      | Some storage, Some(SettledSlot.Integer(bits, _)), Some offset when bits > 0 && offset >= 0 ->
                          yield! exactRow ParticipantRole.AggregateSelector 0 storage
                          if (bits < 31 && count > (1 <<< bits)) || bigint offset + (bigint bits + 7I) / 8I > bigint row.Bytes then
                              yield failure "I2" site "The published selector storage cannot contain its logical domain or extent."
                      | _ -> yield failure "I2" site "Selector storage is missing, inconsistent or not an admitted integer placement."
                  | _, None, _ -> yield failure "I2" site "A callable family has no logical selector domain."
                  match count, row.Tag, callableCase with
                  | n, Some tag, Some expected when n > 0 && (tag.CaseOrdinal <> expected || tag.Payload.IsNone) ->
                      yield failure "I2" site "An inactive union payload is treated as a callable alternative."
                  | _ -> ()
                  match row.Value, row.SelectedAlternative with
                  | Some value, Some selected ->
                      match row.Alternatives |> List.tryItem selected with
                      | Some alternative when row.FormationInputs |> List.contains value ->
                          if value <> alternative.Carrier && not (row.FormationInputs |> List.contains alternative.Carrier) then
                              yield failure "I5" site "The selected write is not paired with its actual carrier input."
                      | _ -> yield failure "I2" site "The written value has no selected alternative in the admitted family."
                  | None, None -> ()
                  | Some _, None when row.Operation = CallableAggregateOperation.Project || row.Operation = CallableAggregateOperation.Snapshot -> ()
                  | _ -> yield failure "I5" site "The source write and its selection are incomplete."
                  for alternative in row.Alternatives do
                      yield! exactRow ParticipantRole.CallableCarrier alternative.Ordinal alternative.Carrier
                      yield! exactRow ParticipantRole.CallableFormation alternative.Ordinal alternative.Formation
                      yield! exactRow ParticipantRole.CallableContract alternative.Ordinal alternative.Contract
                      for value in Option.toList alternative.EnvironmentValue do
                          yield! exactRow ParticipantRole.CallableEnvironment alternative.Ordinal value
                      match callable.Carriers.TryFind alternative.Carrier with
                      | None -> yield failure "I3" site "The alternative has no carrier formation row."
                      | Some carrier ->
                          yield! carrierChecks site carrier
                          if carrier.Occurrence <> alternative.Carrier || carrier.Formation <> alternative.Formation ||
                             carrier.EnvironmentValue <> alternative.EnvironmentValue then
                              yield failure "I3" site "The selected code and environment belong to different formations."
                          if carrier.Contract <> Ok alternative.Contract then
                              yield failure "I4" site "The alternative's contract differs from its carrier's exact contract."
                          match alternative.Adapter with
                          | None when Ok alternative.Contract = slot.Contract -> ()
                          | Some adapter ->
                              match callable.Carriers.TryFind adapter with
                              | Some adapted when adapted.Contract = slot.Contract && Result.isOk slot.Contract ->
                                  yield! carrierChecks site adapted
                                  yield! exactRow ParticipantRole.CallableAdapter alternative.Ordinal adapter
                              | _ -> yield failure "I4" site "The selected adapter has no settled receiving contract."
                          | _ -> yield failure "I4" site "A slot combines different contract identities without an admitted adapter."
                          match carrier.Environment, alternative.EnvironmentPlacement with
                          | None, None -> ()
                          | Some environment, Some placement when Some placement.Value = carrier.EnvironmentValue && placement.Owner = environment.Owner ->
                              match revision.Codata.EnvironmentLayouts.TryFind environment.Owner with
                              | Some layout when layout.Bytes = placement.ViewBytes -> ()
                              | _ -> yield failure "I3" site "The environment view extent differs from its exact layout."
                              if placement.ByteOffset < 0 || placement.StorageBytes <= 0 || placement.Alignment <= 0 ||
                                 bigint placement.ByteOffset + bigint placement.StorageBytes > bigint row.Bytes then
                                  yield failure "I1" site "The environment descriptor has no admitted in-component placement."
                              match placement.Source, callable.ValueShapes.TryFind placement.Value with
                              | CallableAggregateEnvironmentSource.EnvironmentValue, Some(CallableValueShape.Data _) -> ()
                              | CallableAggregateEnvironmentSource.CallableEnvironmentView, Some(CallableValueShape.Callable _) -> ()
                              | _ -> yield failure "I1" site "The environment operand differs from its explicit data/view projection."
                          | _ -> yield failure "I3" site "The alternative drops or crosses its exact environment placement."
              for tag in Option.toList row.Tag do
                  yield! vector site tag.Participants
                  yield! exact site ParticipantRole.AggregateConstructor 0 tag.Constructor tag.Constructor tag.Participants
                  for read in Option.toList tag.TagRead do
                      yield! exact site ParticipantRole.AggregateTag 0 tag.Constructor read tag.Participants
                      match revision.Nodes.TryFind read with
                      | Some { Kind = SemanticKind.DUGetTag(subject, _) } when subject = row.Aggregate -> ()
                      | _ -> yield failure "I5" site "The tag read does not name the selected aggregate occurrence."
                  match tag.PayloadOrdinal, tag.Payload with
                  | Some ordinal, Some payload when ordinal >= 0 ->
                      yield! exact site ParticipantRole.AggregatePayload ordinal tag.Constructor payload tag.Participants
                  | None, None when row.Alternatives.IsEmpty -> ()
                  | _ -> yield failure "I5" site "Union payload identity, ordinal and callable presence disagree."
                  if tag.CaseOrdinal < 0 then yield failure "I5" site "The constructor tag has a negative ordinal."
                  match revision.Nodes.TryFind tag.Constructor with
                  | Some { Kind = SemanticKind.UnionCase(_, caseOrdinal, payload) }
                  | Some { Kind = SemanticKind.DUConstruct(_, caseOrdinal, payload, _) } ->
                      let payloadAt ordinal =
                          if ordinal = 0 && payload = tag.Payload then payload
                          else payload |> Option.bind revision.Nodes.TryFind |> Option.bind (fun node ->
                              match node.Kind with SemanticKind.TupleExpr fields -> List.tryItem ordinal fields | _ -> None)
                      if caseOrdinal <> tag.CaseOrdinal ||
                         (tag.PayloadOrdinal |> Option.bind payloadAt) <> tag.Payload then
                          yield failure "I5" site "The retained constructor/tag/payload differs from the live constructor."
                  | _ -> yield failure "I5" site "The union constructor has no current published construction." ]
        let accountChecks site (account: CallableAggregateDependencyAccount) =
            let unique key values = (values |> List.map key |> List.distinct |> List.length) = values.Length
            let direct = callable.AggregateValues.TryFind site |> Option.defaultValue []
            let valuesCurrent = account.Values |> List.forall (fun row ->
                callable.AggregateValues.TryFind row.Occurrence |> Option.exists (List.contains row))
            let slots = account.Values |> List.map _.Slot |> List.distinct
            let carriers = account.Values |> List.collect (fun row -> row.Alternatives |> List.collect (fun alternative ->
                alternative.Carrier :: Option.toList alternative.Adapter)) |> List.distinct
            let contracts =
                (account.Slots |> List.choose (fun slot -> match slot.Contract with Ok identity -> Some identity | Error _ -> None)) @
                (account.Carriers |> List.choose (fun carrier -> match carrier.Contract with Ok identity -> Some identity | Error _ -> None))
                |> List.distinct
            let inputs = account.Values |> List.collect (fun row -> row.Occurrence :: row.FormationInputs) |> List.distinct
            let flows = inputs |> List.choose callable.Flows.TryFind
            let joins = inputs |> List.choose callable.Joins.TryFind
            let participants =
                (account.Slots |> List.collect _.Participants) @
                (account.Values |> List.collect (fun row -> row.Participants @ (row.Tag |> Option.map _.Participants |> Option.defaultValue []))) @
                (account.Carriers |> List.collect _.Lifetime) @
                (account.Contracts |> List.collect _.Participants)
            let participantNodes = participants |> List.map _.Node |> List.distinct
            let sources = participantNodes |> List.choose (fun id ->
                revision.Nodes.TryFind id |> Option.map (fun node ->
                    { Node = id; Kind = node.Kind; Type = node.Type; Children = node.Children; Anchors = node.ObligationAnchors }))
            let claims = participantNodes |> List.choose (fun id -> revision.CurrentClaims.TryFind id |> Option.map (fun claim -> id, claim))
            [ if account.Occurrence <> site || not valuesCurrent ||
                 (account.Values |> List.filter (fun row -> row.Occurrence = site)) <> direct ||
                 not (unique (fun (row: CallableAggregateValue) -> row.Occurrence, row.Slot) account.Values) then
                  yield failure "I6" site "The dependency account drops, repeats or replays an aggregate value row."
              for row in account.Values do
                  for input in row.FormationInputs do
                      match callable.AggregateValues.TryFind input with
                      | Some values when values |> List.exists (fun value -> not (List.contains value account.Values)) ->
                          yield failure "I6" site "A referred aggregate formation is missing from the dependency account."
                      | _ -> ()
              if account.Slots <> (slots |> List.choose callable.AggregateSlots.TryFind) ||
                 account.Carriers <> (carriers |> List.choose callable.Carriers.TryFind) ||
                 account.Contracts <> (contracts |> List.choose callable.Contracts.TryFind) ||
                 account.Flows <> flows || account.Joins <> joins then
                  yield failure "I6" site "The account differs from the complete current slot, carrier, contract or flow/join rows."
              if account.Participants <> participants || account.Sources <> sources || account.Claims <> claims then
                  yield failure "I6" site "The ordered dependency incidence or its published source/claim evidence is stale." ]
        // Repeated declaration occurrences retain their slot/path incidence,
        // but one identity cannot denote conflicting immutable definitions.
        // This compares published facts only; no type instantiation is inferred.
        let declarationsByIdentity =
            callable.AggregateSlots.Values
            |> Seq.collect (fun slot -> slot.DeclarationFacts |> Seq.map (fun fact -> slot.Identity, fact))
            |> Seq.groupBy (fun (_, fact) -> fact.Identity)
        [ for declaration, occurrences in declarationsByIdentity do
              let occurrences = Seq.toList occurrences
              if (occurrences |> List.map snd |> List.distinct |> List.length) > 1 then
                  for slot, _ in occurrences do
                      yield failure "I5" slot $"Declaration {NodeId.value declaration} has conflicting canonical metadata facts."
          for KeyValue(key, contract) in callable.Contracts do
              if key <> contract.Identity then yield failure "I4" key "A callable contract is filed under another identity."
              yield! vector key contract.Participants
              yield! exact key ParticipantRole.CallableContract 0 key key contract.Participants
          for KeyValue(key, carrier) in callable.Carriers do
              yield! vector key carrier.Lifetime
              match carrier.Contract with
              | Ok identity when not (callable.Contracts.ContainsKey identity) ->
                  yield failure "I4" key "A settled carrier contract row is absent."
              | _ -> ()
          for KeyValue(key, slot) in callable.AggregateSlots do
              if key <> slot.Identity then yield failure "I5" key "A slot is filed under another identity."
              yield! slotChecks slot
              if not (callable.AggregateDependencies |> Map.exists (fun _ account -> List.contains slot account.Slots)) then
                  yield failure "I6" key "A callable aggregate slot has no current dependency account."
          for KeyValue(site, values) in callable.AggregateValues do
              if values.IsEmpty || (values |> List.map _.Slot |> List.distinct |> List.length) <> values.Length then
                  yield failure "I5" site "An aggregate occurrence has missing or duplicated slot rows."
              for row in values do
                  if row.Occurrence <> site then yield failure "I5" site "A value is filed under another occurrence."
                  yield! valueChecks row
              match callable.AggregateDependencies.TryFind site with
              | Some account -> yield! accountChecks site account
              | None -> yield failure "I6" site "The callable selection has no dependency account."
          for KeyValue(site, _) in callable.AggregateDependencies do
              if not (callable.AggregateValues.ContainsKey site) then
                  yield failure "I6" site "A dependency account has no current aggregate occurrence." ]
