# Revision binary codec — unfinished source checkpoint

October 1, 2026. This records draft source for audit and continuation. The six
codec/generator files are **not included in Fidelity.PSG.fsproj** and are not
part of the installed compiler. Published revision schema 12 is unchanged.

The subsequent [cross-project auditor handback](../../Bozzetto/docs/PSG_Transport_Integration_Auditor_Checkpoint_2026-10-01.md)
records verified producer/consumer state, ownership and the coordinated repair gates.
The narrow evidence below remains unchanged.

## Source being preserved

- `BinaryTypes.fs`: explicit snapshot resource limits and typed refusal cases.
- `BinaryRuntime.fs`: bounded BAREWire primitive and collection operations.
- `BinaryGenerated.fs`: generated, typed F# readers/writers for 220 named contract
  types; 10,527 lines of source, not execution logs or serialized sample graphs.
- `Binary.fs`: complete revision encode/decode boundary, format/schema/fingerprint
  agreement, exact input consumption and structural integrity checks.
- `tools/BinaryGeneration.fs` and `tools/GenerateBinary.fsx`: generator source.

The intended library boundary is a pure revision-to-bytes/bytes-to-revision
operation. It opens no socket and supplies no source semantics, proof result,
artifact authority or execution permission. Generator reflection and file output
are tooling operations. A consumer must retain the compiler's authority and
revision identity across transport; structural decoding cannot grant either.

## Evidence already obtained

Persisted-source Sage loading succeeded. An empty revision encoded to 282 bytes,
decoded exactly and re-encoded identically. Empty input, truncated input, trailing
bytes and a changed fingerprint were refused. Receipts are external:

`~/.codex/work/incremental-audit-repairs-2026-10-01/a1/sage/`
`binary-codec-load-r2.messages.json` and `binary-smoke.messages.json`.

These are narrow development controls. No compiled project gate, full primitive
and union-case suite, independent golden encoding, malformed/limit/duplicate
mutation coverage, generator-drift gate, real compiler-published graph roundtrip
or service-to-service acceptance has run for this draft.

## Integration gates still required

1. Review the format and strict resource/canonicality limits against BAREWire,
   wire the codec into the project and execute the compiled contract tests.
2. Require reproducible generation and complete codec coverage. Exercise actual
   published revisions, including malformed and withdrawn evidence controls.
3. Integrate the host transport with a versioned agreement and explicit refusal;
   publish no partial graph and perform no semantic repair at this boundary.
4. Bind transferred revisions to the compiler session's accepted authority.
   Reservation must revoke availability before source mutation, including deferred
   reads and in-flight delivery. Retain shared-demand and joined-cleanup behavior.
5. Run the receiving Alex path from the decoded revision and compare witnesses,
   native artifacts and unchanged-region reuse against the same direct revision.

The companion [Bozzetto transport draft checkpoint](../../Bozzetto/docs/PSG_Binary_Transport_Draft_Checkpoint_2026-10-01.md)
records the adapter draft and coordinated source anchor. Alex remains a passive
reader of `Revision`; transport serialization belongs outside Alex. The running
Bozzetto worker still uses JSON over stdio. This checkpoint does not establish
socketed communication or binary PSG delivery.
