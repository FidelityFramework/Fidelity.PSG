# Indexed revision images

Baker/CCS settles source bindings, demand, def-use and storage identity,
representations and proof premises, then publishes authorized live scopes of a
checked revision. Completeness means all facts required by those scopes; it does
not mean the retained compiler corpus. Alex creates typed emission operands from those settled
facts; its emission accumulator does not establish semantic facts on the graph.
This is the distinction in the normative [PSG architectural separation and
binding identity contracts](../../clef-lang-spec/spec/program-semantic-graph.md#123-architectural-separation).
The binary representation preserves stored facts and identities. Encoding and
reading do not repair the graph, select semantic scopes or assign new identities.

## Delivery unit

Initial attachment receives only demanded live occurrences, their settled local
facts, necessary boundary contracts and explicit support correspondence. Later
delivery carries affected additions, replacements, withdrawals and retirements
against an exact resident base. Settled scope content remains resident. Source
analysis must revalidate its complete support before authorizing that content
for the new checked revision. Equal content or physical signatures grant no such
authorization.

Full retained graph transmission and soft-deleted node bodies are prohibited by
the owner. A whole checked program may be a source-authorized scope, but unused
library bodies and source-internal global domain premise snapshots do not become
transport payloads. Collection membership and absence remain complete source
dependencies. They must not be weakened to make a smaller packet.

An `open` changes the name-resolution environment. It is not an execution root
or a demand for every declaration in a library, and it does not authorize eager
mapping of all library bodies. The source checks the lookups and absence or
membership judgments affected by that visibility change. Actual newly demanded
declarations activate their required closure. Settled unrelated scopes remain
resident; a later transaction carries affected facts and authorizations rather
than retransmitting those scopes. Debouncing a complete-graph push does not meet
this contract.

The normative [scoped re-evaluation contract](../../clef-lang-spec/spec/program-hypergraph.md#51-scoped-re-evaluation-and-witness-authorization)
assigns scope selection, dependency closure and reuse authorization to source
analysis. Publication copies stored Baker rows. Alex and transport readers do
not infer closure or prune a retained graph into a scope.

The current `Revision` codec below represents the existing complete contract.
It is not an acceptable live service delivery unit. Its 88,482,120-byte native
sample measurement exposed retained library bodies and repeated global domain
premises. The scoped payload and delta integration supersedes that path; it has
not yet passed native service acceptance. Increasing its frame cap does not
repair that architectural defect.

`Fidelity.PSG` owns the revision schema and its generated reader. The image uses
directories whose fixed-width entries carry an offset and an extent. Every
offset is relative to the image's start, never a process address. Scalar leaves
use bounded BARE encodings. The header identifies the format and schema; a
fingerprint binds the generated type layout. These identify a representation,
not a compiler proof or an accepted executable.

BAREWire supplies the bounded `ByteSource` interface. One generated reader can
read an owned array or host-managed mapped memory. A socket receives a bounded
transaction; it is not itself a random-access byte source. Files, mapped regions
and received buffers can hold the same image
bytes. A sorted node index supports arbitrary traversal order without reading
every preceding node body.

| Responsibility | Owner |
| --- | --- |
| Source semantics, binding/demand/def-use/storage identity, representations and proof premises | Baker/CCS |
| Published schema, indexed representation and generated reader | Fidelity.PSG |
| Portable encoding and bounded byte-source access | BAREWire |
| File handles, mapping lifetime and disposal on .NET | Fidelity.PSG.Hosting |
| Passive witnessing and typed emission operands from settled facts | Alex |
| Proof discharge, artifact acceptance and launch validation | Composer |
| Sockets, workspace-host identity, correlation, cancellation and joined cleanup | Bozzetto |
| Work demand, invalidation and work eligibility | Fidelity.FSharp.Incremental |

## Readings and acceptance

`Binary.openSource` checks the image envelope and node index. `Binary.tryNode`
reads one indexed node. Neither operation establishes that unread sibling
tables are valid. `Binary.readRevision` reads every published field and performs
the complete structural integrity check. A successful indexed read must not be
promoted into a complete-graph acceptance decision.

Opening currently materializes the node index; it does not read every node body.
The public random-access operation selects a node. Other published fact tables
are available through the complete revision reader. `readRevision` materializes
the immutable `Revision` value that Alex currently consumes. The byte-source
adapters copy bounded read ranges; this implementation makes no zero-copy or
performance claim.

Structural integrity is also distinct from proof discharge, provenance and
source freshness. A received graph does not carry a deserialized compiler proof
receipt. Composer must establish the evidence required for the actual graph and
source scope it accepts. The Composer workspace host (`Bozzetto.Composer`) owns
the live project sessions. Its epoch and Bozzetto's request correlation preserve
orchestration identity; they do not substitute for Composer's artifact and launch
checks. Edit reservation withdraws current-result eligibility before source is
written.

## Required inspection reader

The owner requires JSON inspection to be rendered from the binary revision by a
separate reader using `Fidelity.Data`, through an independently owned sink. Alex
does not acquire a serializer or perform semantic reconstruction for inspection.
The separate [Fidelity.PSG.Json reader](../src/Fidelity.PSG.Json/README.md) now
implements this boundary. It calls `Binary.readRevision` before generated writers
render every published field with Fidelity.Data. Wide integers use typed decimal
strings; decimal and floating values retain exact bits, including signed zero and
NaN payloads. Generation uses tool-time reflection; runtime inspection does not.

The explicit `PsgInspect` process owns its input mapping and output sink. Compiler
publication neither starts it nor waits for rendering. Public MCP JSON-RPC
adapters and graph inspection are distinct from private compiler transport. The
existing whole-revision base64 operation must be replaced by the scoped contract
as part of that integration. Rendering establishes no proof or execution authority.

## Host lifetime

The publisher and host keep image bytes immutable for the reader's lifetime.
`ByteSource.ofArray` makes an owned copy. A custom byte source supplies stable,
bounded ranges and reports unavailability; its callbacks are reader substrate,
never fields in a published revision.

The separate `Fidelity.PSG.Hosting` assembly owns .NET file and mapping handles.
Its complete and per-node read operations serialize with disposal. A retained
view refuses accesses to its disposed source. `FileShare.Read` excludes
cooperating writers; it is not protection against arbitrary external file
mutation. The core PSG assembly has no file or process I/O and does not reference
the hosting assembly.

The self-hosting boundary is the byte source and its owned lifetime. Clef memref
and Fable hosts must supply that substrate while sharing the schema and reader
rules. The current .NET implementation does not establish either port's
implementation or acceptance.

Implementation: [binary boundary](../src/Fidelity.PSG/Binary.fs),
[generated reader](../src/Fidelity.PSG/BinaryGenerated.fs),
[mapping owner](../src/Fidelity.PSG.Hosting/MappedRevision.fs).
Validation belongs in the transport checkpoint and test receipts, separately
from this architectural description.
