# Scoped publication contract

`ScopedPublication` is a pure metadata catalog for source-authored scopes. It
contains no semantic node bodies, retained `Revision`, deferred computation or
host resource. It separates the compiler's accepted checked revision from scope
content identity and the subscription's delivery position.

| Value | Meaning |
| --- | --- |
| `CheckedRevisionId` | Session and compiler-assigned accepted ordinal. A schema number, timestamp or hash cannot substitute for it. |
| `DeliveryCursor` | Subscription and delivery ordinal; advancing it does not invent a new checked revision. |
| `ScopeDescriptor` | Source-selected live occurrences, their actual context breadcrumbs, consumed boundary/support identities and artifact owners. |
| `ScopeAuthorization` | Exact scope content authorized by the source for a checked revision, with complete declared boundary and support stamps. |
| `SourceScopeTransaction` | Exact base and target, explicit scope changes, authorization/withdrawal and ownership replacement/retirement declarations. |
| `ScopedCatalog` | Resident metadata and its current authorizations. Residence after withdrawal grants no permission. |

Support categories include actual nodes, rules, declarations, collection
membership, absence and a whole owning analysis region. Where support cannot yet
be made precise, Baker validates that complete region. A compact support stamp
does not discharge its premises or permit skipping source validation. The
contract merely checks that every declared support position is accounted for.

`start` creates an empty subscription anchored to an already accepted checked
revision. `apply` requires its exact base, a strictly next delivery cursor and
an equal or later checked revision within the same session. Attachment or new
demand may therefore use the existing checked revision. Every surviving scope
has an explicit target authorization or withdrawal; unchanged content never
implicitly inherits authority in a later revision. Replacement content versions
advance, and explicit artifact transitions account for changed definition,
storage and activation ownership. Invalid declarations leave the prior immutable
catalog untouched.

Each body's context inventory contains every source-authored occurrence path,
including distinct paths through a shared DAG. Typed breadcrumb ports distinguish
execution children from module declaration membership. Parents and siblings are
identity handles and do not request their bodies. Historical identity is likewise
separate from current live occurrence membership. An `open` is a visibility change,
not a demand for every member or permission to map a library aggressively.
Baker determines affected lookup, membership and absence judgments and newly
demanded closure. No reader infers those decisions.

This catalog does not establish availability or completeness of executable
scope facts, source proof truth, artifact eligibility, transport acknowledgement
or launch permission. Those boundaries remain separately owned. The complete
semantic payload, Baker publication, subscription protocol and native receiving
acceptance must be implemented before this foundation supplies service delivery.
The current complete `Revision` codec is not that payload and must never become
a full-graph recovery path.

The present transaction declares complete per-scope target support metadata.
That account can grow with the resident catalog even while bodies are retained.
A mature bounded delivery protocol must preserve explicit source authorization
without resending unchanged metadata wholesale; this metadata API is not a
performance result or a final protocol design.

## Live occurrence sections

`LiveOccurrenceSection` carries exact live bodies and explicit source-written
dispositions for every original child position. A child enters a local body,
enters an explicitly named imported scope/boundary, or has source omission
support. A missing body never lets a reader infer omission. Original ordinals
remain separate when positions share a body. Inactive body rows are refused;
context and omitted-child handles require no body. Validation checks these
declarations, not source truth, boundary settlement or dependency completeness.

`OccurrenceDelivery` requires one matching section for each added or replaced
scope and none for retirement or unchanged reauthorization. `OccurrenceBinary`
encodes the changed sections and exact-base transaction over BAREWire in a
separate offset-indexed image. Its `FPSGOCC1` envelope refuses complete Revision
images with no alternate decoder. A host-supplied `ByteSource` owns stable bytes
and their lifetime. Decoding checks representation and section accounts;
`ScopedPublication.apply` separately checks the resident base.

Occurrence availability is one part of compilation. These sections do not yet
carry all settled emission, import, storage and proof facts and cannot serve as
an executable revision. A socket offer, ACK or successful catalog application
does not supply those facts or authorize a launch.

Current breadcrumb sibling inventories can grow with inactive declarations, and
complete authorizations can grow with resident scopes. Those costs must be
measured and corrected by source-authored context/authorization contracts before
claiming delta-sized metadata. Omission of bodies does not establish byte-size
invariance or bounded production performance.
