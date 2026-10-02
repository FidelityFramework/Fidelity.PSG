# Indexed revision images

This document describes the current complete-`Revision` codec. It does not
authorize transmitting the retained compiler graph. Live service delivery must
use Baker-authored demanded scopes and exact-base affected deltas, without
soft-deleted node bodies or repeated global premise censuses. This codec is
insufficient for that integration; see [the delivery unit](Indexed_Revision_Architecture.md#delivery-unit).

The image contains the complete `Revision` contract. Its layout is generated
from those types by `tools/GenerateBinary.fsx`; record fields and discriminated
union cases are explicit in `BinaryGenerated.fs`. Generation fails on an
unsupported reachable type. There is no runtime reflection, type discovery,
semantic reconstruction, alternate encoding or partial accepted `Revision`.

The declaration-order tag of each union is interpreted against the same compiled
type at both endpoints. The format fingerprint covers every reachable record
field and union case, its order and its type, together with the PSG schema and
indexed-format version. A schema, format or fingerprint mismatch is refused.

## Physical layout

The first 64 bytes contain:

| Offset | Size | Content |
| --- | --- | --- |
| 0 | 8 | ASCII `FPSGIDX2` |
| 8 | 4 | Format version, little-endian uint32 |
| 12 | 4 | PSG schema, little-endian int32 |
| 16 | 32 | Contract fingerprint, SHA-256 bytes |
| 48 | 8 | Root directory offset, uint64; currently exactly 64 |
| 56 | 8 | Exact image extent, uint64 |

Every composite value has a fixed-width directory: uint32 child count, a zero
uint32 reserved word, then one `(uint64 offset, uint64 extent)` entry per child.
Offsets are relative to the start of the image, never process addresses. Children
partition the rest of their parent extent exactly, in order. Aliasing, overlap,
holes, wrapping extents and trailing bytes are refused. A relocated byte source
reads the same image without rewriting any offset.

Records contain their declared fields in order. Unions contain a BARE union-tag
leaf followed by that case's fields. Tuples contain their elements. Options and
results contain a one-byte tag followed by their value when present. Collections
contain a canonical BARE unsigned count and each element. A map element is a
two-child key/value directory. Maps and sets use strictly increasing keys or
members; duplicates and unordered values are refused rather than normalized.

Scalar leaves use BAREWire's bounded encoding primitives. Integers of declared
width and floating-point bit patterns are little-endian. Strings use a canonical
unsigned byte count and strict UTF-8; malformed UTF-8 and unpaired input UTF-16
surrogates are errors. Decimal leaves preserve the four declared CLR decimal
words, including sign and scale; invalid flag bits are refused. Arbitrary
integers use sign byte `0`/`1`/`2` for zero/positive/negative, then a canonical
unsigned byte count and little-endian unsigned magnitude. Zero has no magnitude;
nonzero magnitudes have no leading zero byte. No numeric width is inferred.

## Read access and ownership

`Binary.openSource limits source` validates the envelope and sorted node index.
`Binary.tryNode id view` performs indexed lookup and reads only the selected
payload. Opening a view and reading one node do **not** establish integrity of
siblings or other fact tables. `Binary.readRevision view` reads the complete
contract and runs `Integrity.check`. It is the complete decode/admission boundary
for representation, not a proof solver or a grant of execution permission.

`Binary.decode limits bytes` uses the same reader over an owned array copy.
`BAREWire.Memory.ByteSource.create length readRange` adapts a host source; the
callback must return exact bounded ranges from stable bytes throughout the
reader's lifetime. The host owns mapping, pinning, publication and disposal.
Unavailable, short or exceptional host reads become typed failures. Scalar
reads may copy their bounded extents; this API makes no zero-copy promise.

The separate `Fidelity.PSG.Hosting` assembly supplies a .NET read-only mapping.
It contains the filesystem and mapping effects; the core contract does not.
Do not place byte-source callbacks or host resources in a semantic `Revision`.

## Limits and maintenance

Every entry point requires explicit limits for total bytes, collection length,
nesting depth, string bytes, arbitrary-integer magnitude bytes and visited values.
Counts and extents are checked before allocations; narrower scalar limits are
checked before asking the host to copy a leaf. Generated record arities and
maximum union arities bound directory tables; collection tables additionally
honor their item limit before copying. A collection limit never caps the fields
of a fixed record. Exhausted depth and value budgets refuse before reading the
affected directory or scalar. Exhaustion is a typed refusal,
never clamping or a smaller graph. The current managed convenience allocates one
array, so its maximum image extent is explicitly bounded by the API's `int`
budget even though on-image offsets are uint64.

After changing a reachable contract type, rebuild the contract and run:

```bash
dotnet fsi tools/GenerateBinary.fsx src/Fidelity.PSG/bin/Release/net10.0/Fidelity.PSG.dll src/Fidelity.PSG/BinaryGenerated.fs
```

The compiled test suite compares the entire generated file with fresh output,
examines every reachable record and declared union constructor, checks independent
vectors and malformed extents, and distinguishes partial reading from complete
validation. Producer and consumer updates must use the same generated contract.
Content hashes, producer names and schema numbers remain descriptive; they do
not establish source provenance, proof discharge or revision freshness.
