# JSON inspection

This optional assembly renders a complete PSG image using `Fidelity.Data.JSON`.
It is separate from the PSG contract and from Alex. `Inspection.read view`
first calls the shared `Binary.readRevision`, including complete structural
validation, and returns a JSON value. `Inspection.render pretty view` returns
JSON text. There is no JSON-to-PSG decoder or runtime reflection.

`JsonGenerated.fs` contains a typed writer for every named type reachable from
`Revision`. Generate it from the same compiled contract used by the binary
reader:

```sh
dotnet fsi tools/GenerateJson.fsx src/Fidelity.PSG/bin/Release/net10.0/Fidelity.PSG.dll src/Fidelity.PSG.Json/JsonGenerated.fs
```

Record fields retain their declared names. Unions have `$case` and `$fields`;
options and results retain their cases, including nested empty options. Maps
are ordered arrays of `Key`/`Value` entries, preserving structured keys. Tuples,
lists, arrays and sets are arrays in their stored order.

The inspection envelope identifies `fidelity-psg-inspection/1` and the binary
schema/fingerprint. Numeric fields preserve values beyond JSON number precision:

| Stored value | Inspection form |
| --- | --- |
| byte, uint16, int32 | Exact JSON number |
| int64, uint64, bigint | `$type` plus invariant decimal-string `value` |
| decimal | `$type`, invariant `value`, and all four signed int32 `bits` words |
| float64 | `$type`, 16-digit IEEE `bits`, and round-trip descriptive `value` text |
| char | `$type: char-utf16` and exact numeric `codeUnit` |

Floating bits preserve NaN payloads, infinities, subnormals and signed zero.
They are never replaced by JSON null. Decimal words preserve sign and scale,
including signed scaled zero. A hash, schema marker or rendered proof obligation
does not discharge a proof or grant current-source or execution authority.

The explicit inspection process is an independent sink:

```sh
dotnet tools/PsgInspect/bin/Release/net10.0/PsgInspect.dll --input revision.bare --output revision.json --pretty
```

Use `--output -` for stdout. File output requires a new path and refuses
overwrite. The process owns its input mapping and output handle, completes them
before success, and exits nonzero on missing, malformed or inadmissible input.
It uses the bounded image budget of the Composer workspace host. Compiler
publication neither starts this process nor waits for JSON rendering.

The current implementations and checks use .NET. They establish no Fable,
self-hosted Clef or performance acceptance.
