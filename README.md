# Fidelity.PSG

The published form of the Program Semantic Graph (PSG) of the Clef language.

The Clef Compiler Service builds the graph, elaborates it and saturates it. When it is done, it publishes one revision. A revision is an immutable value that holds every fact about the program that a later stage may read. This library declares the types of that value.

## Who produces a revision

The Clef Compiler Service, in the clef repository:

| File | Role |
| --- | --- |
| `src/Compiler/PSGSaturation/Publication/RevisionPublication.fs` | Assembles a revision. It is the only place a graph leaves the compiler service. |
| `src/Compiler/PSGSaturation/Publication/RevisionMappers.fs` | Copies each published value field by field. Generated. |
| `tools/PSGContract/GenerateMappers.fsx` | Generates the mappers. It stops with a named difference when a published type and its counterpart in the compiler service disagree on a case or a field. |

## Who reads a revision

| Reader | Repository | Use |
| --- | --- | --- |
| Composer | Composer | Obtains the revision from the compiler service and hands it to Alex. Its backends read it. |
| Alex | Alex | Witnesses the revision and emits MLIR. The revision is the only description of a program Alex receives. |

## What a revision holds

| Part | Content |
| --- | --- |
| `Header` | The contract version and the producer |
| `Nodes` | Every node, with its kind, frozen type, children, range and obligation anchors |
| `DeclarationRoots`, `ModuleClassifications` | The roots of the design and the members of each module |
| `Platform` | The declared Register and Pointer widths, or the producer's diagnostic where one is undeclared |
| `StaticStringPool` | The placement of source strings |
| `Codata` | Facts settled at the end of saturation: escapes, meets, layouts, carriers, frames |
| `Emission` | Seven projections: ordinary demand, callable, storage, boundary, numeric, memory, spatial |
| `Foreign` | Declared access to storage the program does not own |
| `Demand` | Explicit demand markers and their operands |
| `Obligations`, `ObligationSources`, `ObligationQuery` | Proof obligations, what constrains each, and the design-time query |

## Layout

| Path | Content |
| --- | --- |
| `src/Fidelity.PSG` | The contract |
| `build/Contract.targets` | The rules of the contract, checked before every compile |

## Build

```bash
dotnet build src/Fidelity.PSG/Fidelity.PSG.fsproj
```

BAREWire is expected beside this repository, at `../BAREWire`. A different location is set in `Directory.Build.local.props` through the property `BAREWireProjectPath`.

## State

A revision is an immutable value in memory. Its binary layout is not built. Node identity is the producer's counter value and is not yet stable across revisions. The Alex repository's `docs` state the open decisions.
