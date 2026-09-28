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
| `Edges` | The entire edge set: the relations the node kinds imply and every relation Baker recorded |
| `DeclarationRoots`, `ModuleClassifications` | The roots of the design and the members of each module |
| `Platform` | The declared Register and Pointer widths, or the producer's diagnostic where one is undeclared |
| `StaticStringPool` | The placement of source strings |
| `LiteralStorage` | Per reachable string literal, whether its storage was materialized: its pool entry, or the omission relations under which no demanded position reads it |
| `Codata` | Facts settled at the end of saturation: escapes, meets, layouts, carriers, frames |
| `Emission` | Seven projections: ordinary demand, callable, storage, boundary, numeric, memory, spatial |
| `Foreign` | Declared access to storage the program does not own |
| `Demand` | Explicit demand markers and their operands |
| `Obligations`, `ObligationSources`, `ObligationQuery` | Proof obligations, what constrains each, and the design-time query |

## What a reader checks first

`Integrity.check` returns every structural defect of a revision. A reader applies it before it reads anything else, and refuses a revision that has one. Alex applies it at its entry. Composer applies it where a backend receives a catalog. The rules concern the revision as data. They state nothing about the program.

| Rule | Statement | Source |
| --- | --- | --- |
| Header | The revision names the contract version this reader holds. | `Integrity.check` |
| Filing | A node is filed under its own identity. | `Integrity.check` |
| Closure | Every identity named anywhere in the revision is a node the revision holds. | `Integrity.named`, generated |
| Coverage | Every node has its row in the callable value shapes, alias targets and supports. Every reachable node has its source type and its representation. | `Integrity.related` |
| Requirement | Every site a projection declares as required has its row. | `Integrity.related` |
| Reference | A lazy value has its occurrence, an occurrence has its layout, and a lazy thunk declaration is the thunk of a layout. | `Integrity.related` |
| Agreement | The four codata tables that the callable projection republishes hold the same rows in both places. | `Integrity.agreeing` |
| Storage | A literal's storage row that states materialization names a pool entry that lists the literal, and every literal an entry lists has such a row. A row that states no materialization states an established premise with at least one omission. | `Integrity.stored` |
| Incidence | A string byte view or string extent states established participants, one of which names its site in the role Site. The sources of its edge are the nodes of its participants in order. An omitted actual is in the group of an omission site with the same ordinal, and an omission site with one ordinal has exactly one omitted actual. A callee's body is in the group of a callee; a callee's arguments and parameters are in the group of a call in whose group a callee occurs, at the same set of ordinals. | `Integrity.incidence` |

The closure rule examines every position of a revision that holds an identity. The list of positions is generated from the compiled contract by `tools/GenerateIntegrity.fsx` into `src/Fidelity.PSG/IntegrityNamed.fs`. A test compares the file with the generator's output, so a contract type cannot change and leave a table unexamined.

Each rule was measured against revisions the compiler service publishes before it was stated. The Alex repository's `docs/05_Tests.md` records the measurements.

## Layout

| Path | Content |
| --- | --- |
| `src/Fidelity.PSG` | The contract |
| `src/Fidelity.PSG/Integrity.fs` | The structural rules |
| `src/Fidelity.PSG/IntegrityNamed.fs` | Every position that holds an identity. Generated. |
| `tools/GenerateIntegrity.fsx` | Generates the list of positions from the compiled contract |
| `tests/Fidelity.PSG.Tests` | Tests of the empty revision, the structural rules and the generated list |
| `build/Contract.targets` | The rules of the contract, checked before every compile |

## Build

```bash
dotnet build src/Fidelity.PSG/Fidelity.PSG.fsproj
```

BAREWire is expected beside this repository, at `../BAREWire`. A different location is set in `Directory.Build.local.props` through the property `BAREWireProjectPath`.

```bash
dotnet test tests/Fidelity.PSG.Tests/Fidelity.PSG.Tests.fsproj
dotnet fsi tools/GenerateIntegrity.fsx src/Fidelity.PSG/bin/Debug/net10.0/Fidelity.PSG.dll src/Fidelity.PSG/IntegrityNamed.fs
```

The second command is run after any change to a contract type.

## State

A revision is an immutable value in memory. Its binary layout is not built. Node identity is the producer's counter value and is not yet stable across revisions. The Alex repository's `docs` state the open decisions.
