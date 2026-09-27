# Rules for work in this repository

These are owner requirements. They apply to every change, by a person or an agent.

## What this library is

`Fidelity.PSG` is the published form of the Program Semantic Graph. The Clef Compiler Service produces a revision. Composer obtains the revision and hands it to Alex. Alex, the backends and every other reader consume it through these types.

## Rules

- The contract declares data and readings of stored fields. It computes no fact about a program. A width, a layout, a representation or a demand is a field the compiler service filled. It is never a function in this library.
- The contract references BAREWire and nothing else. It cannot name a compiler. `build/Contract.targets` refuses both before every compile (PSG001, PSG002).
- The contract opens no file, starts no process and holds no process-wide state (PSG003).
- Every type is immutable. No type holds a checker cell, a deferred computation or a callback.
- A change to a published type changes the contract version in `Revision.fs`. The producer in the clef repository follows in its own changeset.
- A fact a reader lacks is added here as a field and filled by the compiler service. It is never computed by the reader.

## Working rules

- Use .NET tooling, shell tools and `dotnet fsi`. Do not introduce or run Python.
- Do not add a package reference where a Fidelity Framework library covers the need.
- The terms Elaboration and Saturation name phases of the graph's construction in Baker. Do not use them for anything else.
