# Late-witness compiler pipeline for L-meta-3773

No circuit with 63 gates has been found. The included generated Lean file proves
only the 64-gate positive control. It passed a fresh complete Lean check. The
generator is ready to turn a future validated 63-gate circuit into a candidate
for the exact posted theorem; that candidate would still require a new Lean
build and the repository checker before submission.

The generator defaults to at most 63 gates, checks forward operands and the
last output, normalizes only commuted allowed first gates, and independently
replays all 808 original test rows before writing. It pins the posted statement,
the checked fast template, and the input words by SHA256. Default opcodes are
0=AND and 1=OR; --and-is-one explicitly reverses that convention. Output paths
must differ from every input and the generator itself.

In a disposable copy of this directory, run:

    python3 geometry-meta3773-witness-tests.py

The ten tests include seven rejection cases and three equivalent successful
64-gate generations. Rejected candidates leave existing output bytes unchanged.
The successful generated file has SHA256
888becf4f2bb9299d003b4ffde38f484cd9cb39a55bd4f632031160b7e4f5d9a.

For a future candidate, run:

    python3 geometry-meta3773-witness-generate.py --candidate candidate.json --output L_meta_3773.lean

Use --control64 only for the auxiliary positive control. The exact posted
statement is preserved in meta3773-statement.txt; this archive makes no claim
that the posted 63-gate existential has been proved or refuted. The complete
build log and source-bound runner status are retained. No local repository
checker verdict is claimed for this auxiliary 64-gate theorem.
