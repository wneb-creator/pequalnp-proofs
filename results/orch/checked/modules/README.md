# Checked scratch modules

These files preserve separately compiled research components. Their adjacent
logs, metadata and recorded hashes identify the checked snapshots. They are
not a complete proof of the posted 51-OR statement.

## Canonical compiler dependencies

`CanonicalCompilerDefs.lean` (SHA256
`74ee0fdf3addcb7caf0f166bef55641ba4b7f98fb69d397bdf4f38cceed46758`)
is the **superseded inductive prototype**. Preserve it as historical source;
do not use it to build the later compiler proofs or flatten it into a final
submission.

The later compiler proofs use `CanonicalCompilerAliasDefs.lean` (SHA256
`dc9fc17b0b48ae7caa20f941e7a9949547133a90950b49f655a7b12b4556ccb5`).
Its `Program n k` definition uses existing lists, finite indices and tuples.
For a scratch build, copy this snapshot into a separate build directory under
the module filename **CanonicalCompilerDefs.lean** and compile that module
before the dependent proofs. The archival filename distinguishes it from the
earlier prototype; it is not the module name expected by their imports.

Use these additional scratch module mappings:

| Module name | Archived source |
| --- | --- |
| `CanonicalCompilerStructure` | `../canonical-compiler-structure.lean` |
| `CanonicalCompilerSemantics` | `../canonical-compiler-semantics.lean` |
| `CanonicalCompilerMasks` | `../canonical-compiler-mask-certificates.lean` |
| `CanonicalCompilerSamples` | `../canonical-compiler-samples.lean` |

The mask-certificates snapshot already contains the definitions and lemmas
from `../canonical-compiler-mask-bridge.lean`; include that shared code once.
The two-OR cycle control is a small compiler test, not a counterexample to
L-meta-1896. Sources under `../../compiler-prepared/` remain prepared unless a
separate checked snapshot and successful log explicitly say otherwise.

## Final single-file assembly

A final proof or refutation must flatten the required current definitions and
proofs into the one named submission file, importing only the posted project
dependency `PEqualNP.Defs` and any permitted Mathlib imports. Scratch-module
imports do not belong in that file. Deduplicate shared definitions and use the
permitted helper namespaces. Retain no superseded custom inductive prototype,
forbidden proof mechanisms, prohibited namespace text, string literals, or
disallowed attributes or options. Build and run the repository checker on the
assembled final file; component checks alone do not establish acceptance.
