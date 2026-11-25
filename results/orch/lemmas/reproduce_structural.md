# Structural checkpoint reproduction

These are partial research results. None proves the posted statement for L-meta-2592, L-meta-2583, or L-meta-2590. Ordinary Lean compilation and an accepted posted-gap checker result are different claims; the named-file checker returned `REJECTED (no-theorem)`.

The audit compared the tracked archive bytes with the frozen scratch sources. The principal frozen structural sources audited for this note match exactly. Every local module named on an import line of any archived `.lean` file in `checked/`, `checked2583/`, and `checked2590/` has a corresponding archived source. No source prerequisite is missing from those import graphs. Generated `.olean` files are intentionally not needed for preservation and must be rebuilt.

## L-meta-2592

Directory `results/orch/lemmas/checked/`:

- Compile `Partial16.lean`, then `ProjectionChecked.lean`, then `Bound17.lean` in this order. Each was checked and exported separately. They establish at least17 non-NOT gates, hence at most2 NOT gates when total size is at most19.
- `FirstNonOrBound.lean` imports `Bound17`; `NormalizeMono.lean` imports `Partial16`. Both prerequisites are archived.
- `Full17.lean` is the independently reviewed source concatenation of the three principal modules, SHA256 `8aee8f9d4ebf20b5ca7a71759822936d9d68c57527b9b2417a239946b54fd7c5`. **This concatenation was not separately compiled.** Its modular components were compiled; do not report a standalone build for Full17.
- `StructuralWitness.lean` preserves the earlier503-line named target whose named build passed. It is another partial checkpoint, not the complete17-bound concatenation.

The Partial16 certificate took about14 minutes to export on this container. Its table proofs can need substantial CPU and memory; subsequent modules use its cached object. Complete logs include `validation/partial16.*`, `validation/projection-checked.*`, `validation/bound17.*`, and `validation/first-non-or-bound.*`.

## L-meta-2583

Directory `results/orch/lemmas/checked2583/`:

- `CostEquivalence.lean` is a **separately compiled standalone** file importing only `PEqualNP.Defs`. SHA256 `53295d611325a8fa7f2c63887260350158d532a2a7582fc419a4363ef3240b9e`. It proves the conditional equivalence between the desired read-one replacement and the numerical bound `N*(q+2) <= C.size+1`; the unrestricted numerical bound remains unproved.
- The scratch intermediates `PlaneReadOneFloor.lean`, `StarConstructionFixed.lean`, and `NormalizationEquivalence.lean` are not separately archived. Their proofs are included in the compiled standalone CostEquivalence file; they are not missing prerequisites. The archived `ReadOneCost.lean` is an earlier independently checked component, not a required import of CostEquivalence.
- `TwoRectangles.lean` independently compiles from Defs. It supplies a restricted semantic star replacement, preserving edge inputs and staying below the target; it does not prove an unrestricted circuit-cost bound.
- For other modular geometry: compile `PlaneGeometry`, then `MixedCoverGap`, then `RectangleCenters`. All sources are present.
- `FinalPartial.lean` is the actual7379-line final named-file snapshot. Unlike Full17, this combined file **was built as the named target**. SHA256 `01bfe8716581cbd0fb80b0e7d9bd1c56cafe3b863659985fcd616756c43ddb65`; nine-source provenance is in `validation/2583-final-combined-manifest.json`. Its build passed, and its checker rejected the absent final theorem. The earlier four-component manifest describes a superseded intermediate composition.

Compile logs: `validation/2583-cost-equivalence.*`, `validation/2583-two-rectangles.*`, `validation/2583-build-final-combined.*`, and `validation/2583-checker-final-combined.*`.

## L-meta-2590

Directory `results/orch/lemmas/checked2590/`:

1. `PetersenSurplus.lean`: generic strict-live DAG normalization and surplus framework, extracted from L971.
2. `PetersenGeometry.lean`: exact Petersen adjacency, independent-set bound4, surplus budget10 under size19, and private-position lemmas.
3. `PetersenOrbits.lean`: five nonempty independent-set representatives plus the empty case, using17 verified automorphisms.
4. `PetersenReduction.lean`: any hypothetical size19 monotone Petersen circuit yields a correct strict-live DAG in one of those six cases.

Each module compiled and emitted an object, with empty complete logs `validation/2590-petersen-{surplus,geometry,orbits,reduction}.{stdout,stderr}`. **No standalone concatenation of this structural chain was built.** `AllEligible.lean` and `FourOrbitCodes.lean` import PetersenGeometry; they provide checked conditional counts, not contradictions. The separately archived `drafts2590/FourOrbitLowSharing.UNCOMPILED.lean.txt` is explicitly uncompiled and must not be counted as a checked result.

The six-case contradiction remains open. Abstract consumption-code constraints admit models; actual gate order or stronger semantic/cost arguments are still required.

## Rebuilding modular chains

Use the repository-pinned Lean `leanprover/lean4:v4.36.0` and pinned Mathlib manifest. From `lean/`, obtain the existing cache with `lake exe cache get` and build `PEqualNP.Defs`; do not run `lake update` or rebuild Mathlib from source. Put generated objects and diagnostics in a scratch directory, not in the archive.

For example, after creating `/tmp/oec/pequalnp-pilot-99/reproduce2590`, run from the repository's `lean/` directory:

```sh
lake env bash -c '
  proof_source="$1"
  proof_output="$2"
  export LEAN_PATH="${proof_output}:$LEAN_PATH"
  for module in PetersenSurplus PetersenGeometry PetersenOrbits PetersenReduction; do
    lean -R "$proof_source" -o "$proof_output/${module}.olean" "$proof_source/${module}.lean" > "$proof_output/${module}.stdout" 2> "$proof_output/${module}.stderr" || exit "$?"
  done
' _ /workspace/pequalnp-proofs/results/orch/lemmas/checked2590 /tmp/oec/pequalnp-pilot-99/reproduce2590
```

Use the corresponding source directory and dependency order for other modular chains. Standalone combined files duplicate declarations from their components: compile a combined file independently, and do not import both it and those component modules into one environment. Archive paths differ from original scratch paths printed in the logs; this does not alter source content or module names.

The scratch-module imports and helper-only statements are suitable for reproducibility, not automatically for the project's one-file PR format. A future complete submission must inline necessary helpers, retain only allowed imports, pass the plain-file guard, and prove the exact then-posted statement.
