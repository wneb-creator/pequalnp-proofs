# L-meta-2592: existing lemma routes

Checked repository components (current upstream snapshot):

- `lean/PEqualNP/Outside/L_meta_4725.lean`, 3224 lines: exact binary-floor hypothesis of `R_meta_2592_271`, giving `15 + notCount C ≤ C.size` for Petersen. Helper `petersen_binary_lower` begins at line 3180; its proof combines `least_petersen_six_branches` (line 3135) and `branching_budget`. Thus a candidate at size ≤19 has at most four NOT gates.
- `lean/PEqualNP/Outside/L_meta_8295.lean`, 66 lines: exact `cutLast` hypothesis of `R_meta_2592_318`. Splits any circuit with a NOT as prefix P, one NOT, monotone suffix Q, preserving size and semantics.
- `lean/PEqualNP/Outside/L_meta_7389.lean`, 305 lines: exact normalization hypothesis of `R_meta_2592_408`; legal wire reads, output final, NOT arity ≤1, retains a NOT or strictly shrinks.
- `lean/PEqualNP/Outside/L_meta_7493.lean`, 4140 lines: 9-vertex graph obtained by setting Petersen input 9 false requires at least 14 non-NOT gates.
- `lean/PEqualNP/Outside/L_meta_4550.lean`, 7181 lines: same 9-vertex target requires at least 15 total gates.

All three L2592 reductions are already live. Root cannot submit a fourth under the three-per-step cap. The open hard frontier in the saved desk feed is:

- L-meta-4727: size ≤19 and 1..4 NOT gates cannot compute Petersen.
- L-meta-7391: normalized legal size ≤19 circuit bound.
- L-meta-8297: last-NOT separator with prefix+suffix size ≤18.
- L-meta-6062 (child of L4727): truth-function trace finite bound with at most four complemented generators.
- L-meta-7229 (child of L4727): signed BinaryCircuit lower bound.

Imports are restricted to PEqualNP.Defs and Mathlib; reusable outside helpers must therefore be copied into the new file and renamed under its namespace. No outside imports may be added.

The branch count already proved gives non-NOT gates ≥ n−1+6 =15. Raising it to19 would require four further structural units beyond the current branch-group argument; there is no direct arithmetic closure using the existing bound.

Recorded 2026-11-25T13:50:20.347712+00:00

## Endpoint partial

`results/orch/lemmas/Endpoint.lean` adapts monotone circuit evaluation from L_meta_2416 and proves endpoint exclusion for a monotone prefix whose output is negated. The general terminal-NOT version permits arbitrary NOT input lists, including the empty list. Targeted imports only. Compilation is pending the fresh toolchain/Defs cache; it is not yet claimed checked.

Endpoint compile PASSED at 2026-11-25T14:06:14.150283+00:00: `lake env lean ../results/orch/lemmas/Endpoint.lean`, exit 0. Complete stdout/stderr in scratch endpoint-build-4.out/.err; both empty. 182 lines.
