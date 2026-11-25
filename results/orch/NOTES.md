# L-meta-4675 orchestration notes

Only root holds and renews the lease. Each agent appends findings in its own section; proof attempts use separate files in results/orch/lemmas. Final proof goes only in the desk-named Lean file.

## Posted statement

```lean
∀ (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
  PEqualNP.TopForm.IsAO2 (p + l) C →
  (∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) →
  PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0 →
  ∃ S : Finset (Fin (p + l)),
    (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
    E.card + S.card ≤ C.size + 1
```

## Lemma search (lemma_search agent)

- Current upstream has no checked proof using `TwoColour.tCount` except `L_meta_4791`, the factor-six normalizer from the desk sketch. Its public theorem is at line 1413; helper proof spans the file. No direct reuse closes L-meta-4675.
- `lean/PEqualNP/Outside/L_meta_4897.lean:1929` proves the desired bipartite cover bound under `ReadK.IsReadK (p+l) C 1`, with separate left/right cover finsets. About 1960 lines; first 1800 are copied graph machinery from L-meta-2237. Helpers include wire recursion, OR reach, read-vector normalization, support budgets, and a bipartite graph translation. We may copy/adapt helpers into our file but cannot import Outside modules because desk permits only Defs.
- `L_meta_2237.lean:1877` and `L_meta_6369.lean:1394` prove the graph version under IsReadK 1.
- `L_meta_2235.lean:1769` proves the same budget on just those edges with a read-once proof tree. `L_meta_3706.lean:1515` expresses this as a surcharge for reread edges.
- `L_meta_8933.lean:1428` (`main_bound`) permits junk AND gates provided each is true on at most one distinct reread edge. Its `repaired_graph` at 1354 replaces junk ANDs with selected edge conjunctions at equal size; clean graph budget applies afterward. Could adapt if our no-mixed-OR condition forces a suitable replacement theorem, but not established.
- `L_meta_7653.lean:610` proves edge-plus-matching budget for circuits with all OR gates before all AND gates. It may give a simpler special case.
- Important failed shortcut: tCount=0 does not imply IsReadK 1 for the original circuit: `(x AND x) AND y` has no OR gates but repeats x. A size-preserving or size-decreasing normalization is required.
- Definitions: `Defs/TopForm.lean` defines exact-two-input monotone backward circuits and `orIn`; `Defs/TwoColour.lean` defines `tCount` as card of OR gates whose OR-only input reach has both colors. AND nodes reset that reach to empty.

## Counterexample strategy (started 2026-11-25 17:09 UTC)

- Actual `IsAO2` forces two earlier operands and only AND/OR; no arity/index loophole found. Empty side/edge cases satisfy the conclusion with the empty cover.
- `tCount = 0` is syntactic, not semantic: OR-reach stops at every AND, including `x AND x`. Identity buffers can hide a variable color, so semantic singleton-color arguments are invalid without extra proof.
- Set up independent exact MILP synthesis using SciPy/HiGHS, with binary gate choices, truth on edge minterms and maximal independent sets, and exact two-bit OR-reach tracking. Complete logs are under `/tmp/oec/pequalnp-pilot-164/*-milp.stdout` and `.stderr`. No Lean claim follows solely from this numerical search.
- Four-vertex three-edge path: 3-gate synthesis is infeasible; 4-gate known-optimal recovery is a solver sanity check. Six-cycle search targets 7 gates against claimed minimum 8.
- Research read 2026-11-25: https://pequalnp.com/papers/note-1 section 7 identifies superlinear general monotone edge-function lower bounds as open, while C4-free bounds are known for formulas/restricted circuit models. Together with checked `L_meta_4791` (sixfold normalization), this confirms the assigned step is a substantive open lower-bound problem, not just a library lookup.

### Clean-circuit framework (lemma_search, 2026-11-25)

`results/orch/lemmas/Reuse.lean` now copies the clean graph-budget proof from L-meta-8933 and supplies direct bipartite translation. Lemma `PEqualNP.Outside.L_meta_4675.Reuse.clean_bound` derives the exact posted conclusion from no rectangle, IsAO2, and computes, plus an extra hypothesis that every actual AND gate implies the output on every assignment. It does not use tCount=0. No unavailable imports or unproved placeholders. Compiler pending toolchain setup.

## Algebraic strategy

- Pair-assignment abstraction gives each gate a point-singleton set, line-singleton set, and accepted-pair set. OR is union; AND is intersection. This does not directly yield a size potential because intermediate gates can accept nonedges that later AND gates remove.
- The hypothesis `tCount = 0` is syntactic, not semantic: OR of `x AND x` and `y AND y` has empty OR-reach even when x and y have different colours. Treating every gate as semantically monochromatic would therefore be unsound.
- Checked upstream L_meta_4791 normalizes every AO2 circuit false on singleton inputs into a tCount=0 circuit of at most six times the size. The assigned lower bound would consequently prove general monotone lower bounds linear in |E| for C4-free bipartite edge functions. The site paper https://pequalnp.com/papers/note-1, section 7, read 2026-11-25, describes superlinear lower bounds for explicit graph edge functions as open in its cited literature. This is an explanation of the hard bridge, not a disproof.
- `results/orch/lemmas/Algebraic.lean` contains the structural agent’s rectangle helpers plus two new finite-family statements (currently uncompiled): `rectangle_family_cover` and `rectangle_cover_bound`. A finite rectangle cover of E gives a vertex cover S with E.card + S.card bounded by the sum of the rectangle side sizes. Induction adds one star centre at a time.
- Remaining bridge: extract such a rectangle cover from C with total side size at most C.size + 1, handling shared gates, junk ANDs, and masked mixed-colour literals.

## Structural proof agent

- Exact definitions checked after upstream fast-forward. `tCount=0` forbids two colours only in syntactic OR-only reach; AND gates stop reach. It does not imply actual singleton support monochromatic (identity AND gates hide both colours), nor READ-1.
- Wrote `lemmas/Structural.lean`: no-C4 rectangle is a star; nonempty rectangle has a singleton side; its number of edges equals sum of side sizes minus one; one center covers the rectangle. Pending compiler setup. Algebraic agent is extending to finite rectangle families.
- A size-preserving clean-circuit normalization would close the theorem using reuse agent's `clean_bound`. This remains the main unproved part. P4 witness from counterexample agent shows top-form and READ-1 cannot be assumed even for optimal tCount-zero circuits, though all its ANDs are clean.
- Research read 2026-11-25: https://pequalnp.com/papers/note-1 section 7 reports that a superlinear lower bound for general monotone circuits of an explicit graph edge function is open (Jukna TR05-021 Problem24); |E|/2 is known for multilinear/arithmetic models. Combined with checked factor-six normalizer L4791, this task implies a substantive new superlinear bound, so the normalization obstacle is genuine research rather than an overlooked library lemma.

### Clean-circuit framework validation

`Reuse.lean` compiled successfully with pinned Lean on 2026-11-25T17:14:31.753179+00:00. Exit code 0; only style warnings. Exact conclusion proved under the extra all-AND-below-output hypothesis. This is a checked partial lemma, not L-meta-4675 itself. Full diagnostics: `/tmp/oec/pequalnp-pilot-164/reuse-build-001.stdout` and `.stderr`.

Algebraic update 2026-11-25T17:14:37.415792+00:00: `Algebraic.lean` compiled successfully (exit 0) with only `import PEqualNP.Defs`. Both finite rectangle-family lemmas and all five copied Structural helper lemmas are checked by Lean. Only warning is deprecated `push_neg` in the copied structural proof. Full diagnostic files: `/tmp/oec/pequalnp-pilot-164/algebraic-check.stdout` and `.stderr`.
