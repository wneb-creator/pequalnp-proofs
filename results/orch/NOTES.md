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

### Counterexample strategy: checked P4 sanity witness

`results/orch/lemmas/Counterexample.lean` compiled with pinned Lean, exit 0, stdout/stderr empty. It proves the 4-gate absorption circuit `by; a OR by; x OR y; final AND` satisfies all concrete gap hypotheses and reaches the claimed bound. Thus a valid tight circuit can have AND output and a clean AND strictly beneath another AND. This is not a refutation. A 4-gate P4 circuit containing a dirty AND was numerically infeasible in the MILP. C6 7-gate and forced-dirty 8-gate searches are ongoing.

### Structural checked results

- All five rectangle helpers compiled unchanged as part of Algebraic.lean (Defs-only imports).
- StructuralExamples.lean compiled with exit 0, no diagnostics at 17:16 UTC. It records the C4-free P4 function on points a,b and lines x,y, computed as `(a OR (b AND y)) AND (x OR y)`. It has tCount zero but is not READ-1 (edge by repeats y). The buffered version additionally has a dirty AND accepting two distinct output edges without READ-1 proofs. These are counterexamples to attempted bridge hypotheses, not to the posted statement.
- First-dirty-gate analysis: before the first dirty AND, each operand has a one-colour singleton support equal to OR-reach, plus clean edge terms. Disjoint same-colour pure supports give a gate false on all edge inputs and can be removed. Hard cases are overlapping same-colour supports (intersection) and opposite-colour rectangles containing nonedges (downstream filtering).

### Counterexample search programs

- `results/orch/lemmas/CircuitSearchZ3.py`: ctypes interface to already installed Z3 4.13.3, no downloaded dependencies. Exact bounded AO2 synthesis with two-bit syntactic OR-reach state; samples are all edge assignments and all maximal independent sets. Every found witness is rechecked on the complete Boolean truth table and syntactic OR reach by independent Python evaluation.
- `results/orch/lemmas/CircuitSearchMILP.py`: independent SciPy/HiGHS Boolean MILP encoding, same target semantics. Numerical infeasibility is exploratory evidence only, never a Lean claim.
- Z3 sanity: P4 at3 gates UNSAT (0.12s), at4 gates SAT (0.09s) with full truth-table validation.
- Running C6 at7 gates and forced-dirty C6 at8 gates, both600s; Fano at26 gates,3600s and2048MiB cap. Fano has21 edges, cover number7,58 truth samples (21 edge minterms,37 maximal independent inputs), and the posted conclusion would require27 gates.

C6 at7 gates: Z3 returned UNSAT in26.13s. This is an untrusted solver result, not Lean-checked. Original MILP C6 searches were stopped after the Z3 backend demonstrated much better performance; only3 CPUs are available, so continuing duplicate MILP searches would compete with the Fano search. Complete logs retained.

### Restricted normalization (lemma_search)

Two new checked partials:
- `Normalize.lean`, namespace `L_meta_4675.Normalize`, proves `erase_edge_inactive_dirty`: if every dirty AND is false on every actual graph-edge pair input, all dirty ANDs can be replaced by a fixed actual edge conjunction. The resulting AO2 circuit has exactly the same size, computes the same graph function, and every AND is below the graph function. Edge minterms retain acceptance because replacement only increases values there; graph-false assignments stay rejected because replacement only decreases values there. Proof includes monotonicity needed to lift minterm acceptance to arbitrary assignments.
- `Fragment.lean`, namespace `L_meta_4675.Fragment`, proves that two disjoint input sets of the same colour cannot both hit an opposite-colour pair. Consequently `(A-hit or X) and (B-hit or Y)` implies `X or Y` on every such pair. This is the semantic step for removing same-colour-disjoint earliest dirty gates with earlier clean fragments. The equal-cost rewiring of shared OR regions remains unproved.

Both compile with pinned Lean, exit 0, empty stdout/stderr on 2026-11-25T17:18:30.484739+00:00. Complete logs `normalize-build-002.stdout/.stderr` and `fragment-build-002.stdout/.stderr` under job scratch. These are restricted partial results, not the full gap.

### OR-reach invariance (lemma_search)

`OrInvariant.lean` proves that identical gate operations and identical OR input lists, expressed by `List.Forall₂ SameOr`, preserve `orSets`, `OrReaches`, `orIn`, `IsTwoColour`, and `tCount`. Therefore arbitrary rewiring of AND operands leaves the tCount hypothesis unchanged. Compiled 2026-11-25T17:20:43.494340+00:00, exit 0, empty diagnostics. Full logs `or-invariant-build-002.stdout/.stderr` in scratch.

### Counterexample search update (2026-11-25 17:20 UTC)

- C6 at8 gates with a required dirty AND: original Z3 encoding UNSAT in157.60s; optimized encoding UNSAT in9.58s. Together with C6 k7 UNSAT, this is numerical evidence that an optimal C6 circuit in the restricted class has no dirty AND. Not a Lean proof.
- Optimized encoding adds adjacent-independent-gate ordering, excludes duplicate gates and identity ORs, and normalizes the first gate by graph automorphisms for C6/Fano. Any SAT witness still undergoes unrestricted full truth-table and reach validation.
- All scripts now validate graph dimensions and C4-freeness, gate indices/operations, full truth table, syntactic coloring, and the required dirty AND on a full independent input.
- Exhaustive Python graph census: the12 labelled C4-free4x4 graphs with9 edges containing the fixed diagonal matching form exactly one bipartition-preserving isomorphism class: theta8. Therefore fixed theta8 at11 gates is the same counterexample family as an unknown graph search under those conditions.
- Original Fano search stopped after roughly3min to reserve one of3 CPUs for Lean work. Optimized Fano26 now runs with3600s/2048MiB limits; theta8k11 runs with600s/2048MiB.

### Composed restricted lower bound (lemma_search)

`Combined.lean` compiles on 2026-11-25T17:23:37.663582+00:00 with the immutable Normalize, OrInvariant, Reuse bodies and two additional wrappers. `Normalize.repair_tCount` proves the repair construction preserves tCount exactly. `Restricted.inactive_dirty_bound` proves the exact posted conclusion under the original hypotheses plus an extra explicit assumption that every dirty AND is false on every actual graph-edge pair input. This composes normalization with the clean bound. The original tCount hypothesis is unused in this stronger-restriction result. `CombinedWrappers.txt` holds just the new suffix for root integration. Full successful logs: `combined-build-003.stdout/.stderr` under scratch.

### Checked local reader pricing

`ReaderPricing.lean` and `ReaderPricingExtended.lean` compile with Defs-only imports, exit0 and no diagnostics. For a pure dirty rectangle A(point)×B(line), a clean reader `(g OR P_lines) AND Q_points` has direct terms Q×P and possible new terms (A∩Q)×(B\P). Under |A|,|B|,|Q|≥2 and P nonempty, with explicit row/base adjacency and triple-cleanliness hypotheses, every new pair is both a complete row and complete column of A×B. C4-freeness makes that common corner unique. `readers_share_at_most_one_novel_edge` shows the UNION across any finite family of such readers still has cardinality at most1. This prices nonstar P4 readers relative to their direct terms, avoiding the false claim that the full reader edge set must be a star.

The remaining region obstacle is nested dirty ANDs or clean readers whose both operands contain only dirty flags. Multiple pure dirty flags joined only by OR can each be priced independently by monotonicity (algebraic agent extending). No arbitrary-circuit extraction/counting theorem yet.
