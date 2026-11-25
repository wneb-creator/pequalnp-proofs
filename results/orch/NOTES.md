# L-meta-4970 orchestration notes

Assigned 2026-11-25T15:48:51.075531+00:00

∀ (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' → ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) → PEqualNP.TopForm.IsAO2 (p + l) C → (∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x = decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) → PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0 → (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → (∃ (j : ℕ) (Q : Finset (Fin l)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a, b') ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨ (∃ (j : ℕ) (P : Finset (Fin p)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a', b) ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))) → ∃ S : Finset (Fin (p + l)), (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧ E.card + S.card ≤ C.size + 1

Only root calls desk or commits/pushes. Strategies append findings with their name; Lean experiments under /tmp/oec/pequalnp-pilot-157 or results/orch/lemmas. Final proof must use its own namespace and exact statement.

Allowed project imports: PEqualNP.Defs only (plus Mathlib). No other Outside imports unless already transitively available through Defs.

## status_review — library scan, 2026-11-25

- Updated CONTRIBUTING requires all helper declarations inside the module's own namespace, full target theorem last. Current script and join ownership now agree after upstream update (root verified redirect).
- No direct stronger checked theorem found. The only outside file referencing `TwoColour.tCount` is `L_meta_4791.lean`, which converts arbitrary AO2 circuits to T=0 with factor-six overhead, so cannot give the exact requested bound.
- `L_meta_4990.lean` is the closest complete result: the exact edge-count-plus-vertex-cover bound for C4-free incidence when every AND gate combines a right-pure OR closure with a left-pure OR closure. Its full theorem starts at line 937; it has 900+ lines of potentially reusable structural counting proof. Target hypotheses do not immediately imply its syntactic AND restriction.
- `L_meta_4897.lean` proves the same bound under `ReadK.IsReadK ... 1`; theorem at line 1929. `L_meta_7639.lean` specializes this to a perfect matching lower bound. Target hypotheses do not imply ReadK=1.
- `R_meta_3491_471.lean` proves the broad desired bound conditionally from a cofactor-size-reduction lemma and a smaller core lemma; it contains dependency-support and incidence-elimination infrastructure. `R_meta_3491_473.lean` offers another conditional recursive elimination route.
- `L_meta_7596.lean` bounds the sum of active left and right vertices by size+1 for general fan-in-two circuits computing true on all edges and false on singletons. This is too weak for dense edge sets but useful in matching/forest cases.

## semantic_bound preliminary

Closest existing full bounds require IsReadK1 (L_meta_2237/L_meta_4897), or no dirty AND accepting two distinct reread edges (L_meta_8933). tCount=0 alone gives every OR reach monochromatic, but does not prohibit dirty rectangle ANDs: (x1 OR x2) AND (y1 OR y2). A draft of the immediate no-two-colour and monochromatic-reach lemmas is in lemmas/SemanticNoMixed.lean, awaiting Lean setup.

### status_review — L4990 adaptation detail

The main count in `L_meta_4990.lean` partitions gates into LL (pure OR gates with at least two singleton supports), A (AND gates that OR-reach the output), and PU (OR merge gates above A). `leaf_count` at lines 116–200 gives a general union-DAG leaf bound. `lsum` at 631–651 uses C4-freeness to make the per-center LL sets disjoint. `core` at 737–760 combines these counts.

The adaptation bottleneck is structural: `Good` (453) includes `AH` (450), requiring every AND input to lie in a class `Q` closed through OR gates only (`QH`, 377). `star` (491) uses this to express pair evaluations as products of singleton supports. T=0 does not by itself imply this: nested ANDs and redundant AND branches inside a semantically pure OR witness are permitted. Thus copying L4990 wholesale requires substantial normalization/generalization; copying leaf_count/lsum alone may help another semantic route.

## counting_proof 2026-11-25T15:51:14.908238+00:00
The posted sketch needs a component correction: one degree-4 centre may be served by two disjoint pair ORs, so the witness OR count is only 2 while degree minus 1 is 3. Witness gates need not be used by the output. A proof must balance components with AND/output combining costs.
Drafted StarCentres.lean with C4-free uniqueness of either centre for a support set of size at least 2, semantic uniqueness of embedded pure OR leaf sets, and left-v-right semantic incompatibility. Awaiting toolchain for checks.

## counterexample strategy, initial checks

No semantic loophole identified: exact binary AO/backward model and gate-count size are enforced. T=0 is structural, not semantic: an identity AND x AND x hides a variable from OR-reach, so proofs must allow this at its extra gate cost. Star witnesses may be unused but are charged to size. Empty-edge and zero-input cases are harmless.

Exhaustive C++ search under /tmp/oec/pequalnp-pilot-157/counterexample_small.cpp enumerated T=0 AO circuits below the claimed bound for all C4-free graphs with no isolated-edge component in 1x2, 2x2, and 2x3. Results: 1/8/35 target graphs, at most 1/3/4 gates, 11/10041/1490485 states. No graph-function output below the bound, even without the star-witness condition. This is computational evidence, not a Lean proof.

## semantic_bound pure-OR normalization

Correction: tCount0 constrains syntactic orIn only; hidden identities x AND x can mask semantic singleton supports. Draft SemanticPureOr.lean proves an abstract normalization: if monotone functions f,g have conjunction exactly OR_Q, one operand is already OR_Q. Evaluate at the maximal assignment vanishing on Q, then use monotonicity and singleton acceptance. This handles a semantically pure-OR AND gate, but OR children need not themselves be pure-OR.

### counting_proof semantic extraction 2026-11-25T15:53:31.138014+00:00
For any pure OR_Q witness, consider the complement-Q assignment. A monotone wire is below OR_Q iff it is false there. At a false AND choose a false operand; at a false OR both operands remain false. This bypasses AND gates to extract a pure union network that retains every singleton accepted by the witness. Any retained OR merge with >=2 singleton support belongs to at most one graph centre by C4-freeness. Across all witnesses of one centre, count leaves minus overlap-components. Missing final ledger: the remaining circuit must pay components plus chosen minimum cover minus 1.

Counterexample-side normalization insight: for OR_Q witness evaluate the circuit at the maximal assignment vanishing on Q. At an AND gate false there, choose a false operand; that operand retains every singleton accepted by the AND. OR gates false there have both operands false. This can extract a union network for one witness, but choosing AND operands simultaneously for multiple centres is the obstacle. A semantically pure OR witness can have structural orIn size 1: (x1 AND x1) OR x2. The extra identity AND must be charged in any leaf ledger.

## Toolchain setup (2026-11-25T15:53:56.296786+00:00)
The saved environment had no Lean executable or .lake directory. Installed official Lean 4.36.0 Linux binary under `/tmp/oec/pequalnp-pilot-157/toolchain/lean-4.36.0-linux`. Source `/tmp/oec/pequalnp-pilot-157/toolchain-env.sh` before Lean/Lake/checker commands: it sets PATH and PEQUALNP_REAL_LAKE (needed by tools/bin/lake shim). `lake exe cache get` is downloading pinned Mathlib artifacts; full setup log is `/tmp/oec/pequalnp-pilot-157/cache-get.log`. No tracked setup files changed.

### status_review — independent partial review and projection obstruction

Source review of `StarCentres.lean` and `SemanticNoMixed.lean` found no mathematical issue or hidden statement weakening. These prove helpers only; the full edge-plus-cover budget is still absent. No forbidden syntax, quotes, extra axioms, or admissions observed. On assembly, put imports first and consolidate the helpers under one allowed module namespace. No build run during cache preparation.

The complement-leaf-set projection idea has an allocation obstruction: let u=a AND d, v=b AND e, w=u OR v. Both f=w OR (a OR b) and g=w OR (d OR e) are exact pure OR outputs on disjoint leaf sets. Projection at the complements of {a,b} and {d,e} selects different false children at u,v; the same OR gate w then branches into two leaves for both centers. All four leaves can lie on the same color side, so T=0 does not prevent this. Consequently C4-freeness alone does not make projected branching gates unique; further redundant-branch pruning or an accounting charge to AND overhead is necessary.

Toolchain agent: at 2026-11-25T15:54:54.814713+00:00, `lake exe cache get` completed successfully (exit 0), all 9,117 files downloaded and decompressed. Lean/Lake are ready.

## cofactor_route — preliminary

Checked prior lemmas L_meta_5371 and L_meta_5720 implement false-cofactor compression with strict gate saving for an essential variable. A false-only simplifier can plausibly preserve T=0 because it bypasses ORs only, but the ≥2-leaf star witness property can fail when support shrinks. Deleting left v can make multiple {v,a} witnesses degenerate at a single right centre b; C4-freeness ensures such newly bare edges have distinct left endpoints across different centres, i.e. a star forest, not necessarily a matching.

A reusable exact subcase proof for all edges sharing one centre has been extracted from checked R_meta_3491_473 into lemmas/CofactorStar.lean (pending local compilation). It proves |E|≤C.size from essential-input counting alone, without T=0/star hypotheses. Main cofactor route still needs a degree+1 gate drop or a stronger induction ledger.

### counting_proof checked helper 2026-11-25T15:55:55.243745+00:00
StarCentres.lean compiled successfully using pinned Lean 4.36.0 via lake env lean; no diagnostics. Frozen for root review/push. Its final lemma cover_card_of_star_witnesses gives a vertex cover of size at most number of distinct witness indices.

## counterexample separate operation count check 2026-11-25T15:56:28.920620+00:00

At cofactor_route request, tested the stronger separate claims OR-count >= |E|-1 and AND-count >= minimum vertex-cover size. All 35 eligible C4-free graph functions on 2x3, all T=0 AO circuits through 5 gates, 86,606,101 states: no violation, without imposing the star-witness condition. Source/log: /tmp/oec/pequalnp-pilot-157/counterexample_opcounts.cpp and .log. Pure computational evidence only.

Toolchain agent: initial `lake build PEqualNP.Defs` passed (exit 0, 5,147 jobs; no Mathlib source builds), and `lake build checklemma` passed (exit 0, 5 jobs). Full logs `/tmp/oec/pequalnp-pilot-157/build-defs.log` and `/tmp/oec/pequalnp-pilot-157/build-checklemma.log`. Scratch proofs/checker can run after sourcing the toolchain environment helper.
