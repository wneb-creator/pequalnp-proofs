# L-meta-5324 orchestration notes

Lease owner: root only. All agents must avoid desk requests.

Exact statement: see /tmp/oec/pequalnp-pilot-49/statement.txt. Allowed project dependency: PEqualNP.Defs.

Work areas: separate files in results/orch/lemmas; final file belongs to root.

Task: bound |covered edges| + |matching subset| by circuit size + twice number of valid wire pairs, for a C4-free bipartite incidence and an AO2 circuit whose AND gates do not force the incidence output.

- 2026-11-24T23:13:21.528011+00:00 [direct_proof] Naive last-gate induction fails at an OR gate used in a safe pair: replacing (a OR b,c) by (a,c),(b,c) costs one extra pair (=2 budget) while removing one gate. Need structural sharing/matching credit. Candidate decomposition: extract a covering family of row/column stars with total sum(S.card+1) at most circuit.size+2*T.card; prove independently that each star contains at most one matching edge, giving H.card+M.card <= that sum.

## Independent dependency and checker review

- Current Defs root imports only Defs modules (no Outside theorem modules); no lemma/theorem declarations found in Defs/*.lean. There is no immediately reusable project cardinality theorem under the permitted import.
- Closest source proof: lean/PEqualNP/Outside/L_meta_5322.lean (364 lines) constructs exactly the dirty-AND residual AO2 circuit and sound wire-pair cover used in L-meta-5324, with residual size + 2*pairs ≤ original size + 1. Its compact W/step/binary/Layout and wire-extension lemmas can be copied into the new helper namespace; importing its module is not allowed.
- Checker invocation for a reduction: node tools/check-lean.mjs <R_meta_5324_k.lean> <original statement.txt> reduce. The theorem must prepend 2–4 closed, nondependent Prop hypotheses to the exact original statement. Conclusion equality is structural, not merely definitional. Children use only Mathlib+Defs, cannot repeat, contain the original statement, be False/decidably false, use text/meta/metadata, or exceed 2000 printed characters. Reduction module contains only its theorem (compiler-generated auxiliaries permitted).
- Updated CONTRIBUTING: proof helpers must be within namespace PEqualNP.Outside.L_meta_5324 (or _aux/subnamespace); namespace/section/end at column zero and named ends. Final theorem is fully qualified, outside helper namespace, and last. Avoid helper simp attributes/instances.
- L-meta-1035 public status confirmed conjecture, seat null, status_at 2026-11-23T19:23:42.563Z, via https://data.pequalnp.com/data/lemma/L-meta-1035.14ea345977c1.json (head snapshot 2026-11-24T23:11:02.647Z). No refutation recorded; public seat null does not establish desk availability.

## Counterexample search 2026-11-24T23:15:00.741370+00:00
- No counterexample in 40,000 random dirty AO2 circuits up to 10 gates on a 2x3 path, C6, C6 with a pendant edge, and C8. Exact full truth tables and all safe pair-cover unions were checked. Equality examples occur.
- Stronger count split from reduction agent passes exhaustive nonredundant semantic circuits through 4 gates: path 29,402 states; C6 127,180; branched C6 488,602. Both |H| <= OR-count+|T| and maximum_matching(H) <= AND-count+|T| were evaluated separately. C8 is still running.
- Search scripts and full logs are under /tmp/oec/pequalnp-pilot-49/counterexample/{search,exhaustive,split}.{py,log}. This is finite computational evidence only, not Lean verification. Every safe pair union was considered using exact finite-set dynamic programming.

- 2026-11-24T23:15:41.098065+00:00 [reduction] Candidate split: H.card <= OR-count(B)+T.card; every accepted matching M has M.card <= AND-count(B)+T.card. Their sum proves posted bound. Counterexample agent validated each inequality exhaustively on <=4-gate semantic circuits over path, C6, branched C6 so far. Uncompiled 2-hypothesis theorem in results/orch/lemmas/reduction.lean; exact original conclusion, no helper declarations. This separates additive edge-count and multiplicative matching-count problems more meaningfully than OR-only normalization, which is essentially equivalent to the whole original via Konig.

- 2026-11-24T23:16:17.097410+00:00 [or_only] OR-only proof strategy: sound wire pairs are bipartite rectangles, C4-free implies stars; group by star center. A nontrivial OR signal with at least two distinct leaf inputs can belong to at most one center. For each center, union of leaves is bounded by its nontrivial OR gates plus pair roots; summing gives |H|+|M| <= gates+2*pairs. Generic binary-DAG leaf count follows by |leaves|+|gates| <= |roots|+2|gates|, using coverage by roots and gate children. Wrote rectangle_is_star, shared_two_leaves_same_center, distinct_centers_overlap_le_one, binary_dag_leaf_count in results/orch/lemmas/or_only.lean (not Lean-checked yet; setup pending). Existing L_meta_1491.lean offers wire semantics, OR reachability, and cone_count2, but final theorem requires least/top-form assumptions.

### Counterexample final finite evidence 2026-11-24T23:17:04.402356+00:00
- Four-gate exhaustive split tests complete: path 29,402; C6 127,180; branched C6 488,602; C8 1,473,225 semantic states, total 2,118,409. Both split inequalities pass.
- Random split testing complete on 4x4, 5x5, 6x6 subgraphs of cyclic Fano incidence; 10,000 circuits each, at most 15 gates; both bounds pass.
- Positive control: removing C4-freeness detects a failure immediately on K2,2 (one shared OR, two pairs cover four edges, violating |H| <= OR+|T|). Two row/column ORs with one pair also violate matching <= AND+|T|.
- No counterexample to L-meta-5324 found. Strongest reduction candidate supported by the checks is independent OR-count edge bound plus AND-count matching bound.

## Static pre-push review and count-source search

- Independent static review PASS of results/orch/lemmas/reduction.lean (69 lines): conclusion matches original statement text exactly after outer whitespace removal; two closed/nondependent children, one fully qualified theorem, no other declarations or forbidden text. Child source lengths normalized 1071/1152 characters; full checker printing still required. Count partition is exact, and restricting the coverage premise from H to M through M⊆H is correct. Under IsAO2, non-OR count equals AND count. Plausibility supported by finite searches in counterexample agent notes, not a proof of children.
- direct.lean and or_only.lean statically pass as partial artifacts only: genuine finite-cardinality/C4-free lemmas, no forbidden tokens/options/attributes, permitted helper namespace. They lack the final target theorem and are not standalone PR proof candidates.
- OR-source candidate: L_meta_2234 qcount (line 356), qfinal (451–535), proving OR-support/star-leaf union bound ≤ relevant OR gates + terminals via disjoint service sets. L_meta_4897 gives edge+cover bound only under ReadK=1. L_meta_4682 generic helpers translate AO circuits into AndCount circuits. No direct matching-count bound found.
- Caution: L_meta_1006 is a checked refutation of general C4-free graph AND-count ≥ minimum vertex-cover (nonbipartite 11-vertex graph, 6 AND versus cover 7), so that broad theorem is unavailable. L_meta_217 proves only thresholds ≤5 by classification.

- 2026-11-24T23:19:06.254424+00:00 [direct_proof] Drafted two pure combinatorial lemmas in results/orch/lemmas/direct.lean: star cover bounds |H|+|M| by sum(|star|+1), and bounds |M| by number of stars. Single narrow dependency Mathlib.Algebra.Order.BigOperators.Group.Finset. First compile attempt hit missing cached .olean only; setup notified.
- [direct_proof] Star-cover extraction may be mathematically equivalent to entire desired bound by Koenig, so prefer genuinely separate OR-edge and AND-matching charges. Library normalizations L_meta_562–566 remove empty/dead/singleton-true AND gates in AndCount model. Reduction agent notes truth-table pair slices alone do not prove AND bound: higher-weight independent inputs in safety are essential.

### Targeted L-meta-1006 concern 2026-11-24T23:20:46.816373+00:00
- L_meta_1006 is a boundary-test refutation, not a circuit computing its full graph function. Its outputs accept only 10 of 16 graph edges at pair inputs.
- Shared gate0 uses vertices {6,7,9,10}; every top that reads it multiplies by disjoint vertices ({2}, {4,5}, {4,8}). Consequently the shared AND contributes only terms of degree at least three, no accepted pair inputs. Deleting it from top operands preserves pair-edge coverage and shrinks outputs, preserving safety. Natural two-color copies retain this fact and leave star top pairs.
- Exact targeted enumeration: 1328 bipartite induced vertex restrictions, all subsets of the five top terms, no matching-budget failure. Largest restricted matching 4. Full graph double-cover matching 11; accepted-pair double-cover matching 10.
- Naive lift x_v -> x_vL OR x_vR, even gated by nonempty left and right supports, is unsafe: {0L,9L,1R} triggers source edge0--9 but contains no double-cover graph edge.
- Script and full output: /tmp/oec/pequalnp-pilot-49/counterexample/target1006.py and target1006.log. This excludes this specific refutation transfer, not every conceivable transformed counterexample.

- 2026-11-24T23:21:07.971705+00:00 [or_only] Added safe_pair_covers_at_most_one_matching and safe_pair_family_matching_bound. These prove the complete abstract rectangle-support matching bound M.card <= T.card; remaining OR-only bridge identifies circuit wire singleton supports. All six lemmas use only narrow Mathlib Finset imports; pending Lean setup. Existing L_meta_2234 qcount/qfinal already prove the OR leaf sharing count exactly. No counterexample discovered.

- 2026-11-24T23:21:33.003576+00:00 [direct_proof] COMPILED results/orch/lemmas/direct.lean successfully, exit 0, no diagnostics. Both star-cover lemmas are checked by local Lean 4.36.0; complete stdout/stderr file /tmp/oec/pequalnp-pilot-49/direct-lean.log is empty on success. Root notified for immediate reviewed partial push.

- 2026-11-24T23:21:55.209076+00:00 [or_only] SUCCESS: all six lemmas in or_only.lean compiled with pinned Lean 4.36.0; exit 0, no diagnostics. Full successful stdout/stderr at /tmp/oec/pequalnp-pilot-49/or_only/compile-002.log (empty). Narrow imports are Finset.Card, Finset.Prod, Algebra.Order.BigOperators.Group.Finset. No Defs dependencies or full Mathlib used.

### OR-side restricted-soundness test 2026-11-24T23:26:23.114515+00:00
- At reduction agent request, tested edge_count <= OR_count + terminal_pair_count with terminal soundness checked only on assignments of Hamming weight <= 2. No failure on all nonredundant circuits through four gates for path/C6: 156,582 states keeping dirty ANDs, 362,827 states dropping dirtiness. Diagonal terminal pairs were included. This is finite evidence, not a theorem.
- Script and full log: counterexample/weak_soundness.py and weak_soundness.log under job scratch.

- 2026-11-24T23:26:54.840607+00:00 [reduction] Continued direct additive-bound research. OR-only qcount/qfinal in L_meta_2234 charges nontrivial OR support to a unique star center by C4-freeness. For general dirty AO circuits, an edge proof through an OR gate has a residual monomial context of size0,1,2; size1 contexts are star centers, and an OR with >=2 singleton supports cannot serve two distinct such centers. Remaining residual edge terms (OR gates with <=1 singleton support and dirty-AND descendants) still lack a valid global charging argument. Zero-OR base case is straightforward conceptually: AND-only wires preserve intersection of assignments, so a safe pair cannot accept two different edge inputs (their intersection contains at most one vertex).

- 2026-11-24T23:26:54.840623+00:00 [reduction] Weak soundness experiment requested from counterexample agent: additive bound also passes path/C6 <=4-gate circuits when soundness is tested only at inputs of weight<=2, with156582 dirty-restricted and362827 unrestricted semantic states. This is finite evidence for a possible pair-level invariant, not a proof.

### Hall localization and unlimited-AND tests 2026-11-24T23:28:43.009152+00:00
- Hall matching-resource condition passes all645,184 states through four gates on path/C6/branched C6: for every matching S, |S| <= number of internal AND gates active on any S edge + minimum number of globally safe terminal pairs covering S. Exact AND-function identities retained. Scripts: counterexample/hall.py and hall.log.
- OR-side stronger finite model uses only weight<=2 truth tables, drops dirty-AND assumption, and closes signal pools under arbitrary free AND gates. Enumerated all pools through3 OR gates: path23,718 total states, C6 138,667 total states; no edge-bound failure.
- For C6 the only untested possible failure after those OR budgets was all6 edges with1 terminal and4 ORs. Exhaustively checked final signal g AND (u OR v) over all136,023 depth3 meet-closures,137,271 contexts; none succeeds. Higher OR budgets pay all edges trivially. Thus this finite model excludes any edge-bound counterexample on those two selected graphs, with no bound on AND count. All statements here are Python finite verification, not Lean proofs.
- Free-AND scripts/logs: counterexample/free_and.py, free_and_three.log, free_and_last.py, free_and_last.log. Signals false on every singleton and every E-edge can be omitted: replacing them by false shrinks functions and preserves the relevant assignments.

- 2026-11-24T23:29:16.277496+00:00 [or_only] SUCCESS: or_semantics.lean (254 lines) compiles with pinned Lean 4.36.0, exit 0 and no diagnostics. Main partial lemma or_circuit_matching_bound proves M.card <= T.card for actual OR-only Circuit.wires, under C4-free E, safe wire pairs T, coverage of matching M, and row/column matching injectivity. Wire OR-homomorphism and pair/singleton decomposition proved by gate-list induction. This solves the zero-AND special case of the matching child, with no fan-in/read-back hypotheses. Full target still open.
