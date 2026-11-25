# L-meta-2592 orchestration notes

Assigned hard step: Petersen edge function cannot be computed with at most 19 fan-in-two gates when at least one gate is NOT. Allowed project module: PEqualNP.Defs. Reductions are open but 3 are already live. Only the primary manages the lease and git mutations.

Strategy findings will be appended below.

## Independent checker/format review (status_1035, 2026-11-25)

- Local verifier: `node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_2592.lean /tmp/oec/pequalnp-pilot-107/statement.txt check`; use `refute` for the exact negation. It checks the pinned build configuration, rebuilds verifier and target, rechecks project declarations, checks standard axioms, and compares the target statement.
- The separate static guard is necessary: `node .github/scripts/outside-guard.mjs imports <file> <imports.json> <file> check`, with JSON allowed modules `["PEqualNP.Defs"]`. Guard code explicitly excludes `bv_decide` as well as native reduction, strings, forbidden names even in comments, custom syntax, and options except the four scoped limits.
- Helpers belong in `namespace PEqualNP.Outside.L_meta_2592` (or `_aux`), ending with its full name. Only the top-level full-name theorem comes last. Avoid helper instances and global simp lemmas.
- Desk reports three live reductions, and upstream contains R_meta_2592_271, R_meta_2592_318, R_meta_2592_408. No fourth reduction should be submitted while the cap remains full.
- Single-file PR plan: checkpoint partials and results on the required branch as authorized, retaining their commit SHAs. Before final PR, remove only branch-added scratch/results in a cleanup commit. They remain preserved in remote commit history, while the net PR diff adds exactly the one target file. No history rewrite or second branch is needed.
- Statement sanity: the 15-edge formula is the Petersen graph; circuit size counts all gates including ignored/unused NOT gates, invalid wire indices read false, and NOT uses only its first input. FanInTwo restricts operations to AND/OR/NOT and input-list length <= 2. No malformed type or contradictory premise is apparent.

## Semantics (2026-11-25T14:04:02.800566+00:00)

- `Circuit.wires` is a sequential fold; missing/future references read false. `FanInTwo` limits operations to AND/OR/NOT and input-list length to two. NOT ignores its second input. Empty AND/NOT gates evaluate true; empty OR evaluates false. No semantic loophole found.
- Draft `results/orch/lemmas/semantics_normalize.lean`: cap every input/output reference by `n + C.size`. This preserves every intermediate state, gate count, fan-in, NOT occurrence, and final value. All references then lie in a finite range (`0..29` here). Complete proof text; pending Lean availability.

## 2026-11-25T14:05:24.107619+00:00 lower-bound route

The checked branch/twin-class argument gives only 15 non-NOT gates. General monotone conversion for arbitrary graph edge functions cannot be assumed. A useful functional lemma for the last NOT is: if `f(x)=G(x,not h(x))` and `G(x,_)` is monotone, then `h≤f` permits setting the negated input to true; `f≤h` permits setting it to false. This needs no monotonicity of h. Draft Lean is in `results/orch/lemmas/lower_bound_helpers.lean`, not yet compiled while toolchain setup is pending. For one-NOT circuits, an AND of an adjacent pair of Petersen inputs is removable by this criterion.

- 2026-11-25T14:06:00.632466+00:00 [counterexample_search]: installed libz3.so.4 (Z3 4.13.3) is callable through ctypes; no Python bindings or executable. Wrote exact 1024-row truth-table CGP search (19 topological AND/OR/NOT gates) and SMT CEGIS synthesis. First CGP best so far is 10 errors, with its only NOT unused; not a witness. Known checked 20-gate construction at L_meta_1755.lean.

Timestamp: 2026-11-25T14:07:17.621387+00:00

## Existing-results audit

- Public feed meta map confirms L-meta-1035 and L-meta-2592 are conjectures as of head generated 2026-11-25T13:58:57Z. No checked refutation of1035 found.
- R_meta_2592_271: binary-floor child L_meta_4725 is checked (15 + notCount C ≤ C.size); few-NOT child L_meta_4727 remains conjecture. Equivalent binary-only lower bound L_meta_6194 checked.
- R_meta_2592_408: normalization child L_meta_7389 is checked exactly.
- R_meta_2592_318: cut-at-last-NOT child L_meta_8295 is checked exactly.
- R_meta_4727_1 merely splits by has-NOT: child L_meta_8021 checked but contradictory hypotheses (noNOT with positiveNOT); hard child L_meta_8023 remains conjecture. Other cuts R_meta_4727_17 (semantic gate-value compilation+finite lower) and R_meta_4727_53 (signed binary compilation+signed lower) are present.
- Full Petersen-minus-vertex lower bound ≥16 is already checked in L_meta_670 (523341 bytes) and L_meta_4033 (521569 bytes). All14 first-gate-orbit bounds L_meta_1665..1678 also checked. These sources nearly hit the512KiB cap; helper reuse would need compression/deduplication.
- L_meta_7493 gives ≥14 binary/non-NOT gates for Petersen-minus-vertex. L_meta_8039 excludes exactly15 gates and2NOT for that graph.
- Explicit20-gate monotone Petersen construction: L_meta_1755 (29lines). Counterexample agent notified.
- Full final-statement censuses retained in /tmp/oec/pequalnp-pilot-107/existing-fin9-size16-statements.txt and existing-petersen-equality-statements.txt.

## Checked finite semantics (2026-11-25T14:10:12.185205+00:00)

- `semantics_normalize.lean` (106 lines) compiled with exit 0 and empty stdout/stderr.
- `semantics_finite.lean` (226 lines) compiled with exit 0 and empty stdout/stderr. It contains normalization plus finite gate/circuit codes built from Fin, products and a sigma type; no new datatype or instance. Decoder soundness and completeness imply `finite_lower_bound`, an equivalence from the generic infinite-Circuit lower-bound statement to finite codes. This does not establish the Petersen bound: the finite nonexistence statement remains open.
- Complete compile logs are `/tmp/oec/pequalnp-pilot-107/semantics-normalize.stdout`, `.stderr`, and `semantics-finite.stdout`, `.stderr`.

- 2026-11-25T14:15:10.833556+00:00 [counterexample_search]: first600s CGP completed2,862,067,242 evaluations without a witness. Second run found18-active-gate monotone superfunction with exactly4 false positives69,104,521,548; full truth-table validated identity f=M OR(D AND h), M=three matching edges(0,5),(2,3),(6,9), D=OR of1,4,7,8. Exact data in search_best_approximation.json. Full SMT cases timed out; restricted fixed-gate repair templates yield UNSAT or timeout only. The finite primary-pair AND/OR distinguishing table in search_witnesses.lean compiled successfully. ThirdCGP requires an active NOT and penalizes candidates without one.

## First essential binary gate bridge (2026-11-25T14:15:41.399652+00:00)

- `semantics_bridge_slim.lean` compiled (exit 0; 512 lines). It contains the self-contained Extended signed circuit semantics used by the9-input certificate and new reusable lemmas. Only8 inherited unused-simp warnings. Complete logs: semantics-bridge-slim-1.stdout/.stderr under scratch.
- `semantics_first_binary_fragment.lean`: first_binary_split takes an actual circuit computing Petersen and obtains its first essential signed binary gate, with distinct original input signals a,b, op d<4, a live suffix, and k+1 bounded by raw non-NOT count. It excludes a zero-length live derivation using target not an original input. binary_floor17_of_suffix turns a suffix lower bound16 for all such input pairs into17+notCount<=size.
- `semantics_live_map_fragment.lean`: map_live transports the signed Live relation through any injective signal map preserving zero, one and bin. Sent to lower_bound for automorphism transport.
- existing_results owns canonical suffix16 proofs; lower_bound owns input-pair automorphisms. No proof of their required suffix premise claimed here.

## 2026-11-25T14:18:35.943239+00:00 checked lower-bound components

- `lower_bound_helpers.lean` compiled: last-NOT replacement under pointwise implication, plus vertex-transitive Petersen permutations.
- `lower_bound_pair_symmetry.lean` compiled: explicit automorphism for each distinct vertex pair, reducing it to canonical edge (0,1) or nonedge (0,2), with adjacency and edge-function preservation.
- `lower_bound_row_encoding.lean` compiled: assignment/row bijection, permutation action on 1024-bit truth tables, injectivity and preservation of both constants and AND/OR/NOT.
- All three compilations returned exit 0 with empty stdout/stderr. Combined transport of arbitrary first signed binary gates to eight canonical suffix cases is being checked. The intended consequence is at least 17 binary gates, hence at most two NOT gates in any size-19 candidate. This consequence is not yet checked.

## Checked first-gate reuse (2026-11-25T14:19:20.616530+00:00)

`semantics_first_reuse.lean` (157lines) compiles with exit0 and empty logs (semantics-first-reuse-2.stdout/.stderr). It reuses counterexample_search's finite pair witnesses and proves generic append/fold noninterference. The final first_binary_reuses_input lemma shows: if a circuit computing Petersen starts with AND/OR on distinct primary inputs i,j, input i occurs in the suffix gates' input lists. Later gates need no basis/fan-in restriction. It also proves the circuit output cannot be an original input. This is a structural prune, not the target lower bound.

## One-NOT occurrence route (2026-11-25T14:20:05.189590+00:00)

- Checked `results/orch/lemmas/one_not_occurrence.lean`: if a primary input is read only by a singleton NOT gate and all later gates are AND/OR, every other output is antitone in that input. This excludes the sole-NOT-read branch for an essential monotone target, including Petersen. It does not apply with another later NOT.
- Compile exit 0, only two deprecated ite-name warnings; complete logs in scratch `one_not-occurrence.stdout` and `.stderr`.
- No proof yet that a singly-read input entering an AND/OR with an internal wire forces four removable gates. Girth-five prevents direct monotone sharing among its neighbors, but possible cancellations through the single NOT remain the substantive gap.

## Root strategy review 2026-11-25T14:21:44.716153+00:00

- Checked: binary16 plus NOT count is a lower bound on total gates; all candidates with four or more NOTs are eliminated.
- Active: canonical first-binary suffix bound, graph automorphisms and signed compilation are being integrated toward binary17, which would leave one or two NOTs.
- Simple extension to two early binary gates is incomplete: computer classification leaves independent-gate and some dependent-gate cases; do not claim binary18.
- Search: explicit NOT-slot synthesis and local repairs found no counterexample; these timeouts and restricted UNSAT answers are not proofs. Signed17 search is next, with exact phase minimization into counted NOT gates.
- Separate one-NOT strategy and circuit input-reuse lemmas continue. All three public reduction slots are occupied, so a new reduction PR is unavailable.
- Proof work continues on the held gap only; no full theorem or refutation yet.

## 2026-11-25T14:24:18.551882+00:00 existing-results proof progress

- `existing_binary16.lean` (4568 lines) compiled exit0: unconditional `16 + notCount C <= C.size` and `size <=19 -> notCount<=3` for Petersen10. Source frozen for reviewed checkpoint. Complete logs preserved in scratch and repository logs.
- Canonical signed first-gate suffix floor16 is checked structurally against the existing nine-input floor15, with the eight finite projection/witness certificates separately kernel-checked. Full self-contained certificate build `existing_binary17_base.lean` is running. Together with checked semantics and symmetry transport, this gives17binary gates (pending full integration).
- `existing_suffix17and_snippet.lean` checked exit0 through `existing_suffix17and_test.lean`: for canonical AND or positive-minus-negative firstgate, provided that gate output remains among suffix roots, the suffix needs17binary gates. Under x0=0 both the necessary primary input and the firstgate output become constants, so the existing contraction charges2. Thus a17binary circuit must begin with OR after normalization (transport/wrapper pending).
- Computer classification of1704 fresh two-gate signed prefixes found696 cases where one-variable restriction alone charges enough to force18binary gates, with1008 unresolved (944 independent second gates,64 dependent). This is exploratory computation, not a checked theorem. Exact cases remain in scratch existing-two-gate-search.json.

- 2026-11-25T14:26:00.737233+00:00 [counterexample_search]: active-NOT CGP run completed2,495,930,919 truth-table evaluations without a witness; best has6false positives and4false negatives. Its independently verified data is search_active_approximation.json. Second explicit-NOT run completed2,565,493,310 evaluations (best4errors, NOT unused). All completed raw logs and reconstructed immutable source snapshots saved under lemmas/search_logs and search_cgp_v*.cpp. Exactly-one-NOT SMT runs with binary selectors timed out180s each. A600s one-hot OR-nonedge case is underway; signed17 stochastic synthesis is underway.

- 2026-11-25T14:27:13.016144+00:00: `one_not_petersen.lean` compiled exit0 with empty logs and passed independent source review (hash23cbca0ce3c4671081840afce15ea3a5f480ecf8e37780bc0208e282265315c4). It adds direct Petersen exclusion and output validity.
- One-NOT caveat: because unused NOTs are allowed, the target implies a monotone≥19 lower bound (monotone18 plus unused NOT would refute it); existing-results found no checked internal monotone≥19.
- Forced-assignment route: if f=A∨(B∧¬g), all A/B/g monotone, A≤B, and independent S has B(S)=g(S)=true, then A(S∪{v})=true for each neighbor v outside S. This does NOT imply A accepts an edge pair: A may have a degree≥3 minterm. Independent-set counts by (size, neighborhood size, maximal): [((1, 3, False), 10), ((2, 5, False), 30), ((3, 6, False), 20), ((3, 7, True), 10), ((4, 6, True), 5)]. This enumeration is computational evidence only.
- Sound monotone pruning: any wire false on all minimal edge inputs can be replaced by false without changing a monotone circuit computing the edge function; mixed low/high-degree minterms in a single wire remain the obstacle to a cheap degree-two normal form.

## 2026-11-25T14:28:54.404008+00:00 checked symmetry transport

`lower_bound_symmetry_transport.lean` compiles with exit 0 (only inherited unused-simp warnings). Its final wrapper `binary_floor17_of_canonical` combines the eight canonical suffix bounds with raw circuit extraction to prove `17 + notCount C ≤ C.size`. The canonical bounds are supplied separately by existing_results; the transport itself is fully checked. The generalized `suffix_of_canonical_with_extra` also preserves membership of the first gate output and accepts a lower bound and operation condition, supporting the stronger AND/mixed-gate bound.

`lower_bound_helpers.lean` now additionally checks `decreasing_endpoints_select_not`: a jointly monotone suffix G(x,z), composed with z=not h(x), whose output is true at bottom and false at top must satisfy G(x,z)=z everywhere. This needs no monotonicity of f or h.

Caution: a projected duplicate-root charge is not generally sound, even for monotone targets (e.g. optimal majority-of-three uses a variable twice). The surviving first-OR case needs a Petersen-specific argument. Nonadjacent vertex identification produces a nine-vertex, fourteen-edge graph with cover number five, but its elementary twin-class branch bound is only thirteen binary gates.

## 2026-11-25T14:32:14.496331+00:00 canonical certificate and second-gate restriction

- Full `existing_binary17_base.lean` now compiles exit0, including the copied nine-input signed floor15 certificate and unconditional canonical suffix16 proof. Corrected a helper-name collision by renaming new witness rows canonicalWitnessA/B. Complete logs: existing-binary17-base-2.stdout/.stderr. Reusable scratch artifact: leanmods/ExistingBinary16.olean.
- `existing_or_and_snippet.lean` is checked via existing_or_and_test.lean (exit0, empty stdout/stderr): after free OR of two nonzero-index inputs and a used second gate primary0 AND that OR, or primary0 AND its complement, at least16 signed binary suffix gates remain. Projection primary0=0 makes two necessary roots constant and regenerates the first OR with one paid gate; 15+2<=1+suffix. Thus this two-gate prefix forces18 binary gates. This is a partial toward excluding twoNOT size19 candidates; symmetry transport and the prefix wrapper remain to integrate.

- 2026-11-25T14:32:28.612875+00:00 [counterexample_search]: signed17 search (17 binary gates, complementary sources free) completed 4,499,867,997 evaluations in 600 seconds; best had 12 errors, no exact circuit. Primary-AND/difference exclusion variant saved for a future run. Residual signed15 (Petersen minus vertex9) passed ASan/UBSan and independent 512-assignment verification before sustained search. Deterministic single-gate replacement of the 18-gate/4-error approximation explored 17,112 replacements (AND/OR/difference/XOR) and found no improvement. Complete new logs saved.

- 2026-11-25T14:33:52.927430+00:00: `one_not_surviving.lean` (83lines, SHA25647d687f8e0a9e198f8354b3d4a19f31f397f825a7207c699662bce5292841385) compiled exit0 with empty logs. For monotone g with both incomparability witnesses against Petersen, at least6 zero restrictions leave g nonconstant. Proof kernel-checks independent-set support≤4 and bounds mandatory-zero coordinates by any independent g=true support.
- Remaining residual-premium route needs two genuine claims: some surviving coordinate allows≥3gate elimination, and Petersen-minus-vertex with a NOT requires≥17total gates. Neither is proved by these helpers.

## 2026-11-25T14:34:36.295460+00:00 unconditional binary17 integration

The import-based integration test passed with exit 0 and empty output. It proves unconditional `binary17`, `at_most_two_not`, and `one_or_two_not`. Preserved source: `lower_bound_binary17_integration.lean`. Its local alias dependencies are reconstructed as follows: `ExistingBinary16` from frozen `existing_binary17_base.lean`, `LowerPair` from `lower_bound_pair_symmetry.lean`, and `LowerRow` from `lower_bound_row_encoding.lean`; emit each matching module name in scratch leanmods before loading the integration source.

The self-contained version `lower_bound_binary17_checked.lean` contains all source directly (5,240 lines, 312,616 bytes), with only Mathlib.Tactic and PEqualNP.Defs imports. Its full compilation was started after root confirmed renewal at 14:34:14 UTC; the exact copy under scratch is `leanmods/FullBinary17.lean`. No posted theorem is claimed yet: the one- and two-NOT cases remain.

- 2026-11-25T14:37:34.278453+00:00: `one_not_protected.lean` (70lines, SHA256591fc8787fcd7579a44500e7b84baea61d37a7699a1940316fd38bc39ea86167) compiled exit0 with empty logs. For a suffix monotone in one signal, increasing that signal preserves targetf if the two signals agree whenever f=false. Specializes to bypassing `(xa∨xb)∧¬xc` by `xa∨xb` when c neighbors botha,b. This proves semantics only; a circuit rewiring/cost lemma is still needed to count one binary gate removed.
- One-NOT strategy after this pass: sole-input lastNOT branch excluded; ≥6 surviving zero-restrictions proved under incomparability; protected negative gate bypass proved. Full one-NOT size≤19 case, general monotone≥19, and the residual16-with-NOT premium remain unproved.

## First-OR and mixed-prefix structure (2026-11-25T14:37:36.727508+00:00)

- Checked `semantics_first_or_fragment.lean`: a non-OR suffix17 premise forces the first essential signed operation to be OR in any <=17-binary candidate; >=2NOT and size<=19 imply that binary bound.
- Checked `semantics_or_live_fragment.lean`: after a first OR of distinct primary inputs, all10 original pins remain live; roots are exactly all10 plus the OR signal when it is live.
- Checked `semantics_live_commute_fragment.lean`: an independent second primary-pair gate can be moved before the old first gate without adding binary gates; this lets a non-OR suffix17 bound exclude such second gates.
- Checked `semantics_subtracted_or_live_fragment.lean`: for distinct a,b,c, seed=a OR b and z=seed AND NOT c, all10 original pins remain live when both extras are allowed. With z live, roots are exactly all10+z, with seed optionally present. The proof uses a finite checked neighbor-outside-pair certificate and witness noninterference.
- All four final snippet test builds exited0 with empty stdout/stderr; scratch logs respectively semantics-first-or-1, semantics-or-live-2, semantics-live-commute-2, semantics-subtracted-or-2. Tests use the checked SemanticsBridgeSlim module; final merge must inline helpers under the allowed Defs import.
- Generic duplicate-root charging is false even for monotone graph targets: P4 f=ac OR bc OR ad has a4-gate Run from [a,b,c,a,d] via (a OR b) AND (c OR (a AND d)), but needs4 signed binary gates from distinct inputs. A complete small truth-table census found no <=3-gate realization (24/468/8756 normalized states by depth). Census is computational evidence, not a Lean lower-bound theorem. The obstruction requires a Petersen-specific argument or NOT-budget tracking.

## 2026-11-25T14:41:30.869268+00:00 final binary17 preservation

After the root reported HTTP 410, development stopped. The already-running full self-contained binary17 build had completed successfully: exit 0, 37,389 bytes of warning-only stdout, empty stderr. Exact reviewed source hash: c9f474e6ab6295325381d345b003a63b90c487e8f70bcf213671cf62679c8843. Complete full-build, integration, and axiom-audit logs are preserved under `results/orch/validation/`. The compiled bound is unconditional, but does not finish L-meta-2592: candidates with exactly one or two NOT gates remain.

## 2026-11-25T14:41:52.481906+00:00 existing-results preservation stop

No own build remains active. Dual9 build was never launched. See lemmas/existing_PRESERVATION.md for checked-vs-draft manifest. Complete checked and failed proof logs copied to results/orch/logs.

## New assignment L-meta-2583 after HTTP410 recovery

Previous L-meta-2592 work is stopped and preserved. The desk assigned L-meta-2583 on recovery; only this new lease is live. Exact statement/imports are in results/orch/2583/. New sources go in results/orch/2583/lemmas/. Reductions are not open despite sketch suggesting a cut. Only root handles desk/lease and submissions.

### 2026-11-25T14:49:38.954051+00:00 — 2583 semantics
Checked `results/orch/2583/lemmas/semantics_pairs.lean`: for any incidence relation and any correctly computing circuit, prime implicants are exactly incident point-line pairs; IsReadK for any k iff every incident pair passes readsAtMost on [p.val,N+l.val]. Defs-only import, no model assumptions. Build exit0; full logs `/tmp/oec/pequalnp-pilot-107/2583-semantics-pairs-2.stdout` and `.stderr` empty. Semantic audit found no malformed-input loophole: IsAO2 enforces backward reads and exactly2 AND/OR operands; readVectors tracks joint tree multiplicities. Root notified immediately.

### 2026-11-25T14:49:55.076064+00:00 — blocks agent, gap 2583

Checked `2583/lemmas/blocks_local_obstruction.lean` (empty stdout/stderr, exit 0). The matching function x0x2 OR x1x3 has a seven-gate AO2 CNF circuit that is Read2 and not Read1, with no semantics-preserving erasure of any single gate redirected to any earlier wire. A three-gate Read1 DNF computes the same function. This is a counterexample only to replacing global minimum size by local erasure irredundancy; it is not a counterexample to the posted projective-plane statement.

Existing checked proof-tree frontier equivalence is in L_meta_3708 (forward direction L_meta_2230), so no need to reprove it. Existing-results agent found one-junk normalization in L_meta_3700 under several extra fixed-point hypotheses; the multiple-junk case remains the structural obstacle.

### 2026-11-25T14:52:24.944232+00:00 — 2583 output semantics
Checked `results/orch/2583/lemmas/semantics_output.lean`: any circuit correctly computing a nonempty incidence relation has output wire 2N+j for j<size; singleton assignments are rejected, raw output is impossible, missing output is false. `plane_output_gate` obtains nonemptiness directly from the posted q,N,line-cardinality hypotheses. Defs-only; no AO2 assumption needed. Final build exit0, complete logs `/tmp/oec/pequalnp-pilot-107/2583-semantics-output-2.stdout` and `.stderr` empty. Root notified immediately. Existing `L_meta_2264.lean` line2088 proves every valid IsAO2 wire true on the all-true input, useful for eliminating satisfiability side conditions in block lifting. No semantic loophole or full normalization proof found.

## 2026-11-25T14:52:38.978322+00:00 2583 semantic singleton-star partial

Checked `2583/lemmas/lower_singleton_star.lean`, exit 0, three harmless simp warnings and empty stderr. For arbitrary monotone factors whose conjunction lies below a C4-free graph function, accepted singleton sets are disjoint, their cross pairs are edges, and one set has cardinality at most one. This does not assume READ1 and isolates the unresolved case to proof edges not generated by singleton cross pairs. Complete success logs copied into `2583/logs/`.

### 2026-11-25T14:54:16.863399+00:00 — blocks agent, line restriction

Checked `2583/lemmas/blocks_linear_factor.lean`: for a finite support S, any monotone Boolean function that dominates OR(S) and rejects the maximal input outside S equals OR(S). Consequently, if a monotone conjunction dominates OR(S) and rejects that maximal input, one child equals OR(S). This is the requested line-specific branch-selection rule; no size conclusion is asserted. Final logs `2583-blocks-linear-02.stdout/.stderr` are empty, exit 0.

Consistency obstacle: for intersecting supports S={a,c}, T={b,c} and line variables l,m, factors A=OR(S) OR m and B=OR(T) OR l force opposite choices under l-only and m-only restrictions. Their product is dirty: it accepts l=m=true with every point false. Thus the incidence intersection axiom alone does not justify a uniform child choice; a global proof must pay for or eliminate the dirty product and its downstream filters.

### 2026-11-25T14:54:21.395652+00:00 — 2583 independent helper review
Semantics agent independently reviewed complete `existing_star_builder.lean` and `lower_singleton_star.lean`, their complete compile logs, and format scans. Both PASS as partial helpers, not full gap proofs. Exact hashes and caveats in `results/orch/2583/lemmas/semantics_review.md`. Critical caveats: star normalization still assumes the sharp size budget; singleton-factor stars do not cover edges arising only through repeated pair witnesses. No author files changed.

### 2026-11-25T14:56:09.336213+00:00 — 2583 global normalization audit
Incident-pair characterization reduces normalization to providing one squarefree witness per edge. The singleton-star helper controls only cross products of singleton traces. A dirty factor may accept an edge pair while rejecting both singleton endpoints, and two incomparable such factors may preserve a repeated edge through their conjunction. The checked matchingCNF example shows this can survive every single-gate erasure. Therefore neither ordinary semantic equivalence nor repeated-variable deletion supplies a global read-one rewrite. A cost proof must charge these remaining pair-only witnesses or justify a nonlocal Boolean factorization. No valid new charging invariant found by semantics agent.

## 2026-11-25T15:03:31.130026+00:00 2583 four-clause obstruction

Checked `2583/lemmas/lower_four_clause_matching.lean`, SHA256 fd90657793b294f5d82091acfd98d55c254eb2eaf66b229036e46935781be6df, exit 0, warning-only stdout and empty stderr. Public theorem `FourClause.clauses_ge_five_on_matching` applies to arbitrary point/line types and any C4-free incidence relation: a globally clean conjunction of OR-clauses accepting three disjoint incidences requires at least five clauses. The proof checks all 512 three-by-three incidence matrices and gives five independent assignments for each of the 21 valid matrices containing the diagonal; every pair of assignments has a union containing a diagonal edge. Pigeonhole then forces five distinct rejecting clauses. This excludes a clean AND of two independent dirty ANDs with OR-only operands from accepting three disjoint incidences. It does not yet compare replacement cost or handle additional OR wrappers/dependent dirty gates. Complete success logs preserved under `2583/logs/`.

### 2026-11-25T15:04:13.349195+00:00 — blocks agent, maximal false plane input

Checked `2583/lemmas/blocks_maximal_false.lean`, empty logs `2583-blocks-maximal.stdout/.stderr`, exit 0. The baseline X_m has only line m true and all points outside m true. Every other line has a point outside m by line degree and unique joins. Activating additional coordinates above X_m computes exactly the OR of the q+1 incident point coordinates and N−1 other line coordinates. Total positive sensitivity is therefore N+q. The source uses separate point and line functions, without a circuit-size claim.
A joint charge remains missing. Summing the line-restriction OR requirements cannot assume every OR gate belongs to one line: clean OR gates merging already formed edges can be productive in several line restrictions and are paid for by their distinct AND joins.

### 2026-11-25T15:06:36.531582+00:00 — blocks agent, sensitivity OR count checked

Checked `2583/lemmas/blocks_or_sensitivity.lean`, empty final logs `2583-blocks-or-03.stdout/.stderr`, exit 0. At any fixed input a, positive sensitivity of the output is at most the number of OR gates plus one. Proof uses a union-cardinality potential across arbitrary wire subsets. OR contributes at most two supports and charges one gate; AND contributes at most one support and charges zero. Its choice of operand is fixed from the baseline value, before the sensitive variable is considered. Exact fan-in two is assumed. Missing wires are constant false; duplicate operands and arbitrary output indices are covered. ReadsBack is not required.

Semantics agent is joining this with the plane baseline cardinality N+q to derive a fully checked OR-count bound. This is weaker than the desired total-size bound. Across line baselines, shared ORs can be productive repeatedly; extra AND joins account for that sharing in clean circuits, but no general charge has been proved for dirty factors.

2026-11-25 15:09 UTC — Counterexample search: exact SMT nonREAD1 query at canonical7-gate size for two3-stars sharing onepoint returned UNSAT in both edgeorbits (5.47s shared,4.05s private). Three-star11-gate queries and K4-incidence14-gate query timedout10s. These are computational results, not Lean certificates. Positive6-gate double-star SAT model independently matches all64 assignments and fails jointREAD1 onedge(1,5). Frozen source/result/logs under2583 search package.

### 2026-11-25T15:08:55.569024+00:00 — 2583 finite gadget audit
L1006 is a boundary-test counterexample, not an exact edge function: its 20-gate binary expansion rejects genuine edges and its graph has odd cycles. One missing edge and nonbipartiteness are kernel-checked in semantics_boundary_gadget.lean (independent reviewer one_not PASS SHA e95f7305024b42b93da8a6990bee051c398a9fa8542634d5ff4f84f4acce36df). L4849 is exact/global-minimum but its8vertex graph contains 5cycle0-4-7-1-6-0, and its11gates equal8edges+cover4−1. Tested177147 ternary restrictions and4212553 zero/identification quotients of L1006, plus75262 nontrivial ternary/identification quotients of L4849; no exact bipartite C4-free candidate simplified below its star budget. Complete logs retained in semantics_gadget_audit.txt. A correct28gate Fano nonREAD1 seed was constructed, checked on all16384 inputs and joint tree counts; read1 fails exactly edges(1,7),(3,7). No single-gate erasure preserves correctness. Search agent received semantics_fano_seed.json. These finite search results are computational evidence, not Lean lower bounds.

## 2026-11-25T15:10:00.861899+00:00 2583 lower-bound preservation stop

Stopped immediately on root renewal-error instruction. No own build/search remains active. All five lower-bound Lean sources compiled successfully; exact hashes and theorem scope are in `2583/lemmas/lower_PRESERVATION.md`. All complete diagnostics copied to `2583/logs/`; exploratory sources copied to `2583/research/`. The complete gap remains unresolved.

2026-11-25T15:10:11.199982+00:00 — Root reported renewal error and ordered stop. Counterexample search killed sole live process23761/session42679 via SIGTERM, exit143. Complete run2 stdout/stderr and all printed candidates preserved in results/orch/2583/search_stop_renewal_error/. No0-error candidate logged; besttruth1criticalerror, bestnonREAD1 2criticalerrors. Final evaluationcount unavailable because run interrupted. All other searches had completed.
