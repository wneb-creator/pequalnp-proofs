# Pilot 152: L-meta-4970

Lease held only by root. Assignment received 2026-11-25T15:40:22Z. Reductions closed.

Exact desk assignment: /tmp/oec/pequalnp-pilot-152/assigned-gap.json
Statement: /tmp/oec/pequalnp-pilot-152/statement.txt
Lean environment: source /tmp/oec/pequalnp-pilot-152/toolchain-env.sh
Use narrow imports, initially PEqualNP.Defs. Fetch targeted prebuilt cache before missing Mathlib dependencies. No Mathlib source builds.

Every agent owns its named lemma file and appends timestamped findings here; root owns final L_meta_4970.lean. No agent calls desk, commits, or pushes. Notify root immediately of any compiling result.

Strategies and findings follow.

2026-11-25T15:43:02.227627+00:00 status_review: Only tCount precedent is L_meta_4791; useful OR reach/orIn propagation toolkit at lines626–737. No stronger lower bound found. Detailed notes in lemmas/library-search.md. Independently reviewed root empty_edges partial: preservation-only approved after compilation; no posted theorem yet.

2026-11-25T15:43:26.523848+00:00 [stars] Compiled results/orch/lemmas/stars.lean: left_star_unique and right_star_unique prove a leaf set of size at least two has a unique center under posted C4-free condition; left_star_inter_card_le_one gives intersection at most one for distinct centers. ownership_cover turns any endpoint-assignment into a vertex cover. ownership_ledger gives the exact finite-fiber identity sum (fiber.card - 1) + image.card = E.card. All helpers use only PEqualNP.Defs, no sorry or added axioms. Build via lake --dir lean env lean results/orch/lemmas/stars.lean passed with empty output. Root notified immediately for push-early.

## Counterexample audit 2026-11-25T15:44:13.104168+00:00

IsAO2 rules out malformed forward reads/fan-in issues. No edge/zero-side defect found. Semantic star witness OR-reach can be empty: b0 OR b1, duplicate AND of that wire, then duplicate OR; this computes OR{b0,b1} but final orIn is empty. Both proof agents informed. Small exhaustive semantic-state search ran p=q=2 through 3 gates and p=2,q=3 through 4 gates; see scratch counterexample-small-search.log and .py. No counterexample found.

2026-11-25T15:44:13.990357+00:00 [stars] Second compiled version adds semantic injectivity of left/right OR leaf sets, opposite-color OR-function distinction for nonempty leaves, and same_right_or_center_unique. These show a nontrivial star OR gate can serve only one center and one color. No extra imports. Root and ledger agent notified.

2026-11-25T15:44:31.362581+00:00 status_review: Useful ledger precedents found in L_meta_8933 gate_budget323–415 and L_meta_2235 s2233(output OR count), s2234(star leaf OR count). They need extra cleanliness/read-once hypotheses. T0 does NOT force semantic monochromatic singletonSupport: duplicate singleton AND wrappers hide OR reach. Details in library-search.md.

## Ledger route — 2026-11-25T15:45:05.471775+00:00

Compiled `lemmas/ledger.lean`: `no_two_colour_of_zero` and `or_reach_monochrome` establish syntactic OR-reach monochromaticity from T=0.

Main remaining obstacle: arbitrary circuit AND gates can have singleton support and can be dirty; star OR witnesses may be unused or have ANDs in their cone. Existing L_meta_8933 gate_budget needs reachable AND singleton support empty and pair-safety, so not directly applicable. L_meta_2235 s2233 counts AND gates in output OR closure versus output OR count; s2234 gives disjoint leaf OR accounting. Semantic agent is adapting L_meta_529 to OR-only star charge. Distinct witness components at the same center must be counted separately unless a stronger gate realizes their union.

## 2026-11-25T15:45:05.890914+00:00 Semantic strategy

Adapted L_meta_529 to count only OR gates. File results/orch/lemmas/semantic.lean proves `Semantic.or_outputs_bound`: for pairwise intersections at most one, monotone fan-in-two multi-output pure OR computation requires sum_i (|S_i|-1) OR gates. `Semantic.main_inv` gives per-family charge set D(Q): gate is OR, false on complement-of-Q assignment, and true on two distinct singleton inputs. Such charge gates are disjoint for distinct-center stars and disjoint from all gates below the final edge function (those have no true singletons). AND cannot merge the singleton classes. No reliance on syntactic OR reach.

2026-11-25T15:46:33.453922+00:00 status_review: Independently reviewed revised stars, ledger, all341 lines semantic, and audit counterexample. Approved partial preservation after reported compilation; audit is not gap refutation. Pure OR semantic charges robust through AND wrappers. Main residual circuit ledger still needed.

2026-11-25T15:47:35.883097+00:00 [stars] Third compiled version adds singleton_bilinear_false, singleton_not_below_bilinear for arbitrary Boolean functions, left/right nonempty-OR separation, and singleton_separates_gate_sets. Last lemma proves Disjoint A B where each A gate has a true one-hot witness and each B gate implies the target edge function pointwise. Interfaces match semantic eof/value by unfolding. 14 helper lemmas currently compile with PEqualNP.Defs only.

## 2026-11-25T15:48:13.615837+00:00 AND/output budget strategy

Compiled lemmas/and-bound.lean (213 lines): self-contained adaptation of L_meta_2235 s2233. output_or_bound proves any finite set F of AND gates in the output OR-closure has card F at most the number of OR gates in that closure plus one. Requires only AO2 and closure membership, not clean/monochromatic operands. Full logs scratch and-bound-build.stdout/stderr (exit0; deprecation warnings only). Parent notified for push-early.

Primary research read 2026-11-25: Jukna, Disproving the Single Level Conjecture, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf . Lemma3.12 equates AND count with biclique cover only for single-level circuits; Theorem2.4 gives asymptotic AND-count savings for saturated matching extensions, which are not bipartite. Thus general normalization/AND-count cover lower bounds cannot be assumed. No known C4free bipartite counterexample identified.

2026-11-25T15:50:16.094728+00:00 [stars] Frozen compiled 292-line snapshot adds semantic StarWitness indexed by Fin p ⊕ Fin l and star_witness_center_unique for all color combinations. selected_star_cover converts per-edge endpoint owners with selected star-gate witnesses into a Fin(p+l) vertex cover whose cardinality is at most the number of distinct chosen gates. Generic image_card_le_of_fiber_refinement and injective centerEmbed support assembly. Root notified for independent review and preservation.

### Ledger base cases — 2026-11-25T15:50:41.127778+00:00

`lemmas/ledger.lean` now also compiles `circuit_dependencies` (fan-in-two support ≤ size+1), `edge_active`, `edge_inputs_bound`, and both `single_left_star_bound` / `single_right_star_bound`. The latter prove the required vertex-cover bound whenever all graph edges share one vertex, using only IsAO2 and exact edge-function computation. Full logs: `/tmp/oec/pequalnp-pilot-152/ledger-build.stdout` and `.stderr`.

## Counterexample/AND audit 2026-11-25T15:51:10.212482+00:00

- `results/orch/lemmas/counterexample.lean` compiles: explicit AO2/T0 semantic OR witness with empty orIn. Auxiliary caution only, not a refutation of L-meta-4970.
- Exhaustive free-OR/2-AND enumeration: no C4-free 3x3 tau=3 counterexample among 4,465,825 second-AND candidates; no 3x4 tau=3 counterexample among 77,214,486. Scripts/logs in scratch counterexample-and-count*.
- Official Z3 5.3.3 wheel verified/extracted under scratch z3-python. Exact truth-table synthesis allowing arbitrary free ORs confirms C8 needs >=4 ANDs (UNSAT 0.13s), C10 needs >=5 (UNSAT 9.56s). C12 in progress.
- Primary literature read 2026-11-25: Jukna, Disproving the single level conjecture, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf, Theorem 2.4 gives an exponential gap between arbitrary and single-level conjunctive complexity for saturated non-bipartite graphs. Generic AND-count=biclique-cover normalization is therefore false; bipartite/C4-free restrictions must be essential.

2026-11-25T15:51:57.139151+00:00 [AND/output budget] Extended and-bound.lean compiles (build-5 exit0). boundary_true_witness decomposes any true wire into a true singleton input in its OR reach or a true AND root in its OR closure. boundary_output_and eliminates the singleton alternative when output rejects all singleton assignments. boundary_reach_up propagates root truth to output, making exposed ANDs automatically below the output. File frozen for root assembly/review.

## 2026-11-25T15:54:40.542590+00:00 Semantic boundary classification

Compiled `boundary_and_star`: if two monotone operand functions have nonempty singleton supports and their conjunction lies below the bilinear edge function, the cross supports form a C4-free complete bipartite graph; one support is singleton, giving a star center. Also compiled `val_monotone` for arbitrary AND/OR gate lists and `pure_or_preserved`: a monotone function below OR(Q) agreeing on singletons equals OR(Q). Frozen snapshot scratch semantic-boundary-checked.lean. WARNING: boundary AND may accept hidden edge pairs outside its cross-singleton star; e.g. (u OR ab) AND (v OR ab) = uv OR ab. Normalization/descent remains necessary.

## Refuted auxiliary zero-support count 2026-11-25T15:55:49.530853+00:00

`results/orch/lemmas/counterexample.lean` compiles with a second explicit circuit (P4, 8 gates). It proves IsAO2, T0=0, exact edge-function semantics, no4cycle, every posted star witness, and cover size >=2, but exactly one gate is false on every singleton input. Therefore zero-singleton-support count >=2*tau-1 is FALSE even under the entire posted hypothesis list. Posted size bound is not refuted (8>=3+2-1). See anchored_* lemmas.

Exact free-OR SMT synthesis for any4x4 C4free graph with diagonal matching found UNSAT at3AND (0.486s). Any5x5/4AND and C12/5AND timed out120s (unknown, not a result). T0-restricted retries running.

## 2026-11-25T15:56:26.649747+00:00 Pure OR preservation under gate cut

Compiled `Semantic.cut_zero_preserves_or`: in an AND/OR circuit `pre ++ [g] ++ post`, replace g by OR([]), a constant-false gate. If g is false on every singleton input, every output that was a pure OR(Q) remains exactly OR(Q). Supporting lemmas prove replacement pointwise decreases all wire functions and agrees with the original full circuit on any input where g was already false. No ReadsBack assumption is needed because fold evaluation already freezes prior wires. The temporary zero gate violates IsAO2 fan-in-exactly-two; a subsequent constant-elimination/normalization lemma must restore AO2. Frozen compiling snapshot: /tmp/oec/pequalnp-pilot-152/semantic-zero-cut-checked.lean.

### Cofactor route — 2026-11-25T15:58:20.949657+00:00

Compiled `edgeEval_set_left_false` and `forced_or_false_positive_neighbors` in ledger.lean. The latter treats a star OR Q as fresh Boolean t: if monotone H agrees with the center-deleted edge function when t=OR(Q), but H(x,true) is a false positive, then every b in Q has an active surviving neighbor point in x. C4free makes those points distinct, so stars agent cardinal lemma gives at least |Q| active points. A minimal false-positive true certificate therefore needs >=|Q| points and suggests >=|Q|-1 AND charge. No additive/disjoint charge or circuit deletion theorem yet.

Cofactor induction caveat: deleting a can shrink other witnesses {a,a'} to singleton. The newly bare edges need not be matching, but they lie in a union of disjoint stars centered at N(a), since every surviving point meets N(a) in at most one line.

2026-11-25T15:58:46.275965+00:00 Semantic: `cut_zero_lift` compiled. If cut gate h implies ancestor a and a lies below output F, then F = Fcut_h OR a. Thus a direct downstream AND reader of below-F a can be cut to zero and a lifted to output, preserving pure OR targets by cut_zero_preserves_or. To keep AO2 and total size, zero propagation must delete h and pay for added output OR. Existing L5779 no_and_reader increases functions and can break star targets, so cannot reuse its minimality argument unchanged. Snapshot semantic-lift-checked.lean.

- status_review: all-wire zero compressor source L_meta_5138 build222ff sent to semantic agent; shortest TopForm normalization L_meta_5779 pushOr_step574/main_aux817. Own new compiled ORCover.or_restriction_bound establishes |S|−1≤ORcount whenever fixing complementS=true gives OR(S), using OR-only cost with no extra ORs. Graph-cover private-neighbor specialization in progress.

## Root replan 2026-11-25T16:00:53.600083+00:00

Full gate budget remains unproved. Keep three substantive routes: (1) normalize while preserving all pure-OR witness outputs via zero-cut and compression; stars agent recovers actual OR witnesses from semantic pure-OR wires; (2) cofactor dirty-reuse false-positive certificates need many distinct active points, then minimum-term AND accounting; (3) exact C12 16-gate synthesis with all posted hypotheses. Do not promote generic AND>=vertex-cover or empty-singleton residual counts to facts. The latter is Lean-refuted even with all posted hypotheses. Cover/baseline OR-count route remains supplementary; local disjoint-charge selection failed.

2026-11-25T16:01:24.688393+00:00 [AND budget] COMPILED true_input_certificate: for any AndOrOnly backward-read fanin-at-most2 circuit, each true output has a forcing input subset S of the original true inputs with |S|≤numberANDs+1. Proof uses descending true-wire frontier; trueOR chooses one child, trueAND chooses all(≤2); counts distinctANDs by gate prefix. Allows zero-arity constant gates, suitable for cofactors. Frozen scratch and-bound-minterm-checked.lean; build and-bound-minterm-2 stdout/stderr exit0.

2026-11-25T16:02:06.705584+00:00 [stars/normalization] Compiled pure-or-source.lean: any wire computing OR(Q), |Q|>=2, in an AND/OR gate list has some actual OR gate computing exactly OR(Q). No fan-in or ReadsBack needed. and_pure_or_operand picks an AND operand false on the complement of Q; monotonicity and singleton acceptance recover the exact OR function. Circuit wrapper matches posted wires/gateAt interface. New declarations start at line697 after copied frozen semantic-lift prefix; root should merge only the new tail. Frozen scratch pure-or-source-checked.lean for independent review.

2026-11-25T16:02:54.901054+00:00 [AND budget] Stronger certificate compiles: true_input_certificate now counts only branching_and gates (AND with inputs.length≥2). Constanttrue AND([]) and unary AND gates do not contribute. This preserves original AND budget when forcing a star OR gate true via AND([]). Frozen scratch and-bound-binary-checked.lean; build and-bound-binary stdout/stderr exit0.

2026-11-25 16:05 UTC — semantic_proof: Compiled zero-cut compressor bridge through actual Circuit.wires. Frozen checkpoint semantic-one-cut-checked.lean in job scratch has 1206 lines and no errors. `Compression.compress_one_cut C hAO j hj` returns a binary AO gate list, maps every wire of `C.gates.set j OR[]` to Option wires preserving all input valuations, and saves at least one gate. Pure OR targets survive by earlier singleton-preserving decrease lemma. Status_review is independently adding syntactic OR-reach labels to ensure tCount=0 survives compression; bare function semantics alone does not imply tCount preservation. Next step is append one output OR combining cut output with old below-F ancestor, paying the saved gate.

### 2026-11-25 16:08:20 UTC — toolchain_setup: matching/fooling-set AND route
No proof of AND-count >= maximum matching yet. Pairwise truth-table/fooling-set reasoning is insufficient: Jukna graph representations can represent a matching with O(log n) AND gates while accepting larger independent sets; exact full function semantics must be used. General k-AND circuits have at most 2^k maximal false assignments (choose one false predecessor per AND, all predecessors at OR, giving at most 2^k input-zero certificates). This proves the matching-size bound on C6/C8/C10 from 5/10/17 maximal independent sets, but first fails on C12: 29 maximal independent sets only force 5 AND gates versus matching size 6. Counterexample agent is testing that case using extremal assignments. Literature searches found no applicable primary-source theorem; single-level biclique-cover equalities do not justify arbitrary-circuit normalization.

2026-11-25 16:14 UTC — semantic_proof: Full concrete `Compression.cut_lift_preserves` compiled (1309-line semantic-full-cut-lift-checked.lean snapshot). Cutting g at pre.length, where g implies an earlier ancestor a which implies output F, then OR-ing compressed F_cut with compressed a yields AO2 D with size≤old and unchanged F; all nonempty pure OR target wires survive. Hypothesis g=false on singleton inputs supplies preservation. The constructor accepts arbitrary g, not just AND. Actual OR gate witnesses are restored by toolchain_setup pure_or_has_or_gate. T0 labels and AND-count decrease are in status_review typed compressor, to be joined next.

### 2026-11-25 16:08:56 UTC — toolchain_setup: independent partial review
Approved preservation of ledger-forced-cofactor-checked.lean (550 lines, SHA256 16896e9f4e9b313de3c815f36a5b19d29bca3b2be4b85a5fd89dff77a53e037f). Reviewed delta from forced-original snapshot: forced-run monotonicity, actual circuit cofactor correctness, and specialization of false-positive neighbor theorem. Independent Lean run exit 0; full stdout/stderr files review-ledger-forced-cofactor.* are empty. Forbidden syntax scan found only the allowed import. No full posted theorem is claimed.

### Quantitative dirty-use charge — 2026-11-25T16:09:05.715461+00:00

COMPILED `dirty_or_binary_and_bound`: for a star OR Q at center a, if forcing its gate to true after a=false creates any false positive, then |Q| ≤ (# branching AND gates of C)+1. Constructed actual circuit replacing the gate by AND([]), preserved AO-only/backrefs/fanin≤2, applied the new true-input certificate, then C4free injects Q into true surviving points in the certificate. Tested in one combined source with frozen stars and AndBudget components: `/tmp/oec/pequalnp-pilot-152/ledger-dirty-combined-checked.lean`; build exit0 with only inherited deprecation/style warnings. Current ledger component now depends on stars and AndBudget; compile via assembled source. The charge is global, not yet disjoint across multiple centers, so it does not prove the posted bound.

### 2026-11-25 16:09:57 UTC — toolchain_setup: typed compiler review
Independent PARTIAL preservation approval of review-typed-checked.lean (1547 lines, SHA256 a76281356bc3208b5c57ab96221e784bd4f5eb7a407da2c95d366602ed41a737). First 1056 lines exactly match reviewed semantic-compressor snapshot. Reviewed TypedCompression reach API, Labels implies T0, label subset induction through zero removal, and deletion-count size budget. Independent compile exit0 with six existing compressor-prefix warnings only; stderr empty. Exact semantic conclusion refers to u(A,a,b,Del), not yet original C. No forbidden syntax found. Full logs review-typed-independent.*.

- status_review: compiled typed zero compression and optional output join, preserving T0 through syntactic OR-reach labels (not inferred from semantic preservation). AND count is tracked simultaneously. Frozen review-typed-join-checked.lean1928lines, build9exit0; semantic agent integrating concrete cut+lift, AND agent handling strict deleted-AND budget. The final target remains unproved.

### 2026-11-25T16:12:09.901055+00:00 AND-count strict deletion

Compiled `andNum_filter`, `andNum_deleted_lt`, and `andNum_join_or`: the typed compressor's filter-count budget strictly reduces actual AND count when its one deleted gate is AND; a final appended OR leaves that count unchanged. Frozen 77-line standalone scratch `and-count-cut-checked.lean`, SHA256 7871b9f85bc17857f69808c99a8f711551d87a88a12d4d01db13d0eb9e8b4828. Status_review independently approved partial preservation; semantic agent integrating. Existing andGate/andNum definitions duplicate TypedCompression exactly, so merge only new lemmas. Also independently reviewed semantic-full-cut-lift-checked tail and approved partial preservation; no full target claim.

2026-11-25 16:16 UTC — semantic_proof: FULL typed cut/lift compiled (2178-line semantic-typed-cut-lift-checked.lean, SHA d370eb3a993e66d406b7a8ed751b94509033413d530ba22d2b4aeb812a07b8c9). `TypedCompression.typed_cut_lift_preserves` simultaneously preserves AO2, T0=0, total size bound, final function, and every nonempty pure OR output, while strictly decreasing AND count when cutting a later AND implying an earlier below-output AND. It combines status_review typed compressor/labels/join, and_lower_bound strict count lemma, and semantic zero-cut preservation. This establishes the direct-AND-reader elimination step for a multioutput AND-minimal circuit. Full TopForm normalization through OR readers and the final disjoint dirty-gate budget remain open.

- status_review: compiled OR-reader ordinary bypass T0 lemma plus final appendedOR T0 lemma, shared matchingL5779 helper names in TypedCompression.Bypass with and_lower_bound agent. Frozen review-typed-bypass-join-checked.lean2099lines, build12exit0. All new compiled files remain partial helper packages; no exact posted theorem yet.

### 2026-11-25 16:16:20 UTC — toolchain_setup: typed cut-lift independent review
PARTIAL preservation approved: semantic-typed-cut-lift-checked.lean, 2178 lines, SHA256 d370eb3a993e66d406b7a8ed751b94509033413d530ba22d2b4aeb812a07b8c9. Reviewed delta from typed-join: descriptor extraction, single-cut semantics and strict AND budget, then typed_cut_lift_preserves. Ancestor index lies in unchanged prefix; ancestor AND gives empty OR label, ensuring the repair OR stays T0. One deleted AND offsets at most one repair OR; AND count strictly decreases. Q.Nonempty excludes none mappings via all-true input. Explicit output bound and mapped-wire bounds cover default cases. Independent compile exit0 with lint warnings only, full logs review-semantic-typed-cut-lift.*. No forbidden syntax found; this is not the posted theorem.

### 2026-11-25 16:17:17 UTC — toolchain_setup: T0 pair-only fooling-set obstruction
Even adding syntactic T0 cannot justify AND>=matching from pair truth tables alone. Explicit checked construction for matching size32 on64 inputs: use the10 equality bit clauses (OR of left indices with bit v) OR (OR of right indices with bit 1-v); hide each left group behind one idempotent AND, so every clause OR reaches only right inputs. Conjoin all10 clauses using9 ANDs. To reject same-color pairs, conjoin the product of ORallLeft and ORallRight, adding2 ANDs. Naive fanin2 construction has393 gates,21 ANDs,T=0, and zero mismatches on all2016 two-active-input assignments. It falsely accepts independent assignment {left0,left31,right1}; hence it does not compute the matching function and is not a posted counterexample. Full rejection of every independent set remains essential. Python evaluated every pair and syntactic OR-reach sets directly.

### 2026-11-25T16:17:58.805960+00:00 — counterexample search final bundle

No counterexample to posted L-meta-4970 found. Final optimized compressed C12 query with at most five AND gates and unrestricted ORs (no T=0 hypothesis) returned UNSAT in 271.72s. Earlier compressed T=0 query returned UNSAT in 16.329s. These are solver results, not Lean certificates. Full direct C12 size<=16 and theta8 size<=11 searches remain UNKNOWN/timeouts, including ordered QF_BV reruns at 180.062s and 180.037s.

Reproducibility bundle results/orch/search is complete: 48 files, 639485 bytes; MANIFEST.sha256 hash e7164d6f61bcc3c1c3726d404136a1bd98c3a2b778e0cf0d77bfc0943c2c9ce9. Exact programs, completed full logs, five SMT-LIB queries, and validation caveats included; no solver binaries or credentials. All search processes have finished. Immutable 96-line Lean auxiliary-counterexample snapshot remains results/orch/lemmas/counterexample_checked.lean, SHA256 9635b2d227b31ef7d7e8ce8aab96a83d274a94834a97f07751df032bcdbe41d3, compiled successfully. The P4 example refutes only the zero-singleton-gate helper, not the posted statement.

2026-11-25T16:18:27.241201+00:00 ledger_proof: COMPILED protected-wire certificate. Protected.frontier_certificate stops backward true frontier at a chosen gate; forced_input_certificate proves if forcing gate true changes a false output to true then a sufficient input certificate has cardinal ≤ original branching-AND count (the protected gate consumes the usual +1). dirty_or_binary_and_bound sharpened to |Q|≤#branchingAND, with no +1. Full assembled build exit 0; immutable ledger-protected-component.lean and ledger-protected-combined-checked.lean in job scratch. This is a partial cofactor charge, not a proof of global summability or assigned gap.

### 2026-11-25T16:18:55.230322+00:00 OR-reader bypass

Compiled 720-line `or-bypass-core-checked.lean` (SHA256 4c021886a7535e29e973793c314beff010de47afad495d860bb9ec9abd75bec8). Removes an OR reader of a below-output, singleton-false ancestor; replaces that reader by its other input; appends an OR of old output and ancestor. AO2, total size, AND count and all pure OR witness functions are preserved. AND-index sum strictly decreases whenever an AND gate follows the removed OR. New reversed delGate semantic monotonicity plus singleton agreement proves arbitrary pure OR witness preservation. Status reviewer approved independently. Final T0 wrapper combines reviewed label-based deletion and append helpers; build in progress.

2026-11-25T16:19:40.787259+00:00 [AND/OR bypass] Full typed_pushOr_step compiled with AO2, T0, same size, same AND count, strictly decreased AND-index sum, same output and all pure OR targets retained. Frozen component `or-bypass-full-component.lean` SHA256 3977767d055f64e3f2579a8add7660fca602672b9224e698d8b2aac8b260f48b; full source `or-bypass-full-checked.lean` SHA256 a9f48bee89918bb4008642d72e4d27eefbb499ec3a71e7b86f2bf8f4ed546250. Component merges core semantic work and status reviewer T0 labels; semantic agent can now instantiate lexicographic minimality. Full posted gate-budget inequality still unresolved.

- status_review independently approved complete OR-reader rewrite component (or-bypass-full-component.lean906lines SHA3977767d055f64e3f2579a8add7660fca602672b9224e698d8b2aac8b260f48b). Full build2exit0 reported and exact component embedding verified; T0/size/AND-count/pureOR witnesses preserved, AND-index sum strictly decreases. Normalization still leaves dirtyAND accounting unresolved.

## Root second replan 2026-11-25T16:20:11.053990+00:00

Do not mistake full normalization constructors for final inequality. Next concrete result is lexicographic minimality yielding TopForm while preserving original star witnesses. Remaining global mathematical problem is additive accounting of dirty intermediate gates and semantic OR charges; local empty-support counts and pair-only fooling sets are invalid. Direct synthesis found no actual counterexample; preserve full computational bundle with timeouts labeled UNKNOWN. Primary Jukna paper checked by root: biclique-cover equality is explicitly a single-level AND result, not a general monotone-circuit theorem. No applicable general bipartite theorem was confirmed.

2026-11-25 16:22 UTC — semantic_proof: FULL witness-preserving TopForm normalization compiled (semantic-topform-checked.lean,3430 lines,SHA fdfb24d8d045cad0f978b720b2f353b58c3bf986553f919aab59a197857e61b4). `Normalization.exists_admissible_topForm` produces AO2/T0 circuit of size≤original computing the same output and preserving every nonempty pure OR wire target; no below-output AND lies inside another AND cone. Proof minimizes AND count then AND index sum, uses typed cut/lift for AND readers and compiled OR bypass for OR readers. Thus normalization is now proved in the correct multioutput class; final dirty-gate / star-component accounting remains unproved.

2026-11-25T16:22:16.302570+00:00 ledger_proof: Global dirty-charge obstacle: C4-free graph with baseline points u,v, line pencils B_i,D_j, and centers a_ij adjacent to B_i,D_j. The common conjunction u∧v safely filters every OR(B_i,D_j), because either chosen line activates an existing u/v edge. Forcing any one such OR to true after deleting its center creates the same independent false-positive input {u,v}. Hence the compiled |Q|≤AND cofactor certificates cannot be made disjoint just from their raw-input sets. A global proof must count the uses/merges of the distinct star terminals, or use a stronger circuit-normalization exchange.

- status_review independently approved minimal/no-direct-reader normalization tail (SHA4aa11723...) and protected frontier/global dirty-star charge (componentSHA9126c450...). Protected gate removal pays the prior +1, so |Q|≤branchingAND; no disjointness across centers follows. Both are partial preservation approvals only.

### 2026-11-25 16:27:45 UTC — toolchain_setup: multioutput structural ledger compiled
COMPILED results/orch/lemmas/multioutput-budget.lean,460 lines; immutable scratch multioutput-budget-checked.lean SHA256 9d7c326cdf35a3272e88d2931345ccece0fc16797ef590d29c10e7129aa07fef. MultiBudget.pure_or_multioutput_budget proves 2*|B|+|M|<=C.size+1 for ancestor closure R of output plus any finite set W of nonempty pure-OR wire targets, including unused witnesses. B are R-AND gates with empty singleton output and two singleton-positive operands; M are R-OR gates with output singleton support size>1 and two distinct positive operand wires. No clean-AND assumption. Every zero-support R gate except possibly main output has an R reader; local slot counting includes positive-support ANDs correctly. Main output may be false or invalid. Build exit0 with one stylewarning; source scan clean. Missing semantic inequality |E|+tau<=2|B|+|M| remains unproved, being investigated by ledger agent.

2026-11-25 16:28 UTC — semantic_proof research: Read Jukna 2006 Graphs and Circuits: Some Further Remarks (https://web.vu.lt/mif/s.jukna/ftp/dagstuhl2006.pdf) and author CNF note (https://web.vu.lt/mif/s.jukna/boolean/CNF.html). These concern graph representations on two-hot inputs and do not supply a lower bound for the full edge function; small CNF graph representations remain irrelevant to exact F semantics. Read site paper https://pequalnp.com/papers/note-1 via curl: accepted L-meta-106 already gives exact cycle bound n+ceil(n/2)-1 for n>=5, so C12 cannot refute the posted size inequality; counterexample agent informed.

2026-11-25T16:30:06.297720+00:00 status_review: Located exact master residual ledger in L4183/L5781 and the one-junk closure in L8103. General residual inequality remains an explicit hypothesis in R4185_7. Safe normal-form adaptation must avoid assuming global leastness. Semantic residual witness probes supply a plausible |T|-1 OR credit disjoint from semantic lambda, but the extra component and cover credits are unproved. Details and source lines in lemmas/library-search.md.
