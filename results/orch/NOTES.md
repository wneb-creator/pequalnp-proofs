# L-meta-1031 orchestration

Lease owned only by root. Other agents must not call desk.

Read /tmp/oec/pequalnp-pilot-56/desk-001.json for exact statement and allowed imports.

Current upstream: 9c4fa2b. Reductions allowed but three already live; assess before proposing another.

Each strategy records findings under a distinct heading. Use own files in results/orch/lemmas; only root edits final lean/PEqualNP/Outside/L_meta_1031.lean.

## Reduction/status strategy

- Time: 2026-11-25T01:09:49.161559+00:00.
- Desk assigns L-meta-1031 with reductions_live = 3. Upstream already has R_meta_1031_1, _2, _3. Current join caps at three live reductions per step, so a fourth is not permitted.
- R_1031_1: useful least circuit (each AND owns an edge), plus an exchange that strictly decreases the count of AND gates owning two disjoint edges while preserving usefulness and not increasing size. Triangle-free pairwise-intersecting edge families are stars.
- R_1031_2: existence of a least circuit where all AND gates are semantically below the graph function, plus cleanup eliminating AND gates with empty ownership while retaining soundness.
- R_1031_3: existence of a least HasStarProfile circuit (empty ownership allowed), plus cleanup eliminating empty ownership preserving profile.
- EXACT reusable second hypothesis of R_1031_2 is checked in L_meta_1906.lean (theorem near line 897). The first hypothesis appears still open (no L_meta_1905 file). L_meta_1600.lean shows a sound AND has star-or-empty ownership in any C4-free graph.
- L_meta_4846.lean proves two disjoint owned edges force an accepted nonedge pair at the gate. This suggests a weaker normal-form target: only pair-soundness, not soundness on all assignments. Pair-soundness plus no triangles implies star-or-empty profile. Need both a least pair-sound circuit and nonempty ownership; neither follows from current source findings.
- L_meta_5355.lean constructs a useful monotone circuit of size at most edge count + vertex-cover cardinality - 1. No general matching lower bound was found; using that bound would assume the unresolved main structure question.
- Import restriction allows only Mathlib and PEqualNP.Defs: outside lemma source must be copied into the single final file if used, not imported.

## Counterexample strategy 2026-11-25T01:10:47.324437+00:00

- Empty graphs including n=0 admit the zero-gate circuit with out-of-range output, so no trivial refutation. Forward references read false; unused/identity/constant gates can be removed from minima of nonconstant edge functions.
- R_meta_1031_2 proves the star conclusion given a minimum circuit with globally sound AND gates and pruning to nonempty owners.
- No installed SAT solver found. A Z3 binary download was attempted, but curl failed before writing bytes when disk had only 26 MB free; abandoned pending toolchain cleanup.
- Plan: exhaustive normalized small circuits for all triangle/C4-free graphs on up to four vertices, then SAT or larger stochastic search if resources permit.

### Small-case circuit census 2026-11-25T01:11:46.541660+00:00

Standalone C++ truth-table search enumerated all binary AND/OR circuits with distinct nonconstant gate functions and no duplicate gate outputs, using earlier distinct wires. Arbitrary references/constants/identities are excluded by standard normalization (not yet Lean-proved), so results are computational evidence only.

- n=4, depth4:81,985 prefixes; all37 nonempty triangle/C4-free labeled graphs found at a minimum size1–4 with every AND owning a nonempty star.
- n=5, depth5:27,160,961 prefixes; all290 nonempty labeled forests found at a minimum size1–5 with every AND owning a nonempty star. Remaining12 cases are5-cycles, lower bound>5.
- Code and full output: scratch counter_small.cpp, counter_n4.log, counter_n5.log.

## Lemma inventory strategy

PEqualNP.Defs gathers 86 definition modules; bounded declaration search found no theorem/lemma declarations in Defs/*.lean. Useful data definitions include coverCircuitB, graphFun, Owns, HasStarProfile. Existing Outside L_meta_539 contains a short Nat.find argument (around line 2738), but no such result is available through the allowed imports.

Created inventory_minimum.lean: generic existence of a minimum AND/OR fan-in-two circuit from any witness. Created inventory_existence.lean: explicit edge-list accumulator construction for every finite graph (including empty graph and n=0). Neither has been compiled yet; waiting for cache readiness and ENOSPC recovery.

## Proof strategy: pair soundness

The full normalization target may be weakened to pair soundness of every AND gate. For n>0, if an AND gate being true on pairInput u v always implies G.Adj u v (u=v included), every AND gate globally implies the graph function. Choose the earliest true AND at an arbitrary input x. Its true inputs trace through OR-only paths to true vertices of x; fan-in at most two supplies a pair. Arity zero or one contradicts pair soundness on u=u. The arity-two case supplies the graph edge. n=0 must be handled separately by the empty circuit.

Uncompiled experiment: results/orch/lemmas/proof_pair_sound.lean, 309 lines. It reuses local wire/cone machinery from checked L_meta_4846, renamed under the task namespace. No theorem imports outside Defs and Mathlib. Awaiting toolchain/cache.

### Five-cycle completion 2026-11-25T01:12:52.612832+00:00

Depth6 normalized census:1,460,469,821 prefixes in20.4seconds; no labeled5-cycle function occurs. A7-gate star circuit is OR(1,4),AND(0,5),OR(1,3),AND(2,7),AND(3,4),OR(6,8),OR(10,9), output11. Together these cover every triangle/C4-free graph on≤5vertices computationally (normalization is not formally established). A separate search found no minimum five-vertex forest circuit with nonstar or empty AND ownership.

Next: stochastic synthesis for Petersen and Fano incidence graphs against all edge inputs and maximal independent sets. For monotone circuits these cases characterize the entire edge function, reducing from2^n assignments to a small truth vector.

## Root literature check (2026-11-25)
Read Stasys Jukna, Disproving the Single Level Conjecture, primary author PDF https://web.vu.lt/mif/s.jukna/ftp/single1.pdf via web tool. General quadratic single-level normalization fails; examples in paper use saturated graphs with cliques, so do not directly refute our C3/C4-free claim. The paper distinguishes formula and arbitrary-fanout circuit lower bounds, which must not be conflated. No confirmed literature proof of the present normalization.

## Scratch storage
The environment had no advertised Lean installation or warm cache. Pinned Lean 4.36.0 was installed under /tmp/oec/pequalnp-pilot-56/lean-4.36.0-linux; due to a 7.9 GB overlay limit, its immutable files are backed by job-specific /dev/shm/pequalnp-pilot-56 and linked at that scratch path. Full Mathlib cache is being restored authentically; checker requires whole Mathlib. No tracked toolchain/configuration file changed.

## Relevance prerequisite (2026-11-25T01:17:57.234771+00:00)

Independent normalization reasoning found no valid whole-region exchange yet. Simple bypass is insufficient: (a∨b)∧(c∨d)∧(a∨c) computes the P4 edge function ac∨ad∨bc but the earliest AND owns disjoint edges; it uses 5 gates versus a 4-gate clean circuit. Sharing among later cleaners is the unresolved issue.

Created results/orch/lemmas/relevance.lean: deletion circuit with missing gate redirected to an out-of-range false wire; semantic proof gives pointwise decrease and equality whenever that gate was false. The final lemma minimum_gate_edge_live says every gate in a least monotone binary circuit computing any graph function is true on some graph-edge pair input. No cycle assumptions. Base wire semantics copied from checked L_meta_1906, renamed into the task namespace. Not compiled yet; cache setup/compile queue pending.

### Larger graph search 2026-11-25T01:21:01.372110+00:00

Exact semantic test compression: a monotone circuit computes graphFun iff it is true at every edge pair and false at every maximal independent set. Petersen has15+15=30 such cases; Fano incidence21+37=58.

Five-minute stochastic searches from canonical star-cover circuits with one gate removed found no exact circuit: Petersen19gates,3,559,004,844 evaluations/74,031restarts; Fano26gates,3,372,699,873 evaluations/69,362restarts. Both best candidates miss one test.

Z35.3.3 installed under scratch(84MB). Dirty-AND queries at canonical optimum: C5k7UNSAT1.26s; C6k8UNSAT9.03s; C5withleafk8UNSAT11.32s. All evidence depends on model normalization and untrusted SAT, not Lean. Sanity C5k7unconstrainedSAT0.35s, full32inputvalidation passed. Its nested-AND circuit is AND01,OR03,OR13,AND(2,7),OR(4,5),AND(6,9),OR(8,10),output11. ANDgate5(in wire10) owns04,34 and inherits01 fromANDgate0. Thus bottom-level-only form is false for arbitrary optima even though AND-soundness survives.

Petersen19and theta(2,3,3)10gateSAT searches underway. Theta graph has7vertices8edges,alpha3,tau4,canonical11gates.

Inventory checkpoint 2026-11-25T01:23:06.373199+00:00: named L_meta_1031.lean generic minimum helper passed lake build (5149 jobs, exit0). Full logs first-partial-build.stdout/.stderr under scratch. No assertion of posted star theorem yet.

## Star special case (2026-11-25T01:24:33.169600+00:00)

Created results/orch/lemmas/star_minimal.lean. The generic dependency-set bound from checked L_meta_1088 is generalized to any essential input subset. This yields degree(c) <= circuit size for every binary circuit computing any graph edge function, without monotonicity or girth assumptions: center plus its neighbors are all essential variables. An OR chain over neighbors followed by one AND achieves this bound on graphs whose edges all share c. The draft star_optimal then derives the entire posted ownership/minimality conclusion for this class, including isolated vertices and the empty graph. Awaiting compile slot; no checked claim yet.

Inventory extension drafted: inventory_star.lean strengthens the explicit edge-list compiler so every AND reads two original inputs forming a G edge. Generic direct-gate evaluation and absence of gate ancestors imply nonempty star ownership. Hence every finite graph has some such circuit, independent of C3/C4 hypotheses; this witness is not claimed minimum. Compilation pending.

## First replan
Direct bypass of an earliest unsound AND is insufficient: the P4 example needs a downstream rewrite. This local strategy is dropped. General normalization remains open. Active work: compile pair soundness and gate-relevance prerequisites; compose a conditional bridge to the exact statement; complete optimal star case; focus counterexample synthesis on small graphs with multiple long cycles. Every partial is labeled explicitly and no proof PR is opened without the exact theorem and checker.

### Pair-sound compile status 2026-11-25T01:27:50.316054+00:00

First attempt was interrupted by root instruction after several minutes of broad Mathlib startup with no diagnostics (exit130). Complete stdout/stderr: proof-pair-build-001.log (empty). Removed broad Mathlib import; next attempt uses only Defs and LAKE_ARTIFACT_CACHE=false. Mathematical proof review found no additional assumptions needed beyond n>0.

### Toolchain/cache setup completed

Full pinned Mathlib cache: all 9,117 files unpacked successfully (exit 0); logs in scratch mathlib-cache-unpack.stdout/.stderr. Toolchain and selected authentic Mathlib output directories use job-specific /dev/shm/pequalnp-pilot-56 backing. Every future build/env command must set LAKE_ARTIFACT_CACHE=false; tools/build.sh honors that exact setting. Generated shared cache was cleared after proof-pair-build-001 exited 130, reclaiming 370 MB; genuine tree outputs were preserved (no tree symlink targeted the removed cache). The proof_pair_sound experiment should use Defs-only imports to reduce startup memory.

Inventory result 2026-11-25T01:28:24.599103+00:00: inventory_existence.lean passed Lean exit0 using only PEqualNP.Defs. Its graph_has_minimum proves the first three conjuncts of L-meta-1031 for every finite graph; the same minimum witness is not yet known to have star ownership. The only initial error was getD simplification after append, fixed using getElem?_append_left. 119lines. Complete logs inventory-existence-02.stdout/.stderr.

### Pair soundness checked 2026-11-25T01:31:51.229656+00:00

proof_pair_sound.lean passed pinned Lean via Defs-only imports, LAKE_ARTIFACT_CACHE=false, exit0; complete log proof-pair-build-003.log is empty. Source310lines. The original wire/cone helpers are copied from checked L_meta_4846 under the task namespace; pair_sound_global is the new deduction.

Prepared proof_bridge.lean (1812lines,88218bytes, uncompiled): copies checked L_meta_1906 pruning proof into the local Prune namespace and R_meta_1031_2 into normalize_bridge. The new finish_from_pair_normalization composes them with pair_sound_global, handling n=0 by minimality against the empty false circuit. Its sole hypothesis remains existence of a minimum pair-sound AND/OR circuit for each allowed graph. This is research material, not a complete proof or a new reduction submission.

Independent review of relevance.lean: trim_semantics and minimum_gate_edge_live correctly handle sentinels, forward references, monotone deletion and graph-minterm preservation. The conclusion is edge activity, not edge ownership.

### Star special case checked (2026-11-25T01:33:07.934824+00:00)

star_minimal.lean compiled with exit 0 on the second run (star-minimal-002.stdout/.stderr, warnings only). All lower bounds and the final star_optimal lemma are now Lean-checked. The final lemma uses explicit OwnsExplicit matching the posted TransGen ownership formula, not the library cone variant. It adds the explicit hypothesis that every edge contains a fixed vertex; no general-girth result is claimed. Root was notified immediately for preservation and independent review.

### Relevance checked 2026-11-25T01:33:55.143484+00:00

relevance.lean passed Lean compilation (exit 0, 327 lines, no output/warnings) using Defs only; full log /tmp/oec/pequalnp-pilot-56/relevance-002.log. Independent semantic review by proof_strategy passed. Final lemma: every gate of a least monotone binary circuit computing any graph function is true on some graph-edge pair. This is a prerequisite, not the ownership conclusion. Preparing stronger essential-edge witness in separate relevance_essential.lean so the checked original remains unchanged.

Inventory result 2026-11-25T01:34:40.589668+00:00: inventory_star.lean passed Lean exit0 (229lines), only PEqualNP.Defs. graph_has_stars establishes the posted nonempty-star ownership property for a computing AND/OR binary circuit on every finite graph, with no minimum clause. This is a separate witness from graph_has_minimum; the common-witness/minimum normalization remains unresolved. Complete logs inventory-star-02.stdout/.stderr.

### Normalization literature and essential-edge extension 2026-11-25T01:34:58.636049+00:00

Read Ingo Wegener, The Complexity of Boolean Functions (1987), section 6.6 Corollary 6.1, printed page 166 / PDF page 176, on 2026-11-25: https://cseweb.ucsd.edu/classes/fa23/cse248-a/papers/logic/cobf.pdf . For OR-output families whose pairwise supports intersect in at most one variable, optimal monotone circuits use OR gates only. This blocks directly using AND-assisted Boolean-sum savings with C4-free incidence. It does not establish a reduction from a quadratic graph circuit to its separate neighbor sums.

Root captured the checked edge-live source as relevance_edge_live.lean. The essential-edge extension now lives in relevance.lean (temporary duplicate relevance_essential.lean was removed). New lemma minimum_gate_essential additionally exhibits an edge pair whose output becomes false after the chosen gate is deleted with false redirection. Compile pending.

### Conditional bridge checked 2026-11-25T01:35:38.165304+00:00

proof_bridge.lean passed pinned Lean on first attempt, exit0. Compiler emits only an inherited unused instance-binder warning from copied L1906. The exact posted conclusion is proved under the sole explicit pair-normalization hypothesis. This does not settle L-meta-1031. Full compiler outputs and source SHA256 values are now in results/orch/proof-validation.txt. Independent review requested from status_review.

### Edge-essential strengthening checked — 2026-11-25T01:41:46.464529+00:00

`results/orch/lemmas/relevance.lean` now compiles (exit 0, empty complete log `/tmp/oec/pequalnp-pilot-56/relevance-003.log`), 389 lines, SHA256 `9223bad0e58e7d29c99d3abcfdd2db0e735d98ff2d85abf5ad9074d8ad759bcf`. New `Rel.minimum_gate_essential` states every gate of any minimum monotone binary circuit computing a graph edge function is essential on some graph-edge pair: the gate is true there and deleting it via the checked false-sentinel construction makes the output false. No girth assumptions. Proof preserves all edge minterms if no such witness exists, uses monotonicity to preserve the whole function, and contradicts strict size decrease. This strengthens the checked edge-liveness lemma but does not imply ownership. Source frozen for root checkpoint. Agent proof_strategy is using it to prove global soundness of the last AND gate.

## Weaker profile route 2026-11-25T01:43:17.233293+00:00

R_meta_1031_3 has two unfinished obligations. A: every triangle/C4-free graph has a minimum Monotone2 circuit computing graphFun G empty with HasStarProfile (empty-owned ANDs permitted). B: given such a minimum profile circuit, find an equally small computing profile circuit where every AND owns a graph edge. A is exactly the conclusion of R_meta_2448_17. No checked theorem directly matches A or B; cached 01:05 public map marks L2448/L2449 conjectures, L1905 conjecture and L1906 checked. L1908/1910/1912/1914/1916/1918 instead concern a fixed nine-input Petersen-fragment lower bound and are not these children.

R2448_17 reduces A further to: (i) a minimum circuit whose owned-edge relation r(C,j,a,b)=G.Adj a b and Owns n C j a b has a connecting owned edge between any two owned edges (no induced matching of size two); (ii) a sequential exchange extending the prefix of star gates by one while retaining minimality and an eligible profile (empty, double-star, or five-cycle with singleton acceptance). The reduction itself classifies these profiles; neither exchange hypothesis was found checked.

The profile route is genuinely weaker semantically, but needs two new steps rather than the pair-sound route's one missing minimum witness. L1906 does not discharge B: its cleanup uses global AND soundness to lift previously computed subfunctions to the output. HasStarProfile says nothing about singleton or nonedge acceptance, so the required lift inequality is absent. An earliest-star AND can sometimes be narrowed to its center without changing graph-edge inputs, but its remaining OR operand may include nonneighbors and may be shared elsewhere; pruning this operand independently can grow the circuit or change another output path. No valid global exchange proved.

### Last-AND soundness checked 2026-11-25T01:43:33.461913+00:00

proof_last_and.lean (493lines) passed pinned Lean first attempt, exit0, no diagnostics. It copies status_review's checked relevance/essential-edge helpers and adds last_difference and minimum_last_gate_sound. The former traces deletion-sensitive wires when all gates after the removed gate are OR; the latter proves a minimum graph circuit's last AND (indeed any gate followed only by ORs) globally implies the edge function. This requires no triangle/C4 restriction. Source frozen for consolidation and independent review.

Remaining exchange obstruction: a sound last AND can inherit edges through dirty earlier ANDs, and its singleton-support biclique does not itself replace that inherited residual without cost. No global size-preserving exchange has been established.

Consolidation 2026-11-25T01:45:14.742868+00:00: results/orch/lemmas/consolidated.lean passed Lean exit0 on first attempt.3027lines/144376bytes, SHA256c3cf7ffffc50b449695e13e6f99914ffcea66ad0eec640bf7bfa612eccc32102. Includes graphminimum/starconstruction, emptygraph, pair-soundness and conditional bridge, edge-live/essential/lastAND, staroptimality. One Defs import,154distinctdeclarations, all ownnamespaces. Explicit partial only: no module-named final theorem. Full logs and validation copied to results/orch/consolidated-build.stdout/.stderr and consolidated-validation.txt.

### 2026-11-25 01:45 UTC — unrestricted gate-count route (lean_setup; timestamp corrected from an approximate label)

The possible route `size >= |E| + vertexCoverNumber - 1` remains UNPROVED.
Separate bounds `ANDcount >= vertexCoverNumber` and `ORcount >= |E|-1` agree with the counterexample agent's finite synthesis, but are substantially stronger than formula or single-level bounds. No formula-to-DAG transfer has been justified.

A valid weaker counting invariant is available on paper: a monotone fanin-two circuit with k AND gates has at most 2^k prime CNF clauses. For each global choice of one input at every AND gate, replace all ANDs by these inputs. The result is an OR-only circuit and hence one clause (possibly constant). The original function implies every resulting clause. Conversely, for any zero input of the original circuit, choose a false predecessor at every false AND; the resulting OR-only output is false. Thus the conjunction of the at-most-2^k clauses equals the original function, and every prime clause occurs among them. For graph edge functions this yields `#maximalIndependentSets(G) <= 2^ANDcount`. Constants and unary gates do not increase the number of choices. This is not yet formalized in Lean.

Counterexample agent reports exact MIS totals: C5=5, C6=5, C8=10, Theta(2,3,3)=7, Petersen=15, Fano incidence=37. Therefore C5/C8 AND lower bounds have this simple explanation, whereas Theta/Petersen/Fano exact vertex-cover bounds need more.

Primary literature checked 2026-11-25: Jukna, Disproving the Single Level Conjecture, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf (2006), section8 explicitly listed an explicit superlinear quadratic-function circuit lower bound as an open problem at that time. No claim about its current status is made. The author's slides https://web.vu.lt/mif/s.jukna/papers/single-dag5.pdf slide14 give `Formula_+(f_G) >= |E|/2` for C3,C4-free graphs; this is a formula result, not an unrestricted circuit result. A sharp OR-count lower bound for these graphs would imply explicit superlinear quadratic-function circuit lower bounds, explaining why a direct potential is elusive.

The gate-elimination idea is also UNPROVED: seek a nonisolated vertex v whose zero restriction saves at least degree(v)+1 gates whenever G is not a star; combine induction with `tau(G) <= tau(G-v)+1`. The checked star case supplies the base. Shared dirty intermediates remain the obstacle, and no such vertex has been established generally.

### Downstream ownership/count audit — 2026-11-25T01:47:06.312533+00:00

Bounded search of accepted Outside L-files found no direct theorem that nonempty-star ownership implies the exact |E|+vertex-cover−1 size lower bound. `L_meta_1601` and `L_meta_1602` explicitly assume the global AND-sound lower-bound theorem and merely transport it; they do not establish that missing theorem. `L_meta_1983` proves Fano size≥27 under no AND-in-AND-cone, stronger than the posted ownership condition. `L_meta_1762` and `L_meta_2660` give constant-factor bounds on soundly owned edge counts, too weak for exact finite refutation. `L_meta_1491`/`L_meta_4183` provide the useful TopForm inequality |E|+noncentreless_tops+2·centreless+junk+unused_OR ≤ size+|Ustar|+1; L1491 additionally bounds a cover of G\Ustar by noncentreless_tops. The uncontrolled Ustar term is the precise remaining obstruction. `L_meta_1733` constructs a minimum TopForm circuit, but only bounds |E\Ustar|≤size+1. Thus a SAT circuit below the canonical |E|+τ−1 construction alone would not yet be a Lean refutation of L-meta-1031.

Potential unproved charging angle: if every dirty AND owns a star, its centre can cover its contributed Ustar edges. To close the TopForm inequality, charge those edges against OR gates outside the top λ regions. A dirty gate owning k star edges plausibly needs k−1 leaf-combining ORs and one extra OR for contamination or mixing an earlier dirty AND; C4-freeness limits sharing between distinct true-star centres. This remains only a heuristic: OR bundles may include contaminants and be shared by several dirty regions, so the standard (1,1)-disjoint exact-OR-family theorem does not apply directly.

### Second replan — 2026-11-25T01:48:29.654398+00:00

Consolidated partial source (3027 lines) passes the named lake build and is pushed in9776a062b6d92789586c08412efef19dc4b8b3dc. Full normalization remains unproved. Separate minimum existence and star-ownership constructions cannot be combined by choosing unrelated witnesses. Pair-sound normalization remains the shortest conditional bridge; the weaker profile route has additional unproved cleanup obligations. Finite searches have produced no refutation.

Refocus: inspect the accepted forest lower-bound induction for stronger input-restriction exchanges on cycles; pursue factorization at the globally sound last-AND boundary; continue cyclic sparse-graph count and ownership synthesis with independently checked encodings. The global OR/AND counting route is conjectural and is not being assumed in Lean. A forest-special-case extension is being assessed for a reasonable dependency footprint. No proof acceptance, checker success, or new PR is claimed.

### Clean-boundary factoring observation (lean_setup, 2026-11-25)

Assume a circuit has already been normalized to an OR aggregation of clean AND boundary gates, and these gates have no readers except that aggregation. If two boundary gates have a common input wire h, say `h AND a` and `h AND b`, replace them by `h AND (a OR b)`. Two AND gates and their one unit of aggregation cost are replaced by one AND and one OR: total size drops by one. The OR aggregation can be reassociated without changing its gate count. This does not use girth. Consequently a minimum circuit in such a boundary normal form cannot share one wire directly between two boundary ANDs. The conclusion is conditional on the actual boundary normal form and absence of other readers; it is not a general normalization proof.

The unclosed step is sharing deeper inside dirty cones, for example boundary terms `(h OR a) AND p` and `(h OR b) AND q`. Distributing these creates an extra product term, so the direct factorization no longer saves a gate. If h has at least two singleton implicants and p,q expose distinct singleton centers, soundness forces a C4. However p/q may themselves contain dirty nonlinear pieces, and assuming they are singleton centers would be circular. No general reduction from these dirty contexts has been established.

Small-case evidence from counterexample agent: dirty-AND queries at exact standard bounds are UNSAT for C5 (7 gates), C6 (8), and C5+leaf (8). Theta(2,3,3) has n=7, E=8, tau=4, bound11; its dirty11 and unconstrained10 queries timed out. A C5 circuit with three ANDs can be dirty but uses ten total gates, confirming that AND-count optimization differs from minimum total size.
