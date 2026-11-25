# pequalnp-pilot-66 — L-meta-1772

Assigned 2026-11-25 03:31:12 UTC. Only root owns and renews the lease.

## Target

∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11

## Coordination

Agents work in separate files under results/orch/lemmas or job scratch. Append timestamped findings here. Root integrates the final single Lean file. Notify root immediately when a new Lean component compiles.

## Environment

Lean 4.36.0 installed in /tmp/oec/pequalnp-pilot-66/elan. Set ELAN_HOME to that path and put its bin directory on PATH. Pinned Mathlib cache for PEqualNP.Defs fetched successfully. Base build is in progress. Do not build Mathlib from source, run lake update, or call the desk.

## Status

One null desk response before assignment. Desk lists reductions_open=true, reductions_live=3; full proof is preferred and reduction availability must be checked before submission.

### 2026-11-25T03:32:55.355247+00:00 — counterexample strategy

No boundary counterexample: edgeless graphs (including n=0) use the zero-gate circuit with out-of-range output n, so ownership is vacuous and size zero is minimal. Existing R_meta_1772_418 already proves this case. Checked definitions include invalid wire reads as false; no implicit ReadsBack assumption. Ownership excludes every earlier true AND in the strict syntactic cone, so it is stronger than being pivotal on an edge. Working on exhaustive n≤4 monotone-circuit checks and C5.

## 2026-11-25 03:32:57 UTC — rules_review: existing proofs

- R_meta_1772_773 reduces to existsLeast, pivotal, repair-by-decreasing-number-of-unowned-ANDs. Exact solved children: L_meta_2666.lean:120 (existsLeast; whole file 146 lines) and L_meta_2668.lean:459 (pivotal; whole file 460 lines). Repair remains the substantive ownership transformation.
- R_meta_1772_642 reduces to star construction plus handling circuits strictly cheaper than every vertex-cover star bound. Exact star child solved by L_meta_5355.lean:399 (401 lines).
- R_meta_1772_418 reduces to nonempty leafless core and restoration of a pendant edge; its proof already includes an explicit zero-gate empty-graph base case.
- L_meta_1906.lean:897 is an ownership-cleanup theorem assuming every AND gate is globally below the graph function. It preserves size and function and makes every AND own an edge; could be used if sound-AND normal form can be proved. Its induction does not use the triangle/four-cycle/minimality hypotheses in its main theorem.
- Generic erasure infrastructure: L_meta_2668.lean:195 bypass_rel, :243 bypass_eval_rel, :259 bypass_eval_eq, :267 bypass_eval_unread, :320 erase_eq_bypass, :348 wire_monotone, :379 bypass_mono, :395 lost_edge. These permit invalid/future wires and are likely better suited to the public Monotone2 target than L_meta_2859, which additionally assumes ReadsBack.
- L_meta_2859.lean:325 proves eraseGate preservation of Monotone2/ReadsBack, exact size drop, and evaluation equality when removed gate equals redirect; :234 main_clean is reusable generic formulation. L_meta_2586.lean:366 proves AND-bypass increasing evaluations and equality when operand equals gate, but theorem specializes n=26.
- All mentioned Outside proof bodies require transplanting into the final own namespace, since assigned imports permit only PEqualNP.Defs and Mathlib. Definitions themselves supply no elimination/minimizer theorems.

### 2026-11-25T03:34:17.844430+00:00 — small-case computations complete

Exhaustive semantic-state BFS over normalized monotone circuits found minimum ownership witnesses for all labelled no-triangle/no-four-cycle graphs on 1,2,3,4 vertices: respectively 1,2,7,38 graphs. On four vertices the maximum minimum size is 4; breadth layers contain 12,114,988,8291 states. Every saved witness has each AND owning an edge. Constants/unary/semantically redundant gates are excluded from search, so minimum claims use the usual informal elimination argument, not a Lean proof. An explicit seven-gate C5 circuit has three ANDs owning {01,04}, {12,23}, {34}; only construction/ownership was checked, not the C5 lower bound. Code, full log, and JSON witnesses are scratch/small-circuits.py, scratch/small-circuits.log, scratch/small-circuits-n*.json where scratch=/tmp/oec/pequalnp-pilot-66.

## Sound-AND route 2026-11-25T03:34:39.255683+00:00

The desired sound-AND existence is exactly the still-unproved child L-meta-1904 of R_meta_1031_2. All three published reductions of that child isolate a hard normalization/lower-bound issue. R_meta_1904_493 supplies a useful checked bridge: if every AND gate rejects every independent assignment of support at most two, then every AND gate is semantically sound on all assignments. Its proof takes the first offending AND on an independent input; earlier active wires have a singleton literal witness, so the two operands yield a support-of-size-at-most-two counterexample. This removes large independent inputs from the soundness problem.

R_meta_1904_137 reduces sound existence to singleton normalization and the sharp bound |E|+vertex-cover ≤ gate count+1; R_meta_1904_271 treats forests/cycles separately but leaves the same sharp bound on the remainder. No existing proof of the needed general normalization was located yet.

## 2026-11-25 03:35:40 UTC — rules_review: reduction cap and packaging

- Public join.txt says at most three live reductions per step, one per agent. Root reports current reductions_live=3; therefore no fourth reduction slot is available now. reductions_open=true enables reductions generally, not additional capacity. Existing R1772 files are consistent with the counter but their existence alone does not prove liveness. The repository guard checks the reductions flag but has no live-count test; acceptance by the local Lean checker would not override the desk cap.
- Push artifacts by an explicit allowlist: Lean source, sanitized mathematical NOTES/TIMELINE, build/checker output, and validation metadata. Keep desk responses/lease material, installation archives, generic command transcripts, configuration files, credential-related diagnostics, and unrelated scratch out of commits. No credential contents were inspected during this review.
- Every intermediate push must identify its result as conditional/partial unless it proves the exact target. Final PR tree must add only the named Lean file; retained earlier commits can preserve removed results artifacts in branch history.

## Minimality strategy — 2026-11-25T03:35:56.474805+00:00

- L_meta_2668 already proves the pivotal-edge-under-erasure property for every gate in every minimal monotone circuit; its 460-line helper suite is reusable without Outside imports.
- L_meta_3760 (10,039 lines) excludes exactly one dirty AND for bipartite C4-free graphs. Its proof uses bipartite parity beyond triangle-freeness: lines 8433 and 8504–8533 exclude an edge qb-v where qb and zstar share a neighbor c′ and zstar and v share a neighbor um. This would form a 5-cycle, allowed by our hypotheses.
- New checked component results/orch/lemmas/MinimalProof.lean exhibits C5, proves triangle-freeness and NoFourCycle by kernel evaluation, and disproves that local parity weakening. This is not a refutation of the posted target. Build: lake env lean ../results/orch/lemmas/MinimalProof.lean, exit 0; log /tmp/oec/pequalnp-pilot-66/minimal-proof-build.log.
- Literature: read Jukna, Disproving the Single Level Conjecture (SIAM J Comput 2006), https://web.vu.lt/mif/s.jukna/ftp/single1.pdf on 2026-11-25. General sound-AND/single-level normalization cannot hold for all graphs; the paper separates quadratic single-level and unrestricted monotone circuits. Its counterexamples contain triangles, so they do not settle our target.

## Normalization agent — 2026-11-25 03:36:12 UTC

- Compiled `results/orch/lemmas/NormalForm.lean` (952 lines), adapted from checked `L_meta_1906.lean`, all declarations under `PEqualNP.Outside.L_meta_1772.Normal` and importing only `PEqualNP.Defs`.
- `normalize_sound` transforms any monotone graph circuit with all ANDs globally `BelowF` into a no-larger circuit whose every AND owns an edge.
- `minimum_sound_to_owned` preserves minimality and yields the exact desired conclusion from a minimum sound-AND circuit. Triangle and four-cycle restrictions are needed only for the remaining soundness existence problem.
- Command: `ELAN_HOME=/tmp/oec/pequalnp-pilot-66/elan PATH=/tmp/oec/pequalnp-pilot-66/elan/bin:$PATH lake env lean ../results/orch/lemmas/NormalForm.lean` from `lean/`; exit 0; full output `/tmp/oec/pequalnp-pilot-66/normal-form-build.log` is empty.
- Research read 2026-11-25: Jukna, Disproving the Single Level Conjecture, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf. Its separating constructions are saturated graphs with triangles, so do not refute this target. Page 10 discusses a lower bound of edge count for single-level circuits on K2,2-free graphs; this cannot be assumed for unrestricted circuits.

## Algebraic route — 2026-11-25T03:37:35.434266+00:00

A gate false-positive on two vertex-disjoint nonedge pairs has at most four killing centers in a C4-free graph. Proved in `results/orch/lemmas/AlgebraicRoute.lean` (`wmax_card_le_four`), using monotonicity adapted from L_meta_5403 and four common-neighbor bounds. `lake env lean` passed; full log in job scratch `algebraic-route-build.log`. This is a local support restriction, not the posted theorem.

Odd-cycle obstruction: the dirty gate `(a OR c) AND (b OR d)` can have three killing centers in a C7. Put graph edges `bc`, `a-w1`, `c-w1`, `b-w2`, `d-w2`, `a-w3`, `d-w3`; each gate AND x_wi is below graphFun, despite no triangle or C4. Thus two-center restrictions cannot be assumed from girth>=5 alone. This observation is mathematical, not yet Lean checked.

Broad degree-two projection fails to preserve gate count automatically: later AND gates can filter false-positive pairs and singleton terms from earlier products. Existing L_meta_1733 gives TopForm but permits multiple dirty ANDs; L_meta_3760 eliminates one dirty AND under bipartiteness, and L_meta_4846 controls disjoint owned edges. No complete normalization argument obtained.

### 2026-11-25T03:39:07.649326+00:00 — solver-based search

Installed no system packages. Built official CaDiCaL rel-3.1.0 from its GitHub source archive in job scratch (small executable). scipy MILP encoding found and fully validated C5 7-gate circuit in16.9s. Equivalent SAT encoding found one in0.075s and reported UNSAT for6 gates. Positive tests are edges, negative tests maximal independent sets; monotonicity makes those tests complete. CNF uses binary AND/OR, earlier distinct operands, output last, no unused gates, and nondecreasing larger operand order. The syntactic normalization assumptions are not Lean checked. Current runs: Petersen19 gates (<20 star bound) and C5 minimum7 with some AND true on singleton.

### Sound-AND/P4 sharing component 2026-11-25T03:40:38.685890+00:00

Checked `results/orch/lemmas/SoundAnd.lean` with `lake env lean` (exit 0, full empty log `/tmp/oec/pequalnp-pilot-66/sound-and-build.log`). It proves `path_factor_guards`: for P4 edges a-c, a-d, b-c with a≠b and c≠d, under no triangles/no 4-cycles, a sound literal guard p∧(a∨b) forces p=c; a sound q∧(c∨d) forces q=a; and no sound r∧(a∨c) exists. This rules out sharing the P4 filter factors with fresh sound star centers. It leaves same-center reuse and readers whose opposite operand has only dirty-gate support. Helper statements are in the allowed final namespace L_meta_1772_aux and use only PEqualNP.Defs.

## Killer-pattern extensions — 2026-11-25T03:41:04.508455+00:00

`SharedKillers.lean` proves that two gates with disjoint nonedge witnesses have at most four shared killing centers under NoFourCycle. `KillerPatterns.lean` proves sharper restrictions with triangle-freeness: two nonedge witnesses ab,ac in one gate and edge bc force every killing center adjacent to a; disjoint witnesses ab,cd in two gates plus cross edges ac,bd allow at most two shared killers; adding cross edge ad allows at most one. Both compile under `lake env lean` with only PEqualNP.Defs; full logs `shared-killers-build.log`, `killer-patterns-build.log` are empty (exit0). These are support restrictions toward repair, not proofs of the full posted target. Files frozen for independent review/push.

### 2026-11-25T03:41:48.826593+00:00 — checked C5 construction

`results/orch/lemmas/Counterexample.lean` compiles with only PEqualNP.Defs. It defines an explicit seven-gate C5 circuit and proves Monotone2, exact graph function equality, every AND owns an edge, and size7 by ordinary kernel reduction. It does not prove minimality or refute the target. Full log: scratch/cycle-five-lean.log (one letI style warning). Independent SAT checks found C5 six-gate UNSAT and seven-gate singleton-dirty UNSAT; C6 seven-gate UNSAT and eight-gate singleton-dirty UNSAT. Larger cycles/theta graphs and Petersen searches running; full logs retained.

## Single-ancestor ownership exchange — 2026-11-25T03:41:58.104337+00:00

- `SingleAncestor.lean` now compiles: `dominated_single_ancestor_owns` proves an AND gate j with unique possible strict-cone AND ancestor i must own an edge if gate_i globally implies gate_j. Redirecting j to i decreases all outputs, preserves every edge input, and contradicts minimality.
- `shared_ancestor_in_all_sides_owns` derives this domination when every operand of j reaches i through an OR-only path with valid earlier-wire reads.
- `AncestorDichotomy.lean` now compiles: `unowned_single_ancestor_is_filter` proves an unowned j has valid earlier-wire operands, at least one OR-only path to i, and at least one operand lacking such a path. Together with fan-in <=2 this leaves exactly a one-sided filter. This is direct ownership progress and does not require triangle/C4 assumptions.
- Both self-contained helper files are frozen for root review and preservation. Full logs: `/tmp/oec/pequalnp-pilot-66/single-ancestor-build.log`, `/tmp/oec/pequalnp-pilot-66/ancestor-dichotomy-build.log`. Warnings only, no errors.

## Local normalization — 2026-11-25 03:42:46 UTC

- `LocalNormalForm.lean` compiled: TopForm + soundness only of AND ancestors active on a selected edge implies ownership. The condition can be limited to nonowning gates. No transformation theorem preserving this local condition has yet been proved.
- `SoundOperand.lean` compiled: for every minimum Monotone2 circuit, every valid input wire of an AND gate has a witness where that wire is true but the circuit output is false. The proof bypasses the AND gate upward on all inputs if the operand were globally below the output, contradicting minimum size. This is independent of graph restrictions. Bypass infrastructure adapted from `SingleAncestor.lean`; new lemmas `no_sound_and_operand` and `and_operand_has_false_witness`. Full log `/tmp/oec/pequalnp-pilot-66/sound-operand-build.log`, exit 0 with only inherited deprecation/linter warnings.
- Corrected earlier majority-of-three example: K3 has a sound 4-gate circuit; its 5-gate CNF is not a minimum, so that example does not refute universal minimum soundness.
- One dirty ancestor boundary: in TopForm the only possible AND ancestor i of an unowned gate j is dirty; if both j operands reach i by OR-only paths, the minimum proof agent's dominance lemma applies. Remaining form j=(i OR S) AND T with i=A AND B. If T implies A, direct j=i AND T rewrites to B AND T; minimum_proof is implementing that direct-filter exchange. Mixed OR side requires accounting for other readers of OR(i,S).

### 2026-11-25T03:46:29.493468+00:00 — search archive ready

Packaged encoder, command documentation, representative exact CNFs, full solver logs, model JSONs and checksums under `results/orch/search/` (about1.5MB). No solver binary, installation files, desk metadata or credentials are included. C5 minimum7 admits no unowned AND in the normalized SAT model; C5 minimum7 also admits no unsound AND. C7 size9 is UNSAT with canonical-first graph symmetry (20.9s); C7 size10 unowned remains UNKNOWN after120s without this symmetry. Petersen19 is UNKNOWN after300s SAT and180s MILP. Solver timeouts are not lower bounds.

### 2026-11-25 03:47 UTC — normal_form: MixedFilter compiled

`MixedFilter.lean` (280 lines) compiles with exit 0. It proves the conditional absorption rewrite j=((A AND B) OR S) AND T to j=(B OR S) AND T when T implies A and the mixed OR has only reader j and is not the output. Monotone2, gate count, output, and all wires except that mixed OR are preserved. Full log: `/tmp/oec/pequalnp-pilot-66/mixed-filter-build.log`. This is a semantic component only; the target does not yet imply the dominance or unique-reader conditions. Conditional-helper expansion stops here. LocalNormalForm is logical packaging, not progress on the missing global bridge. Next analysis concerns arbitrary multiple dirty ancestors and a global cost repair.

## General five-vertex ownership census — 2026-11-25T03:49:06.802993+00:00

`alg-general5.py` in job scratch generated all 34 graph isomorphism classes on five vertices: 33 nonempty graphs had SAT witnesses, and the empty graph was handled directly. Every first satisfiable model had every AND owning an edge, and every model passed independent full truth-table and ownership validation. For 32 nonempty graphs all smaller sizes in the tested normalized binary range were UNSAT; sizes below the elementary input-count bound were not sent to SAT. K5 reached an all-owned size-10 witness, but a smaller-size test timed out, so its optimum is not established by this run. These are computational results, not Lean lower-bound proofs. Full data: `alg-general5-results.json`, `alg-general5-progress.log`, and individual `alg5_*.runlog`/`sat-alg5_*.json` files in scratch. Total71.4seconds.

A conceptual restriction on amplifying the matching-two dirty gadget: attach one clean star center to each reused OR support S. Girth five forces each support independent in the base graph H and pairwise intersections at most one. If a pure CNF over those supports computes H, its necessary clauses are all minimal vertex covers. All such covers independent forces H to be a disjoint union of complete bipartite components; C4-freeness makes these stars. The support-intersection condition then permits only a single star or two isolated matching edges as the nontrivial fully reused CNF cases. This is a mathematical argument not yet formalized, and does not cover mixed AND/OR cyclic sharing.

## Direct-filter repair checked — 2026-11-25T03:49:22.714418+00:00

`DirectFilterExchange.lean` compiles (exit 0). The final lemma `direct_filter_exchange` handles j=i AND T, i=A AND B, with sole possible strict-cone AND ancestor i and T globally implying A. Replacing j by B AND T preserves every wire value, gate count, minimality, and every existing ownership witness; j now owns a graph edge. Generic infrastructure proves cone inclusion from inclusion of direct-reader dependencies and transports ownership under equal values/operations. The file is frozen for root review. Full log: `/tmp/oec/pequalnp-pilot-66/direct-filter-exchange-build.log`.

Global obstruction remains: first-unowned selection does not bound the number of AND ancestors and does not give T⇒A or T⇒B. Multiple independent dirty ancestors can all fire on one graph edge without creating graph triangles or C4. Example ((a OR b) AND (c OR d)) AND ((a OR c) AND (b OR d)) computes the matching ad OR bc, uses 7 gates versus 3 directly, and final AND owns no edge. Thus minimality/global sharing cost, not a graph-only contradiction, must eliminate such patterns.

### 2026-11-25 03:56 UTC — normal_form: global repair reformulation

No full repair obtained. A concrete noncircular decomposition is available: cut an earliest dirty AND i to false and prune constants/dead gates, obtaining C0 whose function is pointwise below F. Define H to consist exactly of graph edges e with C0(e)=false. Then F = C0 OR graphFun(H), because every positive input contains an edge, and C0 is monotone. Thus an exact repair reduces to a budget certificate for an edge patch of H using surviving linear wires, charged against the removed gates and newly unused OR factories. The patch may be sound and all-owned; however, proving its budget for arbitrary mixed AND/OR consumers is still the hard global theorem, and taking a full star patch could be stronger than the target. First-unowned selection does not give a sole AND ancestor or a dominant operand.

Primary-source caution, read 2026-11-25: Jukna, ECCC 2005 report 021, https://eccc.weizmann.ac.il/report/2005/021/download/ pp.15–16, explicitly discusses K2,2-free bipartite graph formula lower bounds and then asks in Problem 24 for an explicit quadratic graph function with a superlinear monotone circuit lower bound. A universal |E|+tau-1 circuit lower bound would therefore be a substantial theorem, not routine accounting. Current status of that historical open problem is UNVERIFIED; no current primary-source resolution found in this search.

### 2026-11-25T03:54:54.391153+00:00 — checked stress witness and frozen search batch2

`StressGraph.lean` (69lines) now kernel-checks the eight-vertex ten-edge subdivided-K4 graph: triangle-free, NoFourCycle, explicit13-gate Monotone2 implementation with every AND owning an edge. No minimality claim. Full log scratch/stress-graph-lean.log; exit0, two letI style warnings. SHA256a6c1b472d8ebcc3616c4e384099b604d8ab71034d980228e89401aa3e3756058. Old Counterexample.lean restored byte-for-byte from HEAD.

Stressgraph12 unconstrained,13 unowned,13 all-owned and optional-pruned12 searches all timed out UNKNOWN. At the C6 8-gate upper bound, forced-unowned is UNSAT in the normalized model; all37 nonempty labelled n4forests at BFS minima are forced-unowned UNSAT. At the C7 10-gate upper bound, forced-unowned remains UNKNOWN. `results/orch/search2/` combines these full logs/formulas with algebraic_route's all34 general n5graph census; 33 nonempty SAT witnesses were all-owned;32 had all smaller tested sizes UNSAT, the empty graph was handled directly, and the K5 lower bound remains unresolved. Batch2 now frozen for review/push.

2026-11-25T03:58:25.513032+00:00 minimal_proof: SingletonEdge.lean compiles. Generic globally decreasing gate replacement + equality on every graph-edge input preserves the whole graph function; graph ownership survives cone restriction. Arbitrary ancestors. Singleton repair + bad-count drop being specialized in new file.

2026-11-25T04:00:29.898431+00:00 minimal_proof: SingletonEdgeRepair.lean compiles (exit0): any unowned AND with exactly one accepted undirected graph edge is replaced by direct input AND. Arbitrary ancestors, no girth assumptions. Same size/minimum/function; preserves old graph owners; Set.ncard of bad ANDs strictly falls. Generic badAndGates_strict_drop available. Frozen for review/push. Full log singleton-edge-repair-build.log.

### 2026-11-25 04:03 UTC — normal_form: star repair compiled

`StarSemantics.lean` proves that the clean star projection of any monotone wire lies below that wire and agrees on all graph edges when its accepted-edge pattern is a star. `StarWire.lean` combines this with the arbitrary-DAG replacement bridge: if an earlier AND-free wire computes the exact OR of the star leaves, one AND replacement preserves minimum size, output function, and all old graph-edge ownership, and the changed gate owns every accepted graph edge. The reusable OR wire need not lie in the old cone; only AND-ancestor inclusion is used. Both files compile (StarSemantics log empty, StarWire inherited warnings only). Logs: `star-semantics-build.log`, `star-wire-build.log` in job scratch.

Next general bridge: decreasing a single AND h preserves all old ownership at gates k different from h, provided no new AND ancestors are introduced. Any positive-edge activation lost at k would force old h=true and h in its strict cone, contradicting ownership. This avoids global edge-equality requirements for transporting ownership during captured-edge residual rewrites.

### 2026-11-25T04:08:39.522172+00:00 — interrupted long searches

The environment/tool refresh around04:02 stopped all three long-search processes. On04:08 inspection neither wrappers nor CaDiCaL remained. Full original logs and formulas persist; logs end mid-search without SAT/UNSAT verdict. These runs are INTERRUPTED/UNKNOWN, not completed timed-out lower-bound tests. Interruption metadata and hashes saved in scratch/long-search-interruption.json. Restarts will use fresh names.

2026-11-25T04:08:41.762581+00:00 minimal_proof: ReplacementLocality.lean compiles. Changing gate j never affects gate k outside the OLD cone of j (k≠j). No assumptions on replacement gate. normal_form composing owner transport. Building MinimalBadNormalForm via singleton repair and Nat.find.

2026-11-25T04:09:24.583885+00:00 minimal_proof: MinimalBadNormalForm.lean compiled, exit0. From any minimal graph circuit, produces same-size minimal graph circuit in which every unowned AND accepts at least two distinct unordered graph edges (Sym2 inequality). Nat.find minimizes bad-AND ncard, singleton repair excludes singleton profiles, pivotal lemma excludes empty profiles. No girth hypotheses. Frozen for review.

### 2026-11-25 04:08 UTC — normal_form: downward ownership transport compiled

`DownwardOwnership.lean` compiles with exit 0. `downward_and_preserves_other_owners` proves that replacing one AND gate h by any monotone gate that is pointwise below the old value preserves every old ownership witness at every k different from h, provided no new AND ancestors are introduced. It does not require agreement on graph edges and applies to arbitrary input pairs. `downward_primary_preserves_other_owners` discharges the cone condition when all replacement inputs are primary, including a singleton-edge AND and the empty OR=false residual. The locality lemma was supplied by minimal_proof. Full log `/tmp/oec/pequalnp-pilot-66/downward-ownership-build.log`; inherited warnings only. This is useful for captured-edge rewrites because only the changed gate itself can lose old ownership.

2026-11-25T04:12:55.572953+00:00 minimal_proof: NormalizedExistence.lean compiled exit0; Defs-only self-contained adaptation of L-meta-5355 star construction seeds minimal existence. Final exists_minimal_bad_normal_form has NO seed hypothesis: every finite graph has a minimum circuit where every unowned AND accepts at least two distinct unordered graph edges. No girth assumptions. Frozen; log normalized-existence-build.log.

## Global clean-class replacement checked — 2026-11-25T04:16:21.420862+00:00

`ClassIteration.lean`, `ClassCover.lean`, `ClassPrefix.lean`, and the combined `CleanClassReplacement.lean` all compile. The final theorem `clean_class_replacement` prepends an arbitrary monotone circuit D with no dirty ANDs, whose output is false on every G-negative input and covers every accepted G-edge of each gate in a finite class S. It then deletes/reroutes all S gates, preserving arbitrary external readers and forward/missing-wire semantics. If D.size <= |S|, final size does not increase. Dirty-AND count cannot increase and strictly drops if S contains a dirty AND. Unlike the earlier class theorem, no equality of edge labels or global pointwise domination is needed. All sources are frozen for root review. Final log `clean-class-build-002.log`: exit0, one harmless unnecessarySimpa warning. The remaining combinatorial gap is finding such a budgeted class for every circuit with a dirty AND under no C3/C4.

### Counterexample search update 2026-11-25T04:20:58.589222+00:00
- Restarted Petersen19, 120-automorphism depth3 prefix search completed 600 seconds UNKNOWN (CaDiCaL return0). No lower bound or witness. Exact formula/full logs in scratch `sat-petersen19restart-19-sym.*`. Stress12 unrestricted and optional-pruned 1200s runs continue.
- Experimental `circuit-sat-shared.py` extends the frozen encoder with structural shared-OR certificates, a selected unowned AND accepting two disjoint edges, and edge-pivotality for every gate (forcing that gate false loses some graph edge). These are diagnostics, not a certified complete minimum-circuit model. Models independently recompute all inputs, cones, ownership, and pivotal witnesses.
- C5 size9 SAT3.51s: n5 gates AND01, OR03, OR13, OR[1,6], AND[4,6], AND[2,8], OR[5,10], AND[7,11], OR[9,12]. Gate7 is unowned and accepts path edges01,12,23; AND ancestors0 and5 cover complementary edge labels. OR03 is shared with independent star4. Every gate pivotal; all ANDs singleton-safe. Nonminimal: repair9→7 by changing AND5 operand wire8=OR013 to existing wire7=OR13, deleting OR3 and final filter7. Shared OR03 survives.
- C6 size10 SAT25.27s: n6 gates OR02, OR03, OR25, OR35, AND[1,6], AND[6,7], AND[8,11], OR[4,12], AND[9,13], OR[10,14]. Gate6 unowned and accepts matching05,23; OR02 shared with independent star1, OR35 also used downstream for star4. Every gate pivotal; AND5 fires singleton0. Nonminimal versus known8. These useful sharing diagnostics do not refute L-meta-1772.

### 2026-11-25 04:22 UTC — normal_form: factory-budget analysis

For a globally sound pure three-clause block OR_A AND OR_B AND OR_T, the triple intersection is empty. Nonempty pairwise-only classes AB, AT, BT would give a triangle, so one pair of clause supports is disjoint. The accepted-pair graph is therefore a blowup of P4; no C4 makes it a double-star or a single star. In the proper double-star case, two singleton overlap centers x,y give the projection (x AND OR_T) OR (y AND OR_B), reusing two original clause OR wires. It costs one gate more than the two old filter ANDs, so freeing one gate from the third OR factory pays. That third factor contains the adjacent centers x,y, precluding fresh sound literal-star reuse, but arbitrary dirty owning readers remain an unresolved global issue. In the single-star case where center u occurs in only one factor and at least two leaves survive, that factor must be {u}; exposing the intersection of the other two shared OR supports is the remaining issue. These deductions are mathematical analysis, not yet Lean-checked.

Shared nonminimal SAT diagnostics supplied by counterexample clarify the goal: a C5 size-9 block is repaired by normalizing an already-owning star ancestor through StarWire, then deleting a redundant filter. Thus truth-table minimization among minimum circuits may be useful in addition to minimizing bad AND count. A C6 size-10 example can be repaired to size9 while retaining both shared OR factories: two private clause ORs and two filter ANDs cost4 versus3 for the matching-two projection. Reaching the known 8-gate upper bound is unnecessary to contradict hypothetical minimum10. With all four matching clause sums shared, three filter ANDs still have the same cost as two primary ANDs plus one OR. External readers of intermediate ANDs, rather than clause-factor sharing alone, are then the obstacle.


### 2026-11-25T04:22:55.886292+00:00 — sound_and: concrete captured double-star repair checked

`DoubleStarRepair.lean` compiles, exit 0; 1584 lines; SHA256 `5fc8b746c4cef079d8a4fab43e8b74b21bb0096201dd87bf6828e8f593bccf53`. Full log: `/tmp/oec/pequalnp-pilot-66/double-star-repair-build.log`. Frozen for review/push. The final `double_star_repair` assumes a minimal circuit computing G, NoFourCycle, earlier AND h with function OR_A AND (b OR d), later gate j literally h AND b, an existing AND-free wire before h computing OR_A, all A adjacent b, and an OR-only path from j to output. It first rewires j to OR_A AND b, then replaces h by the empty OR, literal d, or a primary residual edge AND. It proves exact graph-function preservation, unchanged size/minimality, preservation of every old owner except h, ownership at j of every b–A edge, and that the new h is either OR or owns an edge. This is a concrete two-edit DAG transformation, allowing arbitrary external consumers of h. It does not extract that local template from an arbitrary first unowned AND.

For the remaining three-factor sound-star classification: if the accepted-edge star has at least two leaves and its center u belongs to only one factor, NoFourCycle forces that entire factor to equal {u}. The hard case is therefore u AND OR_A AND OR_T, selecting A intersection T. Reassociation only moves an unowned gate; a global OR-factory sharing budget remains needed. Soundness forces all cross pairs between non-neighbor extras of A and T to be adjacent, restricting either side to a singleton when the other has two leaves of another star.

### 2026-11-25 04:24:31 UTC — normal_form: independent heuristic review

Reviewed scratch `rewire_search.py` at SHA256 `3b70efc5488197512f390237c79e6d0b503818ff773a721aea3f8a5b123a6290`. Legal earlier-input binary monotone mutations, contraction remapping, and last-gate output check out for the Petersen run. Independently enumerated all1024 inputs and confirmed the encoding tests are exactly15 edges plus15 maximal independent sets. The then-best candidate has1 tested mismatch and9 full truth-table mismatches, so is not a witness. Finite heuristic failure remains UNKNOWN, never a lower bound. A zero-score result is fully evaluated before exact-truth-table status, but is still not a Lean proof or automatic target refutation. Minor search-quality issue: a new best accepted on the final inner-loop mutation is not examined before restart and can be missed; no false-positive risk. Root notified.
