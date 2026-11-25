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
