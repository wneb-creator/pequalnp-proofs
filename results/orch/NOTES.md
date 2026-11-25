# pequalnp-pilot-62 orchestration notes

Held step: L-meta-1896. Only the parent manages its lease and submits.
Assigned 2026-11-25T03:05:06Z. Renewed 03:05:31Z, expires 03:25:31Z; renew every 10 minutes and before long work.
Exact desk response and statement: /tmp/oec/pequalnp-pilot-62/desk-answer-006.json and statement.txt.
Target: lean/PEqualNP/Outside/L_meta_1896.lean. Allowed project dependency: PEqualNP.Defs.
Goal: every monotone fan-in-two circuit true at incident point-line pairs and false at generic maximal false inputs has at least 51 OR gates.
Reductions are advertised open, but reductions_live=3; do not assume another reduction slot is available.

Build environment: source /tmp/oec/pequalnp-pilot-62/lean-env.sh.
Use minimal Mathlib dependencies. PEqualNP.Defs and checklemma built successfully; the genuine official root Mathlib cache artifact was unpacked at04:25 UTC. The actual statement checker now builds successfully but faults while importing the full Mathlib statement environment because Batteries.olean is missing; full dependency cache storage is insufficient by the recorded estimates.
Keep full diagnostics in task scratch. Never build Mathlib from source or run lake update.

Agents write separate strategy notes under results/orch and read this shared file. Parent alone updates this file and final target.
Any compiled helper must be reported promptly for independent audit and an early push.
No routes/ directory is published in this clone; sketch references may be unavailable.

## Compiled components
- Geometry: finite coverage of every nonedge pair by generic negative supports.
- OrSignature: OR trace length and preservation under equal trace signatures.
- Routes: generalized merge-count lemma from L_meta_5158, accounting for singleton flips above a false baseline.
The named file currently contains helper proofs only; the posted 51-OR theorem remains unproved.

## Replan 2026-11-25T03:26:42.713482+00:00
- Checked result: exact posted premises imply18 OR gates. Immutable source/log are in checked/routes-eighteen-exact.*; target51 remains unproved.
- Dead route: uniform cross-row merge bounds. A49-edge arbitrary-pair OR graph connects all19zero inputs in everygeneric row; it is not itself a counterexample circuit.
- Dead route: universal C4-free quadratic-shadow |E|-1 theorem. Grandchild found an asymptotic dual-rail affine-plane obstruction; precise notes pending. This does not refute the held13-plane step.
- Active: all-OR-gates-reject-every-negative case should need51OR by input-monomial/DAG extraction. Combining with saturated18merge count may improve18to19. or_lower_bound and proof_routes coordinate.
- Active: canonical free-AND SAT and beam search on theta and quadrangle subcircuits, including reuse of an opposite-line OR outside the subcircuit. No counterexample found.
- Resource limit:2CPU,8GiBRAM. Large8192-subset Lean cap certificate exited137 and is not a checked result; smaller proofs remain sound.
- Cumulative sub-agents:7 (including proof_routes/quadratic_shadow).

## Replan 2026-11-25T04:04Z
- Exact posted assumptions now imply at least 20 OR gates in Lean; target 51 remains open. The named file equals checked/Twenty.lean and its lake build passed (5149 jobs).
- The actual local checker stopped at missing full Mathlib cache (exit 3); no checker acceptance or proof PR is claimed.
- WeightedSurvivors compiled: surviving flags minus one plus first-introduction block count is a lower bound for the OR count. This strengthens deletion accounting.
- Preferred next proof route: all 468 generic rows touch a singleton 126 times and a pair at least 204 times. Under at most 20 OR gates each row meets at most two introduction blocks. Double counting should bound the deleted-coordinate union by eight; weighted survivors then contradict at most 20.
- lean_setup owns finite touch-count certificates; proof_routes owns generic double counting; or_lower_bound owns the final circuit wrapper. The finite DFS route is parked in favor of averaging.
- Small theta search concluded UNSAT for seven OR gates in its SAT model; it is not a Lean proof or a resolution of this gap. A full 13-output, 38-OR query started at 04:03 UTC after successful 39-OR controls; candidates must pass all original rows.
- Dead general approaches remain dead: uniform per-row merge bounds and unrestricted quadratic-shadow C4-free bounds.
- repo_audit independently approved the named 20-OR partial and is reviewing newer snapshots. algebraic_witness is reviewing the SAT encoding.
- Cumulative sub-agents: 7, including proof_routes/quadratic_shadow. Only the parent renews, pushes, submits and releases.

## Replan 2026-11-25T04:27:19.898147+00:00
- Posted51 target remains open. The named file still contains the checked20 bound. The combined exact-premise21 proof reached only a default heartbeat limit in its final wrapper; a declaration-local limit increase is rebuilding, with no finite certificate failures.
- AllRows is fully checked:468 distinct admissible rows,7 true/19 false coordinates each, singleton count126, pair-union count at least204. Its immutable source and complete log have been pushed.
- The checker startup cache issue is repaired with the genuine official Mathlib root cache artifact and standard cache unpack. No checker source changed. A fresh checker run remains pending.
- Capacity3 computation: maximum removed flags minus block count is28. Exhaustive search visited56,424,915 families. Four explicit symmetries reduce a proof of the weaker bound29 to31 roots totaling78,682 states. All of this is computational evidence, not yet a full Lean theorem.
- One capacity3 root is kernel checked (root21,811 search states). Generic pruned DFS soundness and concrete mask/prune semantics also compile.
- Next proof ownership: lean_setup has literal data, finite action/orbit certificates, and31 root computations; proof_routes has concrete trace/mask semantics and fresh-block normalization; existing child quadratic_shadow has generic DFS/row-mask invariants; or_lower_bound has permutation/word transport and final22 assembly after21 is preserved.
- Counterexample route: both3-output models are UNSAT at8 ORs; a4-cap-output11-OR query is running. A direct full38-OR encoding now fits memory (about2.06M clauses), with validated39-OR control; full search is queued. A restricted pure-union38 model is also prepared. No counterexample exists in the checked artifacts.
- Dead shortcuts remain dead: unrestricted quadratic-shadow bounds, uniform cross-row merge charge, and a uniform54-per-gate pure-union deficit charge (an explicit join improves that deficit by60). Amortized variants remain unproved.
- All published computational archives are labelled accordingly and independently reviewed. No PR has been opened; three reduction slots were already occupied.
- Cumulative sub-agents remain7; reactivated existing child, no new team member. Parent alone manages lease, branch, checker and submission.

## Replan 2026-11-25T05:10Z
- The exact-premise21-OR lower bound compiled successfully in run005 (4133 lines). Its full log contains warnings only; the named-file build and posted-statement checker will follow preservation. The target51 remains unproved, and no counterexample has been found.
- Environment interruption around04:42 killed the old Lean/SAT workers; interrupted queries have no verdict. The lease survived and is renewed by the root every10minutes and before long runs.
- Capacity3 verification is paused. Computational capacity4 families can partition all13 points into7 blocks and delete all52 flags, so this deletion route cannot reach51. Only individual checked chunks/helpers are labelled checked.
- Main counterexample effort now uses the unrestricted canonical free-AND global50-OR model, all52 flag positives and468 original generic negatives. Optional dirty-OR and late-prefix cuts were independently reviewed. Its51-OR control passed SAT and all546 sampled-input checks.
- The51-OR baseline is not a counterexample. Lean compiler structure, exact OR count, Boolean semantics, bitmask semantics, literal-mask certificates and sample bridge have compiled. Finite sample-bit checks and completeness of the468 generic rows are being prepared so a real50-OR witness can be certified without delay.
- Resource schedule: one large Lean job plus at most one capped SAT solver. Smaller Lean helpers run serially with a7.3GiB actual-memory guard. No large capacity3 enumeration batches are scheduled.
- Active assignments: counterexample global50 search; proof_routes and existing child canonical compiler/certificates; lean_setup finite geometry completeness; or_lower_bound checked21 integration; repo_audit independent reviews. algebraic_witness is currently idle; the active7-slot ceiling prevented reactivation, and no new agent was created.
- Cumulative sub-agents:7. No PR has been opened. All3 reduction slots were already occupied at last feed check.

## Replan 2026-11-25T05:30Z
- The named21-OR partial built successfully (5149 jobs,331.17 seconds); exact source SHA6c46fc133ba473daf3a9cb88dd2f9b3760e95883375e281be4b091c8ffec3aa3 is pushed. Its axioms are only propext, Classical.choice and Quot.sound. Target51 remains unproved.
- The actual checker built its verifier and judged modules, then returned FAULT/exit3 at missingBatteries.olean. It always imports the fullMathlib statement environment. The disk report records6516 missing imported modules and642MB free at assessment time;3.04–4.97GB further artifacts is an estimate. No checker source, library proof or configuration was altered; no full fetch or Mathlib source build will be attempted in this storage limit.
- All13520 fixed sample input bits are now kernel checked (52 positive flags and468 generic rows,26 coordinates). The51-OR baseline's literal mask certificate also compiled; it is a control, not a counterexample.
- All8192 possible point subsets have now been classified in64 kernel-checked chunks. Eight cached groups and the aggregate prove every admissible subset appears among the468 rows. The row-input agreement bridge is finishing. The exact posted-negation wrapper is independently reviewed and will be compiled next as a conditional helper; no50-OR witness exists.
- Fullglobal50 search was previously resource-stopped after76.08seconds/SIGINT, UNKNOWN. Its exact compressed input and complete logs are pushed. After the final small wrapper check, pause allLean jobs and run the genuine global50 model for900seconds with a shared-memory watchdog. If memory permits, use the secondCPU for the smaller canonical13-output38 model that allowsAND insideOR operands; it previously lost its worker to environment interruption, with no verdict.
- Independent mathematics now supports a39-OR lower bound for the restricted pure-union internalDAG/freeAND output architecture. Private/shared guard charging and exact-pencil ancestry have been audited computationally, but this is not yet Lean-certified and does not cover arbitraryAND insideORs. Deprioritize pure-union38 searches. or_lower_bound will prepare this restricted formalization while solvers run.
- Topology computations and other dead-route evidence are preserved with explicit scope. No valid full51 circuit potential has emerged. Existing capacity4 deletion obstruction still prevents that weak route from reaching51.
- Sub-agents used cumulatively remain7. Only root manages the lease, pushes, checker and submission. No PR has been opened; no reduction slot was available at the last check.
