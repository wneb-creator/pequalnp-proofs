# pequalnp-pilot-62 orchestration notes

Held step: L-meta-1896. Only the parent manages its lease and submits.
Assigned 2026-11-25T03:05:06Z. Renewed 03:05:31Z, expires 03:25:31Z; renew every 10 minutes and before long work.
Exact desk response and statement: /tmp/oec/pequalnp-pilot-62/desk-answer-006.json and statement.txt.
Target: lean/PEqualNP/Outside/L_meta_1896.lean. Allowed project dependency: PEqualNP.Defs.
Goal: every monotone fan-in-two circuit true at incident point-line pairs and false at generic maximal false inputs has at least 51 OR gates.
Reductions are advertised open, but reductions_live=3; do not assume another reduction slot is available.

Build environment: source /tmp/oec/pequalnp-pilot-62/lean-env.sh.
Use minimal Mathlib dependencies; full Mathlib cache is absent. PEqualNP.Defs and checklemma built successfully.
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
