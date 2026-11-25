# Definition audit: L-meta-2592

2026-11-25 UTC. No immediate statement/definition defect found.

- `Circuit.size` counts every gate, including NOT, constants, copies, unused gates, and repeated gates.
- `FanInTwo` explicitly limits gate operations to AND, OR, NOT and input-list length to at most two.
- Evaluation uses an append-only fold. A forward or invalid wire reads false at that gate; it does not introduce feedback or read the eventual wire value.
- NOT negates the first input; the second is ignored. Empty NOT and NOT of an invalid wire are true. Constants therefore cost a gate except false, which can be obtained by an invalid output/input index.
- The output is a fixed natural number. Input length is always exactly ten. It cannot encode an input-dependent index.
- The target is an ordinary OR of the fifteen stated pairwise ANDs. All ten variables are essential. Zero input is false, all-ones input is true, every singleton input is false.
- Consequently a computing output must be a gate wire: a missing output would be identically false; an input output would be true on its singleton.
- The NOT hypothesis means at least one NOT anywhere, with no upper bound on their count. A proof for exactly one NOT does not finish this step.

Useful finite normalization: in gate j, indices at least 10+j can all be replaced by 10+j (false); every NOT can have its ignored second input removed. This makes bounded-size synthesis finite, but the resulting search space is enormous.

No counterexample found by this audit.

## Checked partial

2026-11-25T14:10:30.640604+00:00 — `lake env lean /tmp/oec/pequalnp-pilot-109/audit/Audit.lean` exited 0 with empty stdout/stderr. 94 lines.

The checked file proves exact target zero/one/singleton values, explicit sensitivity of all ten input variables, monotonicity, generic wire length and preservation of input values, and `10 ≤ C.output < 10 + C.size` for every circuit computing the target. This is a partial result, not the posted 19-gate lower bound.

## Global construction search

- KG(5,2) mapping: x0=12, x1=34, x2=15, x3=23, x4=45, x5=35, x6=25, x7=24, x8=14, x9=13.
- Direct star/triangle and shared-cofactor formulas have not improved the 20-gate construction.
- Building official ABC optimizer from https://github.com/berkeley-abc/abc (page read 2026-11-25) in audit scratch, two compile jobs. Full build logs retained.
- Implemented exact Z3 phase minimization for AIG nodes: choose AND versus OR storage phase; count one NOT per source requiring opposite-phase uses. Independent 1024-input evaluator validates every resulting circuit. Sanity check on direct 29-gate DNF returns 29 binary gates, zero NOTs, zero errors.
- Started smaller 6-input/5-output synthesis: four triangle ORs T1..T4 and a partial output q with T4 AND q equal to the three-disjoint-pair matching function. An 11-gate shared implementation (including NOTs) yields a 19-gate Petersen circuit by factoring final T4 aggregation.

- K4-family synthesis at 11 gates / one NOT: both 180-second SMT and 300-second pure SAT runs ended `unknown` (timeouts), not UNSAT. Two-NOT case now running. Small-family annealing still has best four residual truth-table errors; no witness.

- 2026-11-25T14:31:30Z: root requested resource prioritization on this 4-core machine. Stopped the active two-NOT family SAT and pool annealer with SIGTERM; both exited 143. Their interrupted runs establish no SAT/UNSAT result. Full logs and `termination-status.txt` preserved. Only ABC `make -j2` remains active for this agent.

- ABC build completed, 1548 translation units, exit0 and empty stderr. Standard rewriting examined at least1140 fully validated candidates, with best20 binary gates and zero NOTs; manually stopped to change strategy. eSLIM2 runs at 180seconds each (cuts up to10, then growth toward20 with larger SAT budgets) both retained20 gates. The latter attempted cuts only through11 gates and did not finish its reduction queries. These experiments prove no lower bound.
- Global optimizer work paused to free the CPU for the formula certificate. Audit now investigates the no-internal-sharing circuit-to-DeMorgan-formula bridge.
