# L-meta-2592 orchestration notes

Assigned 2026-11-25T13:59:48 UTC. Petersen graph 19-gate lower bound in presence of at least one NOT. Only root holds lease and calls desk. Three live reductions already exist.

Strategies are tracked in TIMELINE.md. Agents append findings to their own results/orch/ files; root consolidates here.

## 14:03 UTC re-plan
- Existing L_meta_4725 proves ≥15 binary gates for Petersen, yielding the >=5 NOT exclusion. Semantic agent has prepared a 3254-line standalone partial.
- Remaining hard cases: 1–4 NOT gates under total19. Few-NOT agent investigates eliminating a single NOT. Combinatorial agent investigates restrictions/branch bounds; counterexample agent sets up exact SAT with cadical.
- Toolchain was missing despite setup brief; official Lean4.36 downloaded to scratch, Mathlib cache fetching. Disk is constrained.
- L-meta-1035: no matching exact file or open PR found; public status still being resolved. We are working only assigned L-meta-2592.

## Stronger binary floor route
- L_meta_5236 has a checked >=16 binary-gate floor after a free extra OR input. Generic embedding now compiled, allowing application to ordinary circuits.
- PairSeparation noPairFactor is compiled; semantic/few-NOT agents aim to use it with two-gate elimination and the9-input floor15 to obtain >=17 binary gates.
