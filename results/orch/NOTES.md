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

## 2026-11-25T14:21:04.322109+00:00 re-plan
- Preserve all compiled components immediately; four partial commits have been pushed. No full theorem/PR claimed.
- Completed and compiled: CutLast, EmbedExtra, PairSeparation/cofactor/automorphisms, signed restriction machinery, plain product-based signed variant, FewNots boundary witnesses, first-gate two-reader/false-two-deletion lemma.
- ReachBridge now compiles against exact generic Reach interface; combine with nineFloor15 and first-gate deletion to obtain17binary floor. BinarySixteen certificate still running, independently audited.
- Stronger conditional deletions: opposite-phase second reader saves3binary underfalse; same-phasefalse saves4. These imply18/19binary after nineFloor15. Remaining first-OR/same-negative-phase case is difficult.
- Tooling/combinatorial agents exploring finite Live-state certificates forbudget17; constant restriction and rowseparation reduce firststep to45ORstates (two graphorbits). Generic duplicate-charge pruning is false (mux counterexample), so discarded.
- Existing L4033 proves9vertex totalgatefloor16; it is near512KiB and does not directly strengthen signedbinaryfloor15.
- SAT searches have no witness or UNSAT result; focus compact signed17/18 searches. Extra processes paused/stopped to keep CPU available.
- Three live reductions already fill the desk limit; no fourth reduction can be submitted. Continue toward fullproof/refutation with onelease.
