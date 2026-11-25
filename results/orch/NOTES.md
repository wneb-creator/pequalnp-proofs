# L-meta-2592 orchestration notes

Assigned Petersen graph: FanInTwo circuits of at most 19 gates containing NOT cannot compute edge function. Only PEqualNP.Defs project imports allowed. reductions_open true, reductions_live 3. Root owns lease and Git operations.

Each agent appends findings to its own notes file under results/orch/; root integrates here. Lemma candidates under results/orch/lemmas/. No agent modifies main target without coordination.

## Status 2026-11-25T13:50:20.094246+00:00
All three reduction slots are filled. Existing preliminary normalization, last-NOT decomposition, and binary-gate floor15 are checked; unresolved bound is 1–4 NOT gates. Stochastic and exact-synthesis searches running. Toolchain initially absent, installed pinned Lean4.36 under scratch; Mathlib cache preparation in progress.
