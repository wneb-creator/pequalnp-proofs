# L-meta-1479 orchestration notes

Lease acquired: 2026-11-25T09:33:51Z. Root owns the only lease for this job.
Goal: at most 27 binary AND/OR gates computing Fano incidence on 14 inputs, with one incidence whose two first derivatives specified by the desk are both false.
Exact statement and assignment: /tmp/oec/pequalnp-pilot-81/statement.txt and desk-assigned.json.
Lean: /tmp/oec/pequalnp-pilot-81/lean-4.36.0-linux/bin. All Mathlib cache, checker, and Defs builds ready.
Main proof file is root-owned: lean/PEqualNP/Outside/L_meta_1479.lean.
Each agent writes findings in its own file under results/orch/lemmas and messages root. Read peers' notes before long searches. Do not modify other agents' files or the final proof.
All helpers in final file must be in PEqualNP.Outside.L_meta_1479 or its _aux namespace; theorem fully qualified and last. No forbidden syntax, quotes, axioms, admissions, native_decide, or bv_decide.
No agent besides root may call desk, commit, push, or open PRs.

Current: baseline star circuit costs 27; finding a double re-read within that budget is the hard condition. Desk says reductions open but already 3 live reductions; inspect them to avoid duplication.

2026-11-25T09:40Z: first named partial built and pushed as 851aefe8ca50f17a2a81da1ba78fc5bb06fd8fda (helpers only). All routes found 28-gate factorized baseline; one gate must be saved. Stochastic uses 21 positive plus 37 maximal-negative rows, singleton bases and derivative bits. Cadical is in Lean toolchain bin. SAT found two-star7-gate local double-re-read impossible (computational only). Structural top-AND supports disjoint and cross pairs incident; nonempty supports must be a1-by-k star, k1..3.
