# pilot-84: L-meta-9502

Sole lease held by root. Assigned 2026-11-25 11:22:02 UTC after eight nulls.
Exact desk data and statement: /tmp/oec/pequalnp-pilot-84/desk-response-9.json and statement.txt.
Target: no <=71 gate AND/OR representation of CYCLE_11 (33x33); a checked counterexample also counts.
Final file: lean/PEqualNP/Outside/L_meta_9502.lean.
Imports allowed: PEqualNP.Defs, Mathlib modules. All helpers own namespace, final fully named theorem last.
Setup agent owns cache: wait for its ready signal before any lake build; no Mathlib source builds.
Use /tmp/oec/pequalnp-pilot-84/lean-env.sh. Full checker cache currently constrained by disk.

Strategies: status_audit lower bound; circuit_search computational witness; representation_strategy hand decomposition; root integration/Lean encoding.

Append findings with UTC timestamps below.

[2026-11-25T11:24:14.340602+00:00] status_audit
## Lower-bound audit
- Existing RepReads.reads_le proves forced input count ≤ size + 1. This graph forces all 66 inputs, yielding size ≥ 65.
- RepPath.path strengthens by one gate when an induced four-vertex path occurs, yielding size ≥ 66 here.
- RepInduced.induced preserves excess of induced subgraphs relative to forced inputs; no available result yet forces the required excess 6.
- The undirected graph is a cyclic chain of 11 bicliques {A_i,B_i} × {A_(i+1),C_i}, sharing A vertices. Straight merge of left/right vertex wires costs 33 + 22 + 11 + 10 = 76 gates.
- Existing exhaustive lower-bound files (e.g. L_meta_6381, L_meta_8299) use finite live-wire search; direct use at 71 gates appears infeasible.

- 2026-11-25T11:25:48.362515+00:00 certificate: Positive witness pattern found in L_meta_9103/9099: raw Circuit lists, Monotone2 via simp, Represents by decide +kernel. Generated independent76gate baseline (33 side-pair ORs, 11 K22 terms, OR aggregation), checked all1089inputs in Python; Lean compile pending rootbeat. Scratch certificate/Baseline76.lean and baseline76.json.
- 2026-11-25T11:25:48.362515+00:00 submission: outside-guard checkGap uses posted row kind; authoritative rejects arbitrary refute on check rows.9502 negative statement currently check; its positive twin9501 is separate. Root informed; preserve refutation results if found before resolving delivery.
