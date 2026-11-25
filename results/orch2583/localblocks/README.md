# Local Fano point-star block searches

Stopped at parent request after L-meta-2583 lease became unavailable. No jobs remain running.
Stopped UTC: 2026-11-25T15:07:34.111951+00:00

The four local functions represent both automorphism orbits of three selected points and both orbits of four selected points in the cyclic Fano plane. `prepare.py` verifies all168point/line automorphisms, enumerates maximal independent-set negative rows, and checks the canonical4*k−1gate circuits on every assignment. Active input counts are9,10,11,10. A saving to4*k−2gates would extend to a26gate full Fano circuit; `lift_candidate.py` performs the extension and exhaustive16,384row verification. No saving was found.

Completed searches:

- Known11gate noncollinear three-star baseline, pinned: SAT in0.03seconds, exhaustive512rows correct. This is only an encoding sanity check.
- Noncollinear three-star target10gates, unrestricted topology apart from usedgates/commutingoperands: UNKNOWN after60seconds.
- Collinear three-star target10gates, ordered source maxima and edge-productive gates: UNKNOWN after20seconds.
- Quadrangle four-star target14gates, ordered source maxima and edge-productive gates: see exact SEARCH-RESULTS.json; no candidate.

`local_cnf.py` adapts counterexample agent’s exact AO2 synthesis encoder, preserving lineage SHA256 in its header. Every returned SAT candidate is checked against the local function on all2^n assignments before being saved. `local_read1.py` was prepared from the separately validated global squarefree-proof DP encoder but WAS NOT RUN locally before the stop instruction. No local nonread1-pruned result is claimed.

No result is a Lean proof or a Lean refutation. UNKNOWN is a timeout, not an UNSAT result. Restricted search conditions are recorded explicitly in each result. No claim that all subgraphs lack a saving is justified by these runs. Complete solver and driver stdout/stderr plus generated CNFs/data have been archived under diagnostics; hashes and sizes are in ARCHIVE-MANIFEST.json.

No desk calls, git writes, pushes, or PRs were performed by this agent.
