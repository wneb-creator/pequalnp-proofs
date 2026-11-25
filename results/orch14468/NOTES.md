# L-meta-14468 shared notes

Lease issued 2026-11-25T18:07:24.727Z. Root owns lease and git. Graph edges: 04,15,06,26,07,17,27,37,57. Known 11-gate monotone baseline.

## 2026-11-25T18:11:53.064097+00:00 — independent monotone search

Stable baseline11.json computes exact target on all256 assignments. Exact monotone extrema are9edge rows and7maximal-independent rows. Fixed10diagnostic3.48millionupdates foundonly baseline-minus-edge0,4 (9livegates,0FP/12FNfullcube). Elastic14diagnostic preservescorrectness, best11. Rootrenewed18:10:49; two distinct600-second searches active, fixed10 andelasticlive-count. Leanbaseline translation delegatedtolean_setup. No10gatewitness.

## Current routes (18:12 UTC)

- Constructive: independently validated 11-gate monotone circuit; fixed-10 and elastic searches running.
- Lower bound: one NOT with at most 10 total gates has at most nine binary gates. A binary-count lower bound of ten closes replacement using the baseline.
- Cofactor: setting pendant vertex 3 false gives a seven-input graph. A free-NOT binary lower bound of nine there, plus a charged eliminated binary gate, would close the result.
- Structural: a live ten-gate circuit with exactly one unary NOT and nine binary gates on eight essential variables has external repeats plus internal fanout surplus equal to two.
- Public proof: status_check found exact pending PR 18915 (Leg0shii), updated before our assignment; source/status inspection in progress. Any reused work must be attributed.

Only root performs desk and git writes. Current heartbeat: /tmp/oec/pequalnp-pilot-103/heartbeat14468-state.json, five-minute cadence.
