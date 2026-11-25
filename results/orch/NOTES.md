# L-meta-2592 orchestration notes

Held only by root pilot-95. Exact statement: scratch desk-next.json.
Only allowed project module: PEqualNP.Defs.
Existing reductions occupy all three slots.


- 2026-11-25T13:48:08.453466+00:00 reductions: cap saturated by 2592_271/_318/_408. Checked L_meta_4725 gives 15 + NOT-count <= size (>=5 NOT impossible). Checked L_meta_5236 gives >=16 binary gates for Petersen with supplied x0 OR x2, excluding >=3 NOT in 18-gate remainder. Details: lemmas/reductions.md.

2026-11-25T13:48:15.556907+00:00 proof_route: existing 15+NOT floor found (L_meta_4725); 9-input cofactor >15 bound found embedded in L_meta_9818. Missing bridge is ≥4 gate elimination under some restriction. Details in lemmas/proof-route.md.

2026-11-25T13:49:26.869316+00:00 Counterexample: no semantic loophole; two bitparallel 19-gate searches running, best initial discrepancy 9/1024. SAT/CEGIS child compiling CaDiCaL.

2026-11-25T13:52:00.779612+00:00 SAT route: CaDiCaL+CEGIS built; planted20 passes all1024 inputs. Four-gate-change neighborhood around four-error19 candidate UNSAT; larger/relocated-NOT neighborhoods and general first-NOT shard pending. No counterexample.

- 2026-11-25T13:52:01.949944+00:00 reductions: proposed stronger partial Sixteen.lean gives 16+NOTcount<=size by running L5236 signed certificate on the original ten pins; root Defs build pending. If compiled, this excludes all >=4 NOT circuits, leaving 1..3. Exact normalization component is already L7389.

2026-11-25T13:54:02.851971+00:00 proof_route: Restriction.lean compiled successfully (Defs only). kept_projection_bound converts a retained input made constant after the first binary gate into an extra gate lower bound. Generic lower L on a cofactor yields L+1≤tail gates, hence≥17 when L=15. Arbitrary-vertex projections and twin obstruction will combine.
