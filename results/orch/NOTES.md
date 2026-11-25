# pequalnp-pilot-160 — L-meta-12087

Exact statement: scratch statement.txt; allowed project module PEqualNP.Defs. Root alone handles lease, integration and publication.

Strategies: circuit_search computational witness; lower_bound monotone lower bound; alternative_proof positive replacement route; status_review independent review.

## Root coordination
- 12-gate monotone witness found by circuit_search and checked all 64 rows. Searching mono11 and oneNOT11.
- PR16697 reportedly targets positive twin12086; independent reviewer investigating.
- Full Mathlib required: CheckLemma.lean imports Mathlib for statement environment. Toolchain being installed because kit cache absent.

## circuit_search — computational synthesis

Target table is 0xfe80e880fe008000, monotone. Minimal true masks: 15,25,26,28,39,43,45,46. Formula with a,b,c,d,e,f = inputs0..5:
F = abc(d OR f) OR de(a OR b OR c) OR df(ab OR ac OR bc).

Verified 12-gate monotone witness (wire6 onward):
OR(1,2), AND(1,2), AND(3,6), OR(5,7), AND(0,8), OR(0,8), AND(5,7), AND(3,4), OR(12,13), AND(9,10), OR(14,15), AND(11,16). Output17. Exhaustive64-row Python evaluation equals target. This is an upper bound only, not a proof of posted negation. SAT model found in37.8s.

Cofactor a=1 is table0xf8e8f080 on b,c,d,e,f. Verified monotone9 witness (wire5 onward): AND(1,2), OR(1,2), AND(2,3), AND(0,5), AND(0,6), OR(5,9), AND(4,10), OR(7,11), OR(8,12), output13. Exhaustive32-row check passes. Thus restricted monotone min10 route is unavailable.

Original mono11 and one-NOT11 synthesis timed out180s each: UNKNOWN, no lower bound. Optimized bounded searches remain active (300s each) as of pause after lease410. No new search will start until root confirms reacquisition. Native libz3.so.4 is available through Python ctypes; no solver package downloaded. Machine reports3 CPUs.

Scratch /tmp/oec/pequalnp-pilot-160/: search_circuit.py, search_optimized.py, search_symmetric.py, search_signed.py, search_cegis.py; corresponding search-*.log complete outputs. Witnesses search-mono-12.gates.json and search-cofactor-mono-9.gates.json.
