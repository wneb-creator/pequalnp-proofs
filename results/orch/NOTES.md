# L-meta-2592 orchestrator notes

Only the root agent contacts the desk or changes git state. Agents use assigned scratch files in results/orch/lemmas and record findings here.

Goal: no fan-in-two circuit of at most 19 gates containing a NOT computes the Petersen graph edge function. Exact statement: /tmp/oec/pequalnp-pilot-97/statement.txt. Allowed project modules: PEqualNP.Defs. There are already three live reductions; focus on a proof or counterexample.


## Review audit 2026-11-25T13:49:12.523782+00:00

All three reductions have one premise accepted: binaryFloor = L_meta_4725; normalize = L_meta_7389; cutLast = L_meta_8295. The other premise in each remains the substantive lower bound. See lemmas/notes-review.md for candidate reusable results and definition edge cases.

Toolchain ready: use PATH=/tmp/oec/pequalnp-pilot-97/toolchain/lean-4.36.0-linux/bin:$PATH. Cache get passed; all 9117 files decompressed. Full log /tmp/oec/pequalnp-pilot-97/toolchain/cache-get.log.

2026-11-25T13:51:29.976234+00:00: library route found accepted full Petersen non-NOT count floor15 (L4725/L6194), full Petersen-minus-vertex size floor16 (L4033). Thus candidates have1..4 NOTs, and a4-gate elimination suffices. Full findings: lemmas/notes-library.md.

2026-11-25T13:51:48.386765+00:00 Counterexample route: Counterexample-search strategy (in progress):
- Verified Petersen graph has 76 independent sets and independence number4.
- Generated40 standard20-gate monotone circuits from maximum independent sets, assigned remaining edges to6-star cover.
- Implemented C++ full1024-row bitset stochastic19-gate search. Best so far5 errors (not a witness).
- Toolchain Cadical now available. 19-gate synthesis with1..4 NOT gates and30 critical inputs is SAT in2s; decoded model fails410 other inputs. Boundary tests alone are insufficient with NOT.
- CEGIS now adds zero, all-ones, singleton and co-singleton inputs, then bad rows.
- Exact-one-NOT 30-row SAT is running separately. All programs/logs in /tmp/oec/pequalnp-pilot-97/counterexample.


## Checked partial 2026-11-25T13:52:43.574526+00:00

Named L_meta_2592.lean builds (exit 0), 3245 lines. Copied sanitized L_meta_4725 binary floor into L_meta_2592 namespace, all helper theorem keywords renamed lemma, added notCount_le_four and no_five_nots. No exact posted theorem yet. Full build log and validation summary are in results/orch. Root notified for independent review and immediate checkpoint push.
