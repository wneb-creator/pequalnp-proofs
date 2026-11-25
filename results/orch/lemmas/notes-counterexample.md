Counterexample-search strategy (in progress):
- Verified Petersen graph has 76 independent sets and independence number4.
- Generated40 standard20-gate monotone circuits from maximum independent sets, assigned remaining edges to6-star cover.
- Implemented C++ full1024-row bitset stochastic19-gate search. Best so far5 errors (not a witness).
- Toolchain Cadical now available. 19-gate synthesis with1..4 NOT gates and30 critical inputs is SAT in2s; decoded model fails410 other inputs. Boundary tests alone are insufficient with NOT.
- CEGIS now adds zero, all-ones, singleton and co-singleton inputs, then bad rows.
- Exact-one-NOT 30-row SAT is running separately. All programs/logs in /tmp/oec/pequalnp-pilot-97/counterexample.

2026-11-25T13:54:56.319620+00:00: stochastic full-row19-gate search completed300s; 1,467,814,678 evaluations across14,678 restarts; best5errors, no witness. Program SHA256 a4098cd7595eb7303b97a21957403569856adcb72f73b956f395b1794e120024.
Boundary exact1NOT returned SAT in115s but fails870/1024 inputs. CEGIS with0,all1,singletons/co-singletons ended UNKNOWN after120s. Full1024row exact4NOT SAT and essential1NOT orbit69 SAT are active. A second stochastic run rewards active NOT gates.

2026-11-25T13:58:00.220288+00:00: capped computational search to3 CPUs for Lean workers. Stopped second stochastic pass and redundant CEGIS retry; retained full logs. Currentjobs: full1024rows exactly4NOT (600s), essential1NOT firstorbit69 (300s), and sequentialessential1NOT orbits521,276,773,116 (300s each).

2026-11-25T13:58:58.964547+00:00: essential-one-NOT orbit69 SAT returned UNKNOWN at300s (269.6 CPU seconds,101.6MB). This gives no exclusion proof. Full1024row exactly2NOT synthesis started with output-not forbidden by structural route normal-form observation;19 gates all used.

2026-11-25T14:03:21.879010+00:00: stopped fullrow4NOT SAT after root identified acceptedL_meta_6581 proving≥16nonNOTgates for Petersen. Thus4NOT+15binary already impossible by existing proof; solver interruption itself has no logical verdict. Focus now1NOT18binary and2NOT17binary signedsource encodings.

2026-11-25T14:18:24.664907+00:00: allfive explicitNOT essentialorbit SAT cases UNKNOWN300s each; signed1NOTorbit69 UNKNOWN300s; standardfull2NOT UNKNOWN600s. Signedgenerator smoke tests (20binary0NOT and21binary1NOT withnegativefalsewireuse) passedall1024rows. Delete2binary+insert1sharedNOT neighborhood over40correct20gatecircuits exhausted183,416,922 configurations, none matched32criticalrows.
