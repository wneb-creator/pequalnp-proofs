Focused exactly-one-NOT local SAT search

100 neighborhoods of verified20gate Petersen monotone circuits were searched with one gate constrained to an OR wire, giving at most19gates after bypass. Each search enforced exactly one NOT and fixed every gate outside the recorded related neighborhood. Relaxed-gate counts: {3: 21, 4: 29, 5: 25, 6: 4, 7: 21}. All100 returned solver UNSAT, zero UNKNOWN, zero SAT witnesses; total search94.111s. Each trial had a25s wall cap and200,000conflict cap per round, substantially above the earlier3000conflict lane.

All trials used91necessary truth rows (all76independent-set negatives plus15edge positives). Any SAT candidate would have been checked against all1024rows and every failing row added; no trial reached a SAT candidate. Thus these are local necessary-row UNSAT results only, not a global19gate lower bound and not Lean-checked UNSAT certificates.

Dynamic encoding controls passed: all20gates encoded with variable pins then fixed to the known circuit returns SAT on all1024rows; adding exactly-one-NOT to that fixed monotone circuit returns UNSAT; a two-gate NOT(x0) then OR(false) returns SAT on all1024rows for the complementary projection target.

Exact source and complete stdout/stderr logs are preserved, with100 trial JSON files giving the seed circuit, skipped gate, relaxed set, limits and outcomes. focused.py reuses the archived parent search/synth.py, search/local_sat.py and cadical_wrap.cpp; its absolute scratch paths reflect the execution environment. No unrestricted search lane was rerun.
