# Circuit-search strategy

2026-11-25 14:20 UTC. Checked actual Circuit semantics: out-of-range reads false, empty AND/NOT true, NOT ignores its second operand. No apparent witness loophole under FanInTwo.

System has libz3.so.4 although neither the z3 Python package nor a SAT binary is on PATH. Driving installed library through ctypes avoids installation/network changes. Script lives in /tmp/oec/pequalnp-pilot-121/circuit-search/synth.py, with full queries and outputs there.

The Petersen function has 76 zero rows and 15 maximal zero rows. Initial synthesis uses 15 edge (minimal true) rows and 15 maximal false rows. Search asks for 19 gates, all used, input pairs distinct for AND/OR, one through four NOTs, and output at the last gate. First gate split into five automorphism cases. This is intentionally a witness search only; the canonical restrictions have not been proved exhaustive. Any candidate must be checked on all 1024 rows before Lean formalization.

Initial cases running with solver time limits. No result yet.

First three 30-row cases were SAT, but full Python truth-table verification rejected every candidate: seed 0 (AND edge first) had 456 mismatches, seed 1 (AND nonedge) 794, seed 2 (OR edge) 635. All are spurious partial-row fits, not counterexamples. Full 1024-row seed 3 and stronger 82-row seed 5 now run, capped at 180 seconds.

Full19-gate cases seed3 (1024 rows) and seed5 (82 rows) timed out after180 seconds, UNKNOWN rather than UNSAT. A bounded C++ stochastic run reached18 mismatches but retained a useless NOT; no witness.

Switched to two smaller architectures proposed by other agents:

- Petersen minus vertex9:12edges on9inputs. A15-gate exactlyoneNOT witness would extend to a19-gate Petersen witness by appending four gates. Z3 seeds6 (stronger subset),7 (all512rows),8 (all512rows with gate distinctness and adjacent-independent lex ordering) are bounded at300seconds each.
- Five outputs on six inputs p,q,r,s,t,u: s∨t∨u; q∨r∨u; p∨r∨t; p∨q∨s; pu∨qt∨rs. An11-gate shared circuit with a NOT would append to19 Petersen gates. Z3 family.py encodes all64rows, up to3NOTs, all gates used, five output selectors, and symmetry constraints. Exact Petersen map from status_review: a1=x0,a2=x2,a3=x8,a4=x9; p=x6,q=x7,r=x3,s=x4,t=x5,u=x1. Add a_i∧c_i (4gates), then OR those four with H (4gates).

All these searches are witness searches. No claimed completeness or lower-bound certificate. Full source, SMT queries, stdout/stderr, and model files remain in the named scratch directory.

At14:34:55UTC, root limited the search to two heavy processes. Stopped the superseded generic9v essential-NOT run and a redundant family qfbv run; these have no verdict. Continued only9v15g essential-NOT via explicit qfbv and family11g via direct one-hot CNF/SAT. Termination details are in scratch resource-stop.json; complete prior logs remain.

The direct family-CNF implementation was sanity-checked by fixing a known13-gate monotone family circuit: SAT, model extraction successful, zero errors on all64 rows. This validates a positive control, not completeness of the11-gate symmetry restrictions.

Further solver refinement: the generic family11g run and direct CNF run both timed out. Active family123 enforces exactly one NOT, excludes the last two gate positions for it, and checks that replacement by either constant changes at least one output. The9v explicit-qfbv run checks the same essentiality on projected12-edge and12-maximal-independent rows.

Prepared but not yet launched symmetry refinements:9v Petersen-minus9 has12 automorphisms and16 orbits of the144 essentiality witness pairs (edge/MIS); family has S4 symmetry and12 orbits of180 marked-output witness pairs. Canonical pair disjunctions should retain a representative of any witness, modulo the other search normalizations; this is not a Lean proof. Data files p9-orbits.json and family-orbits.json. Next query files query-9-orbits.smt2 and family_orbit_cnf.py.
