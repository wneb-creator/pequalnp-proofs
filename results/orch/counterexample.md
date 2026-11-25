## Counterexample strategy

2026-11-25T14:19:07.643818+00:00

Assigned L-meta-2592. Semantics checked: gates are AND/OR/NOT with at most two inputs, evaluated sequentially; unavailable wires return false. No semantic loophole found.

Three existing reductions already fill the reduction limit: R_meta_2592_271 (binary floor/few NOTs), R_meta_2592_408 (normalization), R_meta_2592_318 (last-NOT separator).

Compiled official CaDiCaL from https://github.com/arminbiere/cadical into scratch. Synthesis source is `/tmp/oec/pequalnp-pilot-118/synth.cpp`; five searches started at about 2026-11-25 14:18 UTC, logs `synth-case0.log` through `synth-case4.log`. Cases: first gate AND(edge), AND(nonedge), OR(edge), OR(nonedge), NOT(input). All use 19 gates and 1–4 NOTs, with every gate used and distinct operands for binary gates. These are searches for witnesses, not certified exhaustive lower bounds. Runtime cap is 1800 seconds per case.

Incremental SAT encodes all 76 false inputs and 15 positive edge inputs initially. Every candidate is checked on all 1024 inputs; up to32 counterexamples are added per round. Only a candidate passing full enumeration counts as a discovered counterexample. Search and diagnostics remain in scratch until parent decides what to preserve on branch.

2026-11-25T14:25:36.541990+00:00 Replan: all five original searches ran about six minutes with no satisfying candidate for the initial91 rows. Replaced with synth-v2.cpp: sparse20row initial set, adjacent independent-gate ordering, NOT bounds(2,2,3,2,3). Five new1800second searches running. Full1024 validation retained. No UNSAT or counterexample result yet.

The tempting deleted-Petersen15gate route is ruled out by existing results8033,8035,8037,8039; did not spend search time on it.

Potential proof leverage: deleted-Petersen binaryfloor15 plus19total with3NOT forces every xi=0 restriction to eliminate at most one binarygate. A first AND(xi,xj) eliminates itself and its first downstream binary user, contradicting this bound. Parent notified; formal normalization remains required.

2026-11-25T14:28:32.118837+00:00 v2 sparse strategy produced models quickly in allcases; all rejected on complete truth tables. ORnonedge secondmodel had144mismatches; ORedge secondmodel172. These cases now84constraints. Restarting firstANDcases with1NOTmax using descendants strongerbinaryfloor18 insight, retaining ORcase learned searches.

Started specializedH16gate1NOTsearch withfirstOR of two neighbors of removedvertex9. Relabeling originalinputs4,6 to0,1, permutationoldlabels=[4,6,2,3,0,5,1,7,8]. Any validHcandidate extends to19gate Petersen using threegates OR(firstOR,input7), AND(input9,that), OR(Houtput,that). Full512validation before conversion. Source synth-H.cpp, log synth-H.log.

2026-11-25T14:37:10.841562+00:00 CPUallocation: only specializedH16/1NOTSAT remains active while rootcertificate compiles. FullPetersenANDedge(PID4887),ANDnonedge(PID4885),ORedge(PID5650),ORnonedge(PID4409) pausedwithSIGSTOP, learnedstate retained. ActiveHPID4670. Timersarewalltime, so pausedcases mayexpire immediately ifresumedaftertheir30minute totaldeadline. No resultwillbeclaimed from timeout.

Prepared SATrepairsource synth-repair.cpp aroundlocalworker19gatecandidate; notcompiled orrunningyet. Repair cardinality bounds numberofchangedop/operandchoices relative to frozenrepair-seed.json, withwhole1024input validation.
