# L-meta-14985 orchestrator notes

Graph edges: 04 14 05 15 06 26 36 46 07 27 37 57. Posted statement negates the claim that one-NOT circuits can always be replaced without gate penalty.

Strategies: circuit synthesis, monotone lower bound certificates, independent proof/truth investigation, root Lean integration.

## Circuit search 2026-11-25T18:36:34.365872+00:00
11-gate monotone witness verified by Python on all256 inputs: [('or', 2, 3), ('or', 0, 8), ('or', 9, 4), ('and', 6, 10), ('or', 9, 5), ('and', 7, 12), ('or', 0, 1), ('or', 4, 5), ('and', 14, 15), ('or', 11, 13), ('or', 17, 16)], output18. x2,x3 only enter as c=x2 OR x3; effective7-variable function is (a OR b)(d OR e) OR (a OR c)(f OR g) OR df OR eg. No witness after >760 million random10-gate one-NOT candidates. Exact Z3 search uses system libz3.so.4 via ctypes; at-most1 NOT and exactly1 variants running.

2026-11-25T18:37:02.014625+00:00 proof_routes: Target has no isomorphic existing 8-input 12-edge theorem and no induced C5. Restriction x3=false is graph-isomorphic to checked L_meta_11741. New input coords map to old [0,2,1,false,5,6,3,4]. Old file proves lower9 for binary gates with free complement. Its lower_slice theorem (lines881-926) raises lower by each essential root made constant. Taking singleton input3 yields binary lower10 for target8. Essential input3 is witnessed by assignments64 and72. Then any NOT circuit has at least11 total gates; monotone11 witness finishes positive replacement statement and hence refutes assigned negation.

2026-11-25T18:37:10.596495+00:00 certificate_generator: independently checked all 512 rows of map target←old [0,2,1,constant0,5,6,3,4], existing oldGraph table equality, and input3 essential witness rows64/72. All pass. No forbidden-format candidates in L_meta_11741 source. Evidence scratch certs/mapping-check.json.

2026-11-25T18:37:40.046816+00:00 lower_bound: Located L_meta_11741 core graph after deleting target twin vertex3. Its helper framework gives a lower bound of9 binary gates even when complementation is free. lower_slice lifts by1 via essential input3 set false. Wrote target8 circuit bridge and positive finish in results/orch/lemmas/lower_bridge.lean; proof_routes owns lift. Thus any circuit using NOT has≥11 total gates and is replaceable by known11-gate monotone witness; circuit without NOT replaces itself. This refutes assigned negative statement.

### Circuit search stopped 2026-11-25T18:37:46.777197+00:00
Root found a theoretical lower-bound route and requested CPU release. All four owned search processes received SIGTERM and terminated with exit143. No circuit counterexample found. Heuristic non-discovery is not a lower bound.
- anneal10.log: restart=15820 iterations=1582100000 best=8
- anneal10mono.log: restart=6180 iterations=618100000 best=4
- synth10.log: terminated before solver verdict; inconclusive
- synth10-atmost.log: terminated before solver verdict; inconclusive

2026-11-25T18:37:58.442644+00:00 proof_routes: Wrote results/orch/lemmas/routes_lift.lean (GraphTarget8.minimum). Uses existing lift_ok certificate wrapper rather than new mathematical proof. Permutation swaps (1,2),(3,7),(4,5),(5,6),(6,7), followed by bit3→0, reproduce old GraphTarget.full. Helper must be appended after original11741 aux declarations renamed to14985_aux and before lower_bridge.lean. Lean compilation pending root toolchain restoration.
