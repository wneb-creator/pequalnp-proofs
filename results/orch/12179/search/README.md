# L-meta-12179 computational synthesis controls

The target is the exact truth table `3892346880 * 2^32 + 2147483648`, hexadecimal `e800800080000000`. It equals input3 AND threshold4 of the other five inputs.

Two direct SAT searches for ten-gate circuits (general AND/OR/NOT and monotone AND/OR) were stopped after the separate Lean proof established that every general circuit computing the target needs at least eleven gates. **Neither solver reached a SAT or UNSAT verdict.** Their complete logs are retained; these searches are not used as proof evidence.

`synth.py` models the actual permissive circuit definitions: a free false sentinel represents malformed references, constant true and false gates are counted, unary copies repeat their input, NOT ignores its second input, and all64 assignments are encoded. Output-last and use of every intermediate are justified informally by removing dead gates and padding a smaller circuit with identity AND gates. The symmetry restrictions order adjacent independent gates and retain first-operand-pair representatives under all120 input permutations fixing input3. These encoder completeness arguments have not been formalized in Lean.

A canonical eleven-gate monotone control and a thirteen-gate general control obtained by adding two NOT gates were constructed directly. Their assignments satisfy every clause, including symmetry constraints, without using a SAT solver. The decoder independently checks all64 truth-table entries and emits the actual circuit wire numbering in each witness JSON. `control.log` and `control_not.log` record the checks. These are computational controls, not a proof of the posted statement.

To reproduce the searches with Python3 and CaDiCaL on PATH:

```sh
python3 results/orch/12179/search/synth.py build 10 general /tmp/oec/pequalnp-pilot-157/12179/general10
cadical -t 1200 /tmp/oec/pequalnp-pilot-157/12179/general10.cnf > /tmp/oec/pequalnp-pilot-157/12179/general10.solver.log 2>&1
python3 results/orch/12179/search/synth.py decode /tmp/oec/pequalnp-pilot-157/12179/general10 /tmp/oec/pequalnp-pilot-157/12179/general10.solver.log
```

Use `monotone` instead of `general` for the second basis. The positive-control scripts use the same scratch directory and expect metadata built with `build 11 monotone .../monotone11_control` or `build 13 general .../general13_control` respectively. `MANIFEST.json` records byte counts and SHA256 digests; `STOP-STATUS.json` gives exact termination status. The proof and refutation live outside this search bundle.
