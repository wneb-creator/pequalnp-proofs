# Four-input central-edge control

This is a computational control for the function `u v OR u A OR v D` on four Boolean inputs. Both formal derivatives on the central edge `u v` must be false. The encoding includes all 16 truth assignments, binary AND/OR gates, distinct earlier operands, and the last gate as output.

CaDiCaL reported UNSAT for five gates and SAT for six gates. These are solver results, not Lean or kernel-checked proofs. In particular, the five-gate result is **not** a lower bound for the eight-input double-star and is **not** a proof of L-meta-2602. Treating each three-leaf OR as an indivisible variable restricts the circuit class.

The six-gate witness is:

```text
w4 = v OR A
w5 = v AND D
w6 = u AND w4
w7 = u AND w6
w8 = w4 AND w7
out = w5 OR w8
```

Independent evaluation checks its distinct earlier operands, all 16 truth assignments, and both derivative traces. Replacing each of `A` and `D` with a three-input OR adds four gates and yields a ten-gate upper bound for the eight-input double-star. This gives no nine-gate lower bound.

The archived Python scripts are exact copies of the executed scripts, including their job-local paths. They import the encoder in `../repair_nearmiss_v3.py`, which imports the solver path from `../and_count_search.py`. `manifest.json` records those dependencies, solver and input CNF hashes, exact solver arguments, and complete output hashes. Solver stdout and stderr are preserved byte-for-byte in gzip files; the reproducible CNFs are omitted. `validate.py` independently rechecks the six-gate witness without the SAT encoder or solver.
