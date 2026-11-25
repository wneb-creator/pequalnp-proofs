# Petersen circuit search checkpoint

These are computational search records, not Lean lower-bound certificates.
No counterexample or certified UNSAT result was found in these concluded runs.

- `circuit_search_120.log`: interrupted stochastic search after about 118 seconds and 1.1 billion mutations; best 19-gate monotone circuit has nine errors among 1024 inputs. The best JSON was independently evaluated in Python.
- `circuit_search_p19_not0.log`: full truth-table SAT, 19 gates, one to three NOT gates, first gate NOT(input 0), UNKNOWN at 1200 seconds wall time. There were 795084 conflicts and 669.94 seconds CPU time.
- `circuit_search_p19_and01.log`: same full truth-table problem with first gate AND(input 0,input 1), interrupted with UNKNOWN to diversify the search.
- `circuit_search_cegis19*`: initial 42-row boundary CEGIS with any first gate and one to three NOT gates. No model within 180 seconds; UNKNOWN.
- `circuit_search_cegis19_or02_3*`: boundary CEGIS with first gate OR(input 0,input 2) and exactly three NOT gates. No model within 300 seconds; UNKNOWN.
- `circuit_search_known20.json`: explicit 20-gate monotone upper-bound circuit, checked in Python on all 1024 inputs and against all 1424364 clauses in the custom full-row CNF.
- `circuit_search_signed_smoke.log`: clause-by-clause validation of the distinct-complemented-wire encoding and decoder on all 1024 rows of a small signed circuit.
- `circuit_search_repair8*`: local repairs of the 19-gate near miss with seven or eight gates free. Forty-four completed ten-second trials returned UNKNOWN; the next active trial was interrupted on the parent's stop instruction.
- `circuit_search_signed18_1*`: 18 binary gates and at most one distinct complemented wire, initially 42 rows, 4529 variables and 65197 clauses. Interrupted during its first solve on the parent's stop instruction; UNKNOWN.

Complete stdout and stderr are combined in each `.log` file. `MANIFEST.json` lists checksums of the files in this checkpoint. Large derived CNF files stay in task scratch storage; scripts in `results/orch/lemmas/circuit_search*` reproduce them.

The custom encodings are used to find witnesses. UNSAT from these scripts would need a separate Lean proof and a proof that all normalization restrictions preserve every relevant circuit. Timeouts establish no mathematical lower bound.

The parent reported a desk lease error at 14:38:48 UTC and instructed all searches to stop. Both active jobs were terminated with SIGINT. The final checkpoint at 14:39:50 UTC contains 108 log, solution and JSON data files totaling 446077 bytes, excluding this README, the manifest and outcome summary. No proof or counterexample was obtained.
