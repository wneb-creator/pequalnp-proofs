# Counterexample search preservation

Gap L-meta-2592. Work stopped when root reported that the desk lease was no longer live. No further proof search is authorized by this archive. All active search processes were terminated by SIGINT after pausing; complete stdout/stderr were retained.

No full counterexample or full lower-bound certificate was obtained. Boundary-row SAT candidates were decoded and rejected on the complete 1024-input truth table. Local repair UNSAT results concern only fixed portions of one near-miss circuit, not the posted statement. All signed/polarity encodings are exploratory and have no checked Lean representation bridge.

## Sources and results

- `search.cpp`: 19-gate bit-parallel stochastic search near 20-gate monotone star covers. Compile with `g++ -std=c++17 -O3 -march=native`; run arguments were `600 2592`. Completed 1,806,800,000 mutations; best circuit has five incorrect inputs and no NOT.
- `search_not.cpp`: same search with a strong penalty for no NOT. Arguments `900 259299`; stopped during resource reallocation. Best recorded circuit has ten incorrect inputs.
- `signed_search.cpp`: signed-AND DAG stochastic search with exact producer-inversion minimization for exact semantic hits. Arguments `1200 17 259217`; stopped without an exact hit.
- `gennot_weak.py`: repository `notes/data/lrat-link/gennot.py` with row selection strengthened to all weight-at-most-two inputs, maximal independent sets, and all-ones. `count_clauses.py` adds exact NOT counts for witness searches; these exact-count shards are not complete normalized lower-bound certificates.
- `synth_binary.py`: fresh eight-operation signed binary DAG SAT encoder; `add_inversion_budget.py` adds physical producer phases and a shared-inversion budget; `normalize_cases.py` normalizes semantic wires to false at zero and optionally fixes the first OR pair to edge01/nonedge02.
- `decode_not.py`, `decode_binary.py`, `decode_physical.py`: independent model decoding and exhaustive truth-table checks.
- `validate_encoder.py`: four known-correct Petersen circuits satisfy every generated clause, including two asymmetric-difference constructions and a polarity-flipped construction. Full output is `schema-validation.stdout`. It reads the auxiliary input `../negation-cover-seed.json`, supplied by negation_theory.
- `make_local_repairs.py`: preservation-only reconstruction of the exact local0/local1/local2 CNFs from `search.stdout`; local0 and local1 returned UNSAT, local2 was not run.
- `orbit_cases.py`: generates five conditional useful-cut orbit shards for exploratory one-NOT searches. Those shards were not run.

The physical decoder reconstruction was also checked on all 1024 assignments using all eight binary-operation types and arbitrary producer polarities; `decoder-test.*` records that test.

## Reproduction inputs

The scripts were run from `/workspace/pequalnp-proofs`; some auxiliary wrappers retain the original scratch path `/tmp/oec/pequalnp-pilot-111/counterexample`. The allowed graph edge string is:

`01,12,23,34,40,05,16,27,38,49,57,79,96,68,85`

The vertex-deleted P9 graph uses nine reindexed inputs and edges:

`01,12,23,05,16,27,38,46,68,85,57,74`

General generation sequence (substitute numeric parameters and output paths as appropriate):

1. `python3 synth_binary.py 10 17 <edges> base.cnf`
2. `python3 add_inversion_budget.py base.cnf 2 budget.cnf`
3. `python3 normalize_cases.py budget.cnf normalized.cnf edge`

For the 18-binary/at-most-one-inversion case, use 18, 1, and `all`; it includes zero inversions and has no useful-cut pruning. The two 17-binary cases use `edge` and `nonedge`. The first-OR restriction depends on the structural lower-bound work assembled by root; failed searches alone do not establish it.

CaDiCaL was the binary bundled with Lean4.36.0; `cadical-version.txt` and `cadical-help.txt` identify its version/capabilities. Each long run had a built-in wall-clock limit and complete stdout/stderr redirected before startup. The final three runs were interrupted due to lease loss, not completed proofs. Their logs are `p10-b17-n2-edge.*`, `p10-b17-n2-nonedge.*`, and `p10-b18-n1-normalized.*`.

Large CNF and LRAT files and compiled executables are intentionally excluded from the archive inventory. CNFs can be regenerated from sources and accompanying metadata; no complete successful target UNSAT proof was lost by excluding them. All complete textual run logs are included.
