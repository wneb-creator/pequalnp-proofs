CaDiCaL synthesis record for L-meta-921

All searches used the dual model: four-point line conjunctions on supports of size at most five. The target full problem has13 outputs and2380 promised assignments. No target proof or counterexample was obtained.

Encoder: cadical_synth.py. Sources are the active original input variables plus free false/true constants. Internal gates are ordinary binary AND/OR, with repetitions, duplicate functions, and unused gates permitted. Final output gates are AND sinks. Only operand ordering is used as a syntactic symmetry reduction. The output-sink and earliest-output-AND normalizations have sound paper arguments, but no complete kernel bridge to this encoding has been supplied. Free constants can be propagated away from a SAT candidate without adding gates. A lower-bound UNSAT result would still require the bridge from every original allowed circuit, including constants, unary gates, unavailable reads, and padding.

lean_setup independently reviewed the encoder and found no flaw in selector, gate, final-output, full-domain-validation, or constant-normalization logic. encoder_test.py constructs known9-,12-,39-gate line circuits, verifies every generated CNF clause under explicit satisfying models, and verifies their original-index normalized circuits on all2380 assignments. The test exited0; complete output is encoder-test.log.

1. Three nonconcurrent lines [0,1,2], cap8 gates.
31 necessary samples,975 variables,12139 clauses. CaDiCaL returned UNSAT in2.02 seconds. Files triangle8-i0.cnf, triangle8-i0.lrat, triangle8-i0.solver.log, triangle8-i0.result.json; driver triangle8-driver.log. This is a finite encoded-subproblem result only, not a Lean result or the posted39-gate lower bound. CNF154871 bytes, LRAT18167848 bytes.

2. Four lines in general position [0,1,2,4], cap11 gates.
Initial21 samples gave a partial SAT model, which failed100 of2380 full-domain assignments. The model is saved as general4-11-i0.candidate.json. Adding40 counterexamples yielded61 samples,2382 variables,35919 clauses. That query timed out after60 seconds and returned UNKNOWN. No fully valid small circuit was obtained. Complete artifacts have prefix general4-11.

3. All13 lines, cap38 gates.
The exact130 initial samples are saved in full38-seed.json: the zero assignment,13 exactline4 positives, all52 properline3 negative assignments, and64 weight5 negative assignments formed from three points of one line plus two outside points. Every weight5 sample omits every full target line. This seed already includes all proper triples; a26-gate triple-only circuit does not satisfy it.

The CNF had17235 variables and558231 clauses. The driver imposed180 seconds total budget, and CaDiCaL received179 seconds after encoding. Only one solver process ran, with a1536MiB address-space limit. It returned UNKNOWN (exit0) after179.58 seconds with maximum resident set size177.20MB. No SAT model or UNSAT verdict was produced. All artifacts are retained: full38-i0.cnf (9689533 bytes), full38-i0.lrat (826863155 bytes; incomplete proof trace), full38-i0.solver.log (21476 bytes; complete stdout/stderr), full38-i0.result.json, full38-driver.log, and full38-seed-audit.log. The partial trace is not an UNSAT certificate.

Kernel proof capabilities and plain-source limitations are recorded separately in sat-capabilities.md. In particular ordinary bv_decide adds an inadmissible reflection axiom, while a tiny from_lrat proof reconstructed from inline numeric data was checked with only the three allowed axioms. That capability probe does not certify any synthesis search here.

4. Final fixed-prefix discovery query, all13 lines, cap38 gates.
The same exact130 seed was used, with three additional unit clauses fixing gate0 to OR(input0,input1). There were17235 variables and558234 clauses. The first-OR reduction and point-pair symmetry are only mathematical/computational observations here, not a kernel-checked normalization, so this remains a restricted discovery query. The driver imposed120 seconds total, leaving119 solver seconds. CaDiCaL returned UNKNOWN (exit0) after119.58 seconds; maximum resident set size176.00MB. No SAT model or UNSAT verdict was produced. All CNF, partial LRAT, stdout/stderr, driver log, and result JSON are retained with prefix full38-or01. The partial LRAT is563916399 bytes and is not an UNSAT certificate. No solver process remains running from this agent.

A separate finite Python construction produced12 permutations fixing point0 and sending each nonzero point to1, and directly verified that they permute all13 cyclic lines. Data and reproducible checks are point-pair-automorphisms.json, automorphisms.py, automorphisms.log. This is not a Lean theorem or a checked circuit-renaming bridge.
