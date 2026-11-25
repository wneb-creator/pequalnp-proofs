# SAT counterexample search for L-meta-2592

CaDiCaL was built from the public arminbiere/cadical repository under task scratch. A C++ incremental CEGIS encoder models 19 binary AND/OR or unary NOT gates, exact-one wire selectors, acyclic references to earlier wires, output at the last gate, at least one NOT, and all gates live. A witness is evaluated independently on all 1024 inputs.

The 20-gate known monotone witness supplied by the counterexample agent passes the encoding with all selectors fixed and passes the independent 1024-input check. Generic 20-gate synthesis was undecided after 60 seconds; that is not a lower bound.

For the 19-gate four-error candidate (18 live monotone gates plus one dead NOT), a neighborhood with at most four changed gate triples is UNSAT in 2 seconds on 72 selected assignments. This is only a restricted computational result and is not Lean checked. A six-change neighborhood and a general first-gate-NOT-input shard remain in progress. Variants relocating the dead NOT to each slot have been generated.

Files in scratch: synth.cpp, seed952.txt, seed952-notpos0.txt through seed952-notpos18.txt, planted20.stdout, repair952-budget4.stdout, repair952-budget6.stdout, search19-notinput.stdout. All stdout/stderr is retained.
