# Full-plane constructive CEGIS for L-meta-2056

The data contains exactly 52 positive incidence pairs and 704 maximal-false inputs for the sum convention (p+l) mod13 in {0,1,3,9}. The negative set was independently reconstructed from all8192point subsets.

The initial54-row sample consists of all52positives and the two pure-side negatives. An explicit25-active-gate complete-bipartite approximation, padded to63 gates, satisfies that sample and every SMT assertion but fails702 full-boundary rows. The independently reviewed refinement script added16 genuine diverse violated negatives, yielding70sampled rows. It does not accept raw SAT as a solution.

The old bitvector pipeline's70-row63-gate query returned UNKNOWN after171.374seconds of conversion and300seconds of native solving. The first obsolete54-row conversion was terminated after the explicit seed made it unnecessary. Complete stdout/stderr and metadata are retained.

The reviewed direct one-hot CNF encoder enforces only exact backward binaryAND/OR gate semantics and selected final truth values. It has no semantic normalizations. It validates every SAT clause assignment, reconstructs actual source-indexed gates, and checks all756boundary rows. Fixed64control and nontrivial free-last3control passed; the free suffix changed topology. Each control compiled about846000clauses in4.7seconds and completed in7seconds at156MB peak. CNF files are reproducible from the retained encoder, data, rows, gates and command parameters; their full solver logs, assignments, mappings and result JSON are retained here.

The63-gate70-row direct-CNF baseline reached its300-second native limit with UNKNOWN (conversion2.88seconds,295MB peak). No full-boundary63-gate witness or Lean proof has been found. Any future zero-violation candidate still requires the kernel-checked packed Lean verifier.

The independently approved normalized successor adds only ordered commutative operands, canonical OR for copies, a later reader for every nonfinal gate, and use of every nonisolated input. For unrestricted full-target search, dead gates can be deleted and the output padded with OR copies; arbitrary fixed-prefix repair queries should continue using the unnormalized encoder. The normalized free-last3 control passed every853718clause and all756boundary rows in4.44seconds at159MB. Both source and all control artifacts were independently reviewed.
