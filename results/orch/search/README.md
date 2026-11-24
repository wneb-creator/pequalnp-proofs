Counterexample searches for L-meta-2028

No counterexample has been found. These are computational searches, not Lean proofs.

Primary programs
- synth.py: binary AND/OR circuit SAT encoding; fixed graphs use edge-pair positives and maximal-independent-set negatives, unknown graphs use all Boolean inputs.
- and-synth.py: fixed-graph normalized AND-only skeleton, with arbitrary OR subsets between AND gates. With --size, ORs are charged by unshared expansion; this restricted cost model does not encompass arbitrary OR sharing.
- and-decode.py: independent full truth-table evaluation and binary expansion of normalized AND models.
- anneal.py: stochastic binary circuit optimization from star-cover seeds.
- quotients.py, restrictions.py, substitutions.py: input identifications and/or constant substitutions, full truth-table checks, semantic gate deduplication, and exact finite vertex-cover computation.
- Batch drivers and graph data preserve the individual queries.

Complete stdout/stderr from every retained solver run is in its .log file. Regenerable CNF files and the solver source are omitted. Kissat source commit is in MANIFEST.json. Drivers currently name the original scratch paths; inspect those paths when reproducing elsewhere.

A solver UNKNOWN verdict is a timeout, not an impossibility result. Local-template UNSAT results cover only the stated edit neighborhood. No UNSAT certificate was translated into Lean. Positive controls exactly meet the lower bound; their is_counterexample flag is false.

The initial uncorrected anneal.log and anneal-best.json ran the wrong graph and are deliberately excluded. Correct 11-vertex stochastic results are anneal-seed11*. The exact seed11.cnf was generated from the correct graph before a metadata filename collision and is unaffected. seed11-graph.json is the authoritative 16-edge target.

See ../search.md for the chronology, scope limits, and independently reviewed results.
