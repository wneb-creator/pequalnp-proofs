# Computational search for L-meta-3451

These experiments search finite binary monotone AND/OR circuits. They do not prove the posted universal Lean statement. No counterexample to that statement has been found. Solver UNSAT verdicts below are external computational evidence; they are not Lean kernel checks.

## Search scope and normalization

For a nonempty bipartite incidence graph with N vertices per side, the target is the disjunction of its edge conjunctions. A clean AND gate is false on every singleton assignment and every nonincident cross-pair assignment. The searches use earlier-wire selectors, binary AND/OR gates, and no constants. Unary gates, constants, unused gates, and duplicate truth functions can be removed by ordinary semantic preprocessing; that preprocessing has not been formally connected to these scripts in Lean.

An output-last circuit of at most k gates can be padded to exactly k by output copies. Standard searches permit OR copies. A single AND-count budget permits OR-copy padding; a single OR-count budget permits AND-copy padding. A script supporting both budgets must not claim at-most-k completeness from this padding argument.

Exact boundary searches test all positive edge pairs and all maximal independent negative assignments. Their extra singleton and nonedge tests express cleanliness directly. The parent proof contains a Lean theorem that monotonicity makes edge/maximal-independent boundaries complete, but the executable encoding, graph census, model translation, and UNSAT reports remain external computations.

The reviewed symmetries include graph input automorphisms and lexicographic ordering of adjacent independent gates. There is a representative satisfying both sets of constraints: choose a globally lexicographically least input relabeling and topological gate order. The independent review is recorded in ../review-computational-evidence.md.

## Completed results

* All 15 C4-free labeled 2-by-2 graphs: exhaustive circuit-state search agrees with clean constructions, maximum size 4.
* All 334 C4-free labeled 3-by-3 graphs: 15 nonempty circuit isomorphism classes. Exhaustive search through seven gates settles 14 classes and excludes the remaining C6 class through seven. A clean eight-gate C6 circuit is exhaustively validated. All 334 clean witnesses are retained.
* All 25 essential C4-free 4-by-4 graph isomorphism classes: clean witnesses of at most 12 gates are exhaustively validated. A 90-second unrestricted SMT census proves 14 classes UNSAT at one below their clean upper bound; 11 time out. No lower-bound SAT witness was found.
* A longer CaDiCaL run settles C8 (mask 43365): at most 10 gates is UNSAT after 268.96 seconds, matching its clean upper bound 11. Together with the census this settles 15 of the 25 classes computationally.
* At the known minimum sizes for P4, P4 plus a disjoint edge, P6, and C6, requiring a dirty singleton AND or a dirty nonedge AND is UNSAT in each case. This is evidence about those four optimal finite cases only.
* For C6 at total size at most 10, at most two AND gates is UNSAT after 57.43 seconds. At most four OR gates times out after 60 seconds. Neither result is a general gate-count theorem.

`counterexample_n4_summary.json` is the original frozen census; the later C8 result is separately recorded in `../counterexample-extra-results.json`. The interrupted clean census and interrupted 300-second C8 trial are explicitly labeled unfinished. They are never counted as UNSAT or completed timeouts.

## Retained certificates and logs

The exact C6 CNF and its binary LRAT certificate are losslessly compressed under `../certificates/`. Metadata records compressed and uncompressed SHA-256 hashes, CaDiCaL 2.1.2 binary hash, commands, exit status, and the absence of Lean certificate checking. The compressed pair totals 2,099,772 bytes, exceeding the posted proof-file size cap even before a checker is included. C8's exact CNF is also retained compressed; no LRAT was generated in that run.

All reported searches retain complete stdout and stderr. The scripts record source hashes, solver versions, tested assignments, verdicts, and statistics. UNKNOWN and interrupted runs provide no lower bound. SAT models are evaluated independently on every full assignment before being called witnesses.

## Adaptive CEGIS

`counterexample_cegis.py` begins with singleton and cross-pair samples. A sampled SAT candidate is checked on the entire truth table. Each false positive is extended to a maximal independent assignment and added as a negative sample. Only an event named `full_validated_sat` is a full witness; an ordinary `check` event with `status: sat` may describe a rejected sampled candidate. The N3 smoke run exercised both paths and recovered a valid clean eight-gate cycle circuit. The current N5 cycle run seeks at most 13 gates against a verified clean upper bound of 14.
