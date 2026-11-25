# Independent search review: L-meta-4675

Reviewer: lemma_inventory agent. Reviewed at 2026-11-25T17:27:59.656826+00:00.

Verdict: no underapproximation or invalid pruning found in the reported main C++ exhaustive searches or the free-gate SMT encodings. The evidence remains computational and is not a Lean proof or an independently checked UNSAT certificate. No giant search was rerun.

## Exhaustive C++ search

Reviewed counterexample-search.cpp, split-search.cpp, and dirty-search.cpp. Truth tables are exact for the queried n<=6; uint64 shifts range from 0 through 63. The two-bit colour tracks OR-only reach: inputs get their side's bit, AND resets to 0, OR takes union, and colour 3 is forbidden. Duplicate removal uses both truth table and colour, so it retains idempotent AND buffers which change colour. Replacing a duplicate by its earlier equal-labelled wire preserves downstream truth tables and colours and never increases either gate count. A minimal counterexample therefore has a duplicate-free representative.

The adjacent-order pruning is also sound: when the new gate does not use the immediately prior gate, the two are independent. A lexicographically least topological ordering by (truth table, colour) has no adjacent independent inversion. Reordering renumbers subsequent references but preserves both labels. Operand sorting is justified by commutativity. For nonempty edge functions an output cannot be a raw input; every possible earlier-gate output is encountered at its prefix. All gates in generated circuits read earlier wires and have fan-in exactly 2.

An independent Python graph census reproduced 14, 53, 188, 333 nonempty C4-free targets for 2x2, 2x3, 2x4, 3x3 respectively, with maximum conjectured bounds 4, 5, 6, 8. The retained complete logs search through 3, 4, 5, 7 gates, hence include every below-bound gate count for those dimensions. Coverage of at most 6 total inputs additionally uses side-swap symmetry, isolated-vertex padding and the separately proved star/empty cases. The 9,281,809,818 count is generated depth-seven extensions, not inequivalent circuits.

## Free-gate SMT encoding

Reviewed freegate-synth.py and all 101 archived free-*.smt2 files. Their assertions contain only nonempty selector groups, optional colour purity, commutative operand order and target equality; no unexpected distinct-function or structural restriction was present.

For AND counting, each original AND operand can be flattened through its OR cone into a nonempty subset of raw inputs and previous AND outputs. Prior AND outputs have empty OR reach. The pure-colour selector condition is exactly the zero-mixed-OR restriction on this cone. Output raw inputs are correctly excluded: any such OR-reachable input would force acceptance of a singleton, impossible for a nonempty bipartite edge function. Dropping the purity condition (--mixed) enlarges the class as claimed.

For OR counting, flattening AND cones dually yields conjunctions of raw inputs and previous OR outputs. The encoding imposes no colour restriction and is therefore suitable for the stronger unrestricted OR-count test. Identity padding and repeated signals are allowed, so exact k counted gates also covers fewer counted gates. All operands/output are nonempty, matching the no-constant AO2 setting; every finite monotone circuit with a nonempty edge function has such a representation.

Every edge pair is tested positive, and every maximal independent set is tested negative. Monotonicity then forces equality on every assignment. Thus restricting to boundary rows is exact for the output specification, not merely a two-hot test. The operand value-order constraint loses nothing because the counted binary operations commute.

An independent isomorphism check, canonicalizing sorted row bitsets under column permutations, recovered 9, 14, 21 classes for 2x3, 2x4, 3x3. The batch's AND records contain each class exactly once; the OR records omit only the trivial single-edge OR>=0 query. Cover sizes independently matched maximum matching search. All 85 batch records and their retained logs say UNSAT. Four archived SAT controls (K2,2 AND1/OR2; C6 AND3/OR5) were independently decoded and evaluated on all 16/64 assignments and matched the target.

## Fixed-total-size SMT caveat

synth.py additionally forbids duplicate (boundary truth vector, colour) states, requires each nonfinal gate to be used, and fixes the final gate as output. Its UNSAT result is therefore an exact irredundant-size result, not automatically a bound on all circuits of size<=k. Separate established optimality makes these restrictions harmless at the optimum. In particular, removing a duplicate boundary state preserves all boundary outputs and thus the full monotone target, so it contradicts optimality. A dirty gate is detected exactly by maximal-independent negative rows, since it is monotone. The author added this caveat to SEARCH_REPORT.md; the claimed complete small-case bounds rely on the C++ and free-gate encodings instead.

## Provenance and limits

Initial archive omitted exact SMT inputs and query arguments. This was reported and corrected: search-archive-manifest.json now includes .smt2, .stdout and per-file SHA256 values. Currently running files require a final manifest refresh before checkpointing. UNKNOWN remains UNKNOWN; timeout runs establish no lower bound. Z3 UNSAT responses have no retained proof certificate and are not consumed by Lean. The review supports the stated finite exploratory scope only, not the universal posted theorem.
