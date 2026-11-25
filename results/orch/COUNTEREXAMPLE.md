# Counterexample strategy

2026-11-25: audited Circuit.eval and FanInTwo. Allowed gate operations are genuinely AND/OR/NOT, arity at most two; invalid and forward wire reads are false. No semantic loophole found.

Petersen graph has 76 independent subsets and independence number 4. Its five maximum independent sets are {0,2,8,9}, {0,3,6,7}, {1,3,5,9}, {1,4,7,8}, {2,4,5,6}. A six-vertex cover gives a 20-gate monotone circuit by six star terms (15 gates total) joined by five OR gates.

No z3, pysat, ortools, cadical, kissat, or minisat currently on PATH. g++ is available. Existing repository generator notes/data/lrat-link/gennot.py supports exact SAT encoding with general NOT. Root is checking the Lean toolchain for bundled cadical.

Implementing bit-parallel stochastic search near the 20-gate vertex-cover circuits while solver setup proceeds.

## Computational searches at 14:14 UTC

- Physical 19-gate stochastic search near 20-gate vertex-cover circuits: more than 130 million mutations; best required-NOT circuit still disagrees on 10 truth-table rows. An unrestricted monotone 19-gate candidate computes a Petersen supergraph with one extra nonedge and disagrees on 5 rows. No witness.
- One- and two-NOT exact SAT on only minimum-true/maximum-false rows returned spurious antitone circuits. Both were checked on all 1024 rows and rejected. Strengthened SAT includes all assignments of weight at most two, maximal independent sets, and all-ones.
- Exact one-NOT strengthened SAT ongoing, plus a variant requiring its monotone cut to be true on some maximal independent assignment and false on some edge assignment (idea from negation_theory). finite_certificate runs counts two through four.
- Local SAT repair of the near miss with four or seven unfixed gates was UNSAT (search evidence only, no Lean certificate).
- Signed 17-binary-gate stochastic search ongoing. Every exact semantic hit will undergo an exact inversion-cost check: remove outgoing parity constraints from at most two producer wires, solve the remaining polarity equations, and reconstruct physical AND/OR/NOT gates.
- Fresh signed SAT encoder uses all eight essential non-XOR binary Boolean functions. A polarity encoding enforces at most two shared producer inversions for 17 binary gates (at most 19 physical gates). This is exploratory, not yet linked to Lean. Decoder reconstruction was checked on all 1024 inputs with all eight operation types and arbitrary output polarities.
- A separate signed 15-gate SAT instance for vertex-deleted Petersen P9 tests whether a stronger signed lower bound of 16 may be feasible.

All programs and complete outputs are under /tmp/oec/pequalnp-pilot-111/counterexample/. No validated counterexample or full proof yet.

## Replan at 14:26 UTC

The initial stochastic run completed 1,806,800,000 mutations and 18,068 restarts without an exact result (best monotone candidate: five incorrect truth-table rows). The required-NOT run reached ten wrong rows before resource reallocation. Stochastic workers are now stopped.

P9 signed15 (ordinary vertex deletion x0=0) reached its 900-second limit with UNKNOWN. A separate P9 monotone15 CNF has been prepared but not run.

All semantic wires in the new signed encoder can be normalized to false on the all-zero input; this leaves AND, OR, a AND NOT b, and NOT a AND b as its four operations. Producer polarity variables and one optional complementary copy per producer translate this representation into physical AND/OR/NOT gates. This fresh encoder is exploratory and has no checked Lean transport bridge. A SAT witness will be reconstructed and checked exhaustively before any claim.

Three bounded SAT workers are active, each with complete stdout/stderr saved:
- `p10-b17-n2-edge`: 17 binary gates, at most two physical inversions, normalized first gate OR on adjacent inputs 0,1.
- `p10-b17-n2-nonedge`: same, first gate OR on nonadjacent inputs 0,2.
- `p10-b18-n1-normalized`: 18 binary gates, at most one inversion, including zero; no first-gate or useful-cut pruning.

The first-OR restriction for the 17-binary cases is based on combinatorial_proof's checked conditional structural result; its P9 lower-bound premise is being assembled by root. The one-NOT useful-cut/orbit files remain search-only and idle because completeness would require a monotone replacement lower bound.

Physical exact-NOT SAT searches must not be mistaken for complete lower-bound certificates: normalization may delete NOT gates. finite_certificate now has a separately checked transport for physical AND/OR/NOT canonical circuits with an at-most-NOT bound including zero, but that does not cover the new signed encoder.

## Preservation-only stop

2026-11-25T14:43:08.843609+00:00 Root reported lease loss and unsuccessful recovery; all searches were paused immediately and later terminated by SIGINT under root's instruction. Final three solver runs ended UNKNOWN (exit130), not SAT or UNSAT. The dedicated monotone18 three-minute diagnostic also ended UNKNOWN.

No target counterexample or full target lower-bound certificate was obtained. The initial boundary-only one-NOT and two-NOT models failed 899 and 874 complete truth-table assignments respectively. Local0/local1 UNSAT results only cover fixed-circuit repair neighborhoods.

Preservation inventory: /tmp/oec/pequalnp-pilot-111/counterexample/archive-inventory.json. It lists 113 complete textual logs, sources and metadata files (about 3.75MB), excludes CNF/LRAT data and compiled executables, and identifies the auxiliary negation-cover-seed.json. ARCHIVE_README.md gives provenance and regeneration instructions. Root will independently review and archive these materials before final stop. No desk requests or lease releases were made by this agent.
