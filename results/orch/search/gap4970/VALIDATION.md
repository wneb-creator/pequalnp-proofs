# Gap L-meta-4970 finite checks

No counterexample was found. These are SAT experiments, not Lean proofs or certified lower bounds. The encoder was independently reviewed at SHA256 617e74a731ee5fa13bfcc3ccc14e034fe5636ef89de2fdc734fe7b36a1f741a9.

The model allows duplicate operands, unused gates, and an output before later serving-star gates. It enforces exact binary AND/OR gates with earlier inputs. Two-colour OR count uses syntactic OR-only reach, resetting at every AND. Pure serving-star functions are constrained on their singleton positive inputs and the complementary maximal false input; monotonicity makes these exact semantic constraints. Every emitted model is independently checked on its complete input truth table, all gate OR reaches, and every posted serving-star hypothesis.

Controls: P4 at 5 gates with an unused star OR after the output is SAT and fully checked on 16 inputs; C6 at 8 gates is SAT and fully checked on 64 inputs. P4 at 4 gates and C6 at 7 gates are UNSAT according to CaDiCaL. The independent reviewer replayed both positive models and checked all DIMACS clauses.

The 3-by-3 census has 10 side-permutation/side-swap classes, representing 228 labeled C4-free graphs with no isolated K2 component. Every case was UNSAT at |E|+tau-2 gates. Empty graphs satisfy the bound trivially; an isolated K2 contradicts the serving-star hypothesis. Exact-size searches include all smaller counterexamples by adding AND(output,output) gates, which preserve function, zero two-colour count, and existing star witnesses. This padding argument is mathematical context, not a new Lean certificate here.

Complete solver and driver output, models, and result JSON files are preserved in controls/ and census/. Regenerable CNFs remain in scratch.

The 4-by-4 census has 42 classes representing 14,088 labeled graphs under the same exclusions. An independent implementation checked all permutation/swap orbits and recomputed every vertex-cover number by maximum matching. At |E|+tau-2 gates, 28 cases returned solver-UNSAT and 14 returned UNKNOWN; none returned SAT. C8 at 10 gates was UNKNOWN after 30 seconds; the other cases had 10-second caps. This is incomplete finite evidence, not a lower-bound certificate. Complete output is in census4/ and COMMANDS_4X4.json records commands. Fresh census CNFs were hashed and deleted after solving to conserve disk; their hashes and byte counts are in the summary, and they are reproducible from the frozen encoder and archived graph data.
