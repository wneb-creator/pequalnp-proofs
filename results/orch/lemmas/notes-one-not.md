# One-NOT algebra route

Verified in Lean (`OneNot.lean`, Mathlib-only dependencies):

- For `f(x)=G(x,not h(x))` and G monotone in the extra input, h<=f permits replacing the negated input by true; f<=h permits replacing it by false.
- If both constant replacements change the result, there are witnesses h=false/f=true and h=true/f=false.
- For the Petersen graph and monotone h, the first witness can be an edge and the second a maximal independent set.
- Explicit lists of 15 edges and 15 maximal independent sets have kernel-checked support certificates over all 1024 Boolean assignments. No native evaluation or added axiom.

Computationally checked, not yet formalized: the 120 Petersen automorphisms partition the 225 edge/maximal-independent-set pairs into five orbits. Representatives have edge mask 3 and independent mask 69, 521, 276, 773, 116, with orbit sizes 30,60,60,60,15. These constraints were sent to the SAT agent. Data: /tmp/oec/pequalnp-pilot-97/one-not/orbits.json.

Limitations: this does not provide a gate-count lower bound. It covers essential NOT; a nonessential NOT may instead be replaced by a constant, but proving the resulting monotone lower bound is still needed. Arbitrary semantic monotonicity does not justify replacing all NOT wires by constants; contradictory DNF terms can create false positives.

Potential structural subcase: sole NOT reads input v, positive v first enters AND, and the two simplification chains remain distinct. Setting v=false should erase the NOT, its first consumer, the positive AND and its next consumer: four gates, conflicting with the checked Petersen-minus-v bound16 at budget19. General first-use OR and merged-chain cases remain unresolved. Sent to structural agent.

Build command: PATH=/tmp/oec/pequalnp-pilot-97/toolchain/lean-4.36.0-linux/bin:$PATH lake env lean ../results/orch/lemmas/OneNot.lean (from lean/), exit0. Full stdout/stderr at /tmp/oec/pequalnp-pilot-97/one-not-graph-build.log (empty on success).

## Signed-source synthesis and reviews

Added /tmp/oec/pequalnp-pilot-97/one-not/signed_source.py (source now d2b97cd9e88d9139f10ed770cde5cb77efbb3085828f420adadade18d7c64793): shared marked sources eliminate explicit NOT positions; supports exact k marks, 52 critical or all1024 rows, essential witness masks, unrestricted-negation diagnostics, optional used-gate and adjacent-independent lex constraints. Decoder expands actual NOT gates and validates all1024 inputs. Counterexample agent independently passed known20-gate positive and22-gate signed-constant smoke tests. Old source retained as signed_source-before-lex.py.

Added phase_optimizer.py: enumerate gate polarity assignments by Gray code, dualize AND/OR and adjust input/output signs, minimize shared NOT-source count. Every result is checked against the original signed circuit and target on all1024 inputs. A planted nontrivial phase inversion of the known20-gate seed was recovered correctly. In unrestricted signed search, fixing all gates to AND is a valid DeMorgan gauge and removes phase symmetry. The checked non-OR seed bound means a correct17-binary AIG starts with two negatively signed inputs.

Independent reviews passed: LibraryOrReduction, FewNot, FewNotSeeds, FewNotGeneric, NonOrSeed. Reviews checked actual target transport, supply conditions, count charges, source equivalence and finite certificate data; imports in scratch composites require final inlining. All review details were sent to root.

Avoid an invalid next step: duplicate projected roots do not generically give another gate charge. Even monotone P4 `(a AND c) OR (d AND (b OR c))` uses4 gates and identifying a=b yields majority3, still needing4 monotone gates. Constant-root mass charges are sound; duplicate charges require extra structure.

2026-11-25T14:30:35.395465+00:00

CleanReader.lean compiled and frozen: SHA256 d707058e59dd8d32167b369b5afff086b9df6e3237e90b9ea69fd433e0d655fb, 182 lines, 8437 bytes. Generic antitone propagation treats each positive-literal reader paired with its complement as constant (AND/OR and fan-in <=2). Final clean_reader proves both positive input literals i,j have suffix gates that do not also read their own complement wire10/11 in prefix NOT i, NOT j, AND10 11 circuits computing Petersen. Finite singleton/edge witnesses are kernel-decided; only PEqualNP.Defs imported. Build exit0, empty /tmp/oec/pequalnp-pilot-97/clean-reader-build.log. Root independently reviewing; structural agent will combine with reader-count bounds to remove suffix reads of both complement wires.
