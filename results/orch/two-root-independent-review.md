# Independent two-root encoder and C8 fragment review

Reviewed by structure_proof at 2026-11-25T04:32:09.721230+00:00.

The exact two-root CNF encoder in `/tmp/oec/pequalnp-pilot-65/finite-search/two_dirty_roots.py` was read independently. Its Tseitin clauses correctly define AND/OR equivalence; the graph variables encode a 4-by-4 bipartite graph with a diagonal matching and no K2,2; its 256 truth rows, dirty-gate witnesses, marked pair mask17, and both formal derivative recurrences match the declared semantic model. The nonempty and identical-singleton restrictions accurately describe the requested distinct-fanin realization model. Root0 has D1 and D2 on opposite sides; root1 places each dirty gate on at most one side.

The original UNSAT claim applies to EXACT output equality with the graph function. It does not prove a pair-shadow cover bound for a subcircuit, which only needs output implication into the graph function. That distinction is essential: the implication-only control is SAT.

## Verified C8 counterexample to the proposed fragment cover bound

Inputs0,1,2,3 are points and4,5,6,7 are lines. The graph edges are:

`04, 05, 15, 16, 26, 27, 34, 37`.

Let

- D1 = (x0 OR x1) AND (x4 OR x5)
- D2 = (x4 OR x7) AND (x0 OR x3)
- R0 = (x2 OR D1) AND (x6 OR D2)
- R1 = (D1 OR D2) AND (x3 OR x5)
- H = R0 OR R1.

The implementation uses4AND and9OR gates with distinct earlier physical inputs. D1 is dirty at input pair14; D2 is dirty at input pair07. Both are true on marked pair04. Independent evaluation of all256 Boolean assignments confirms H implies the C8 graph function. Both formal derivatives at marked pair04, based at singleton0 or singleton4 respectively, are false.

The pair shadow is exactly `04, 05, 15, 26, 34, 37`, and therefore contains the diagonal matching `04,15,26,37`. Its vertex cover has cardinal at least4. This refutes the proposed statement that two such clean roots have pair-shadow cover at most3. It does not refute the full plane gap, nor a whole-function AND-count lower bound.

The missing graph edges16 and27 absorb higher terms but are not computed by H on their pair assignments. For example, D1's bad pair14 together with input6 is accepted through R0 and is justified by graph edge16; D2's bad pair07 together with input2 is justified by edge27. The exact mismatching masks are66,67,74,75,132,134,148,150,164,180,194,195. All are false negatives for H; there are no false positives.

Both D1 and D2 are false on pairs16 and27. With those dirty gates fixed, any extra clean root computing either missing pair must obtain it from its direct literal-by-literal term. One such root cannot directly compute both missing pairs, because its rectangle would include forbidden pair17. Thus this particular fragment needs at least two additional clean roots to complete the entire C8 function while retaining D1,D2.

The independent truth/trace log is archived alongside this note. The finite_search witness JSON and encoder should remain preserved by the root agent. Solver UNSAT without a Lean certificate is computational evidence, not a proof of a Lean theorem.
