# L-meta-2448 independent definition and library audit

Reviewed the exact statement in desk answer 007 and the checked repository definitions on 2026-11-25. This note contains mathematical observations and a library inventory, not a proof of the held step.

The claim is existence of an exact graph-function circuit with minimum **total** gate count among all Monotone2 circuits, and with a star profile. Monotone2 permits zero/one/two-input AND and OR gates; forward or invalid reads evaluate false. Ownership uses the strict dependency cone and requires the AND to be true on the edge input while every earlier AND in its cone is false there. Owning no graph edge satisfies the profile. No defect was found in the empty graph or zero-vertex cases: an empty circuit with invalid output computes false and has a vacuous profile.

The exact function is required on every input, not merely singleton and pair inputs. Prior shadow counterexamples from L-meta-1896 therefore do not refute this statement. Triangle-free and C4-free does not imply bipartite, so the stronger available bipartite cleanup lemmas cannot be applied directly.

Useful accepted components:

- `L_meta_2666`: a minimum Monotone2 circuit exists for every finite graph function.
- `L_meta_1599`: every graph edge is owned by some AND in any exact AndOrOnly circuit.
- `L_meta_2668`: each AND in a minimum exact circuit is essential on an edge input: deleting it in favor of false changes acceptance of that edge. Essentiality does not assert ownership.
- `L_meta_1600`: a globally sound AND (its truth implies the graph function) has empty or star-shaped ownership in a C4-free graph.
- `L_meta_1603`: assuming all ANDs reject singletons, carriers have a two-operand singleton-product description. The singleton-rejection hypothesis is not derived.
- `L_meta_4181`: minimum TopForm normalization with nonincreasing size.
- `L_meta_4543`: a minimum TopForm can additionally minimize the cardinality of Ustar among such circuits.
- `L_meta_1499`: a globally sound AND below another AND can be exchanged to decrease andPairs without changing the number of dirty ANDs.
- `L_meta_3657`: under its stated live/lift-fixed/no-sound-operand assumptions, an AND is globally sound exactly when all strict descendant gates are OR gates.
- `L_meta_3653`: in the bipartite C4-free setting, exactly one dirty AND that accepts a singleton can be eliminated without increasing size, subject to the stated live/lift-fixed/no-sound-operand assumptions. It does not remove arbitrary dirty AND families.

`R_meta_2448_17` remains conditional. Its first hypothesis provides a minimum circuit where every two owned edges have a connecting owned edge. The proof then classifies nonempty owner graphs as double stars or five-cycles (up to isolates), with a five-cycle forcing the owner AND to accept a singleton. Its second hypothesis is the unresolved step extending the star profile through another gate while retaining eligibility. Neither hypothesis is an established consequence of the posted assumptions in that reduction.

No unconditional lower bound of total size `|E| + vertex-cover-number - 1`, or unconditional star normalization, was found in the checked main statements inspected. `L_meta_1601` and `L_meta_1602` retain a sound-AND counting theorem as a hypothesis; they do not prove it. `L_meta_1733` bounds only the edges outside Ustar after normalization.

The finite encoder review is recorded separately in `synthesis-independent-review.json`. Its C5 and C6 fixed star controls were independently replayed on all inputs. Solver UNSAT results concern a normalized finite model until the normalization and minimum claims are formalized in Lean.
