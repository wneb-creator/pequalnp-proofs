# Cubic Heawood gate-elimination assessment

Assessment finished 2026-11-25, approximately 08:15 UTC. This is a separate route from the capped one-dirty work. No new Lean theorem, circuit witness, or UNSAT result was produced. The finite restriction recurrence below reaches only the already known 20-gate general lower bound, so it does not support a refutation of the posted 26-gate existence statement.

## Primary sources read

- John E. Savage, [Models of Computation, Chapter 9](https://cs.brown.edu/people/jsavage/book/pdfs/ModelsOfComputation_Chapter9.pdf), sections 9.3.2 and 9.6.1, read 2026-11-25: “The gate-elimination method uses induction on the properties of a function”. Definition 9.3.1 requires both at least three subfunctions for every input pair and recursive preservation under an appropriate restriction of each variable. Theorem 9.3.2 gives `2n-3` over all binary Boolean gates for that recursively defined class. Its proof is not a theorem from the initial pair property alone. The monotone path-elimination examples concern sorting and merging.
- Stasys Jukna, [Disproving the Single Level Conjecture](https://web.vu.lt/mif/s.jukna/ftp/single1.pdf), SIAM Journal on Computing 36(1), 2006, read 2026-11-25. The paper distinguishes unrestricted monotone Boolean circuits from single-level circuits and disproves a general constant-factor normalization. Its displayed separating graphs are saturated extensions of bipartite graphs, with cliques added inside both parts. This does not settle the cubic bipartite case, and its single-level bounds cannot be imported as unrestricted bounds.
- Peter A. Bloniarz, [The Complexity of Monotone Boolean Functions and an Algorithm for Finding Shortest Paths in a Graph](https://bitsavers.trailing-edge.com/pdf/mit/lcs/tr/MIT-LCS-TR-0238.pdf), revised MIT report, January 1979, read 2026-11-25. The quadratic-function chapter treats worst-case complexity and AND-gate complexity; I found no exact cubic graph theorem. Its historical discussion also distinguishes multioutput direct sums from an OR of disjoint functions. I have not verified the current status of the latter additivity question.

UNVERIFIED references: the full text of Bublitz's 1986 graph-decomposition paper was not obtained; no cubic/girth-specific theorem is attributed to it. The site's `papers/note-1` appeared in search results but could not be opened, so its descriptions are not used as evidence. The author-hosted full Jukna book PDF timed out; no precise theorem is attributed to that unread PDF. These access failures are not mathematical evidence against any proposed result.

## Exact finite checks

Reproduction source: `/tmp/oec/pequalnp-pilot-70/lower-bound/cubic_gate_elimination_probe.py`.
Complete stdout/stderr: `/tmp/oec/pequalnp-pilot-70/lower-bound/cubic-gate-elimination-probe.log`.
The Python process exited 0 in about three seconds. It uses the exact 21 assignment edges, canonical quadratic-plus-linear cofactors, brute-force vertex covers, an exact-cover enumeration of triple systems, and complete truth tables for the two small examples. These are ordinary finite computations, not Lean certificates.

| Restriction | Number of cases | Remaining variables | Quadratic edges | Minimum cover | Star circuit upper bound |
| --- | ---: | ---: | ---: | ---: | ---: |
| One variable = 0 | 14 | 13 | 18 | 6 | 23 |
| Two distance-1 variables = 0 | 21 | 12 | 16 | 6 | 21 |
| Two distance-2 variables = 0 | 42 | 12 | 15 | 5 | 19 |
| Two distance-3 variables = 0 | 28 | 12 | 15 | 6 | 20 |

The last column is an upper bound, and a pair-clean optimum under the existing clean-circuit theorem. It is **not** an established unrestricted optimum.

Every one-cofactor has three linear variables and a 10-variable, 12-edge quadratic component with cover number 4. The corresponding explicit star construction uses 18 gates after adjoining the three linear variables. The nonlinear graph is the incidence subdivision of K4.

All original and one-zero cofactors give four distinct subfunctions for every pair. Among the 91 two-zero cofactors, 42 have minimum pair count 3 and 49 have minimum pair count 4. Among the 364 three-zero cofactors, exactly 14 fail the three-subfunction condition, precisely when a vertex's three neighbors have been deleted and it becomes inessential. Each one-cofactor fails the condition on the three pairs drawn from its three linear variables. Thus the initial robustness does not give the recursive class required by Savage's theorem.

There is no smaller simple cubic bipartite C4-free graph: with `m` vertices per part, its neighborhoods contribute `3m` distinct pairs in a part, so `3m <= m(m-1)/2` and `m >= 7`. At equality, these triples form a Steiner triple system on seven points. The script exhausts all 30 labeled systems and verifies that all 30 belong to one orbit under the 5,040 point permutations; the assigned Heawood neighborhoods occur in that orbit. This observation concerns the bipartite class specifically; Petersen is a smaller nonbipartite cubic C4-free graph.

Two weakened claims are already false. Cubicity without the C4 restriction permits K3,3, whose exact function has a five-gate circuit on six inputs. Robustness of all one-variable cofactors alone does not imply `2n-1`: majority on three inputs has the four-gate circuit `(x AND y) OR ((x OR y) AND z)`. The script verifies these circuits on all 64 and 8 inputs, respectively.

## What bottom-gate elimination actually yields

For a reduced minimum circuit, take a bottom gate `g = op(x,y)` on distinct raw inputs. If x has only this one occurrence, setting y to the canalizing value of op makes the whole function independent of x. For Heawood this is impossible for either input: an OR bottom gate would force containment of distinct cubic neighborhoods, while an AND bottom gate would force degree at most one. Both bottom inputs therefore have fanout at least two.

Fixing x removes its direct consumers. If the chosen value also makes g constant, at least one successor of g disappears. That successor is distinct from every direct consumer of x: a binary gate reading both x and `op(x,y)` is redundant by absorption or idempotence, contrary to minimality. Since the full function depends on more than two variables, g cannot itself be the output. This gives three eliminations for a canalizing assignment, but only two for the other assignment.

Even granting the unproved unrestricted 23-gate deleted-vertex optimum, an AND bottom gate followed by the three-deletion argument reaches only 26. For an OR bottom gate, the three-deletion assignment is x=1, whose cofactor has an 18-gate upper bound; the x=0 branch gives only two guaranteed deletions. A fourth deletion or a new global charge is essential. No rigidity classification of unrestricted 23-gate cofactors was proved.

I tested the strongest direct recursive version of this local argument over every reachable canonical quadratic-plus-linear cofactor. For each hypothetical bottom `op(x,y)`, pair-cofactor inequality determines whether each input must occur at least twice. The recurrence takes the maximum of the four input/value restriction bounds for that bottom gate, then the minimum over all possible bottom gates. It includes the extra canalizing-successor deletion and the essential-variable lower bound.

Source: `/tmp/oec/pequalnp-pilot-70/lower-bound/cubic_gate_elimination_dp.py`.
Complete stdout/stderr: `/tmp/oec/pequalnp-pilot-70/lower-bound/cubic-gate-elimination-dp.log`.
Exit 0; 141,468 distinct cofactor states; 29.21 seconds. Result: Heawood 20, each zero-cofactor 18, each one-cofactor 16. The implementation checks every resulting value against an explicit bipartite star upper bound. This experiment is not a machine-checked lower-bound proof; its purpose is to show that this precise local recurrence does not improve the existing bound.

## Remaining obstruction and recommendation

The live binary-DAG identity `gates = raw-input occurrences + internal fanout excess - 1` reduces a 27-gate lower bound to a total charge of at least 28. Bottom-input duplication supplies only a local part of that charge. Cubicity and C4-freeness constrain direct neighborhood sharing, but do not yet control higher-degree Boolean intermediates or sharing after filtering. Assuming a same-size single-level normalization would hide exactly that missing step.

No primary source read here establishes the desired cubic bipartite `2n-1` theorem. No smaller graph in that exact class exists to serve as an easier test. The cofactor computations give useful exact upper bounds and potential SAT pruning, but they do not justify a Lean refutation or a new reduction. End this initial route without more detached helper development; revisit only if a concrete additional deletion or global charge is proved.
