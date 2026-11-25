# L-meta-3566 structural assessment

Updated 2026-11-25 21:55 UTC; proof_route, independent of desk ownership.

## Checked mathematical scope

The compiled GraphPeel/Upper/PeelGlue/Converse artifacts show that the posted universal peeling claim is equivalent to the exact lower bound C.size >= |E(G)| + tau(G) - 1 for every nonempty bipartite C4-free graph, in the posted exact binary backward AND/OR model. The converse is an implication with the posted statement as an explicit premise. It does not prove that premise. A single graph/circuit below this bound would refute the posted statement without needing lower bounds for its vertex cuts.

The graph-only issues are resolved: a positive-degree vertex can leave a nonempty residual graph; deleting its incident edges changes edge count by its degree; minimum vertex-cover size changes by zero or one; and the bonus condition exactly detects the latter case. The generic restriction artifact saves one gate for any positive-degree vertex with a nonempty residual graph. Saving its entire degree is the unresolved circuit statement.

## Library census

Existing accepted clean-AND accounting (L-meta-7241, and fresh L-meta-6232) proves the required bound when each relevant AND gate accepts only graph edges on pair inputs. TopForm normalization (1501/5779) preserves the number of dirty AND gates. The one-junk exclusions (3760/8725) and the unique-edge-ownership elimination (8305) do not handle two or more shared dirty AND gates. Their use as a generic cleaner would be circular.

L-meta-217 gives a genuine additional necessary condition: every C4-free graph function with vertex-cover number at least t, for t <= 5, needs at least t AND gates. This was passed to finite_search as an AND-cardinality constraint. It does not supply the missing OR-gate lower bound. L-meta-910 supplies a stronger fixed Heawood AND-count condition.

The upstream refresh added 1,372 Outside files. A complete final-type census found no new generic theorem closing the gap. Its four generic candidates were conditional R_meta reductions. The low-ID proof6232 retains a clean-AND hypothesis;5857 is a fixed nonbipartite case;9728 proves the exact 26-gate lower bound for Heawood with one edge removed. Details: upstream-type-scan.log, upstream-all-generic-types.json and upstream-final-types.json.

## Why the tempting transfers fail

Taking all single-vertex cofactors of one circuit gives neighborhood OR functions, but naively doing so duplicates circuit gates. Shared dirty ANDs can have overlapping cofactor contributions. Therefore the exact lower bound for a multioutput family of ORs whose supports intersect in at most one variable does not imply this single-output result with its desired constant.

Likewise, the classical single-level separation constructions read in Jukna use saturated graphs with cliques inside bipartition classes. They are not bipartite C4-free counterexamples. Graph representation only on edge/nonedge pairs is weaker than computing the full graph function; this distinction invalidates several apparent counterexamples. Direct audit of L-meta-1006's AND-count witness found39 false negatives over2048 assignments, including6 edges; it has10 quadratic and14 cubic minimal true sets, so it cannot serve as a full graph-function witness.

## Primary sources actually read

Jukna, Lower Bounds for Tropical Circuits and Dynamic Programs, Remark10, PDF page19: https://arxiv.org/pdf/1406.3065 . Read2026-11-25. It explicitly distinguishes lower bounds for a matrix's multioutput Boolean sums from its single-output bilinear function, and records the latter C4-free edge-count bound as unavailable in the unrestricted Boolean circuit model at the paper's date. This is historical evidence only; the present-day status is UNVERIFIED because no complete modern literature review is possible here.

Blum, On the Approximation Method and the P versus NP Problem, section3, PDF pages12-14: https://eccc.weizmann.ac.il/report/2024/179/download/ . Read2026-11-25. The survey confirms that AND gates do not improve optimal monotone circuits for pairwise-intersection-at-most-one Boolean-sum families, while explicitly discussing the importance of multiple outputs to those counting arguments. This confirms the model distinction, not a proof of the posted claim.

Jukna, Disproving the Single Level Conjecture: https://web.vu.lt/mif/s.jukna/ftp/single1.pdf . Read2026-11-25. The useful separation is via saturation and does not directly preserve bipartiteness.

## Precise remaining obstruction

We need a size-preserving clean-AND normalization, or a direct accounting argument charging all the extra Ustar edges created through multiple shared dirty AND gates without double-counting shared OR work. Existing local absorption identities lose any saving when their operands serve several consumers. The finite SAT searches target this obstruction by allowing at least two dirty AND gates and checking every assignment after decoding; no verified circuit beating the bound has been obtained. There is currently no full proof, no refutation, and no justified route from the checked conditional artifacts to the posted endpoint.
