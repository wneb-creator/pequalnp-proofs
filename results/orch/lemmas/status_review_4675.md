# L-meta-4675 independent review

The posted theorem assumes a C4-free bipartite edge set, an IsAO2 circuit computing its edge function, and syntactic two-colour count zero. It concludes that some vertex cover S satisfies E.card + S.card <= C.size + 1. The former L-meta-4970 hypothesis supplying a pure-star OR witness for every edge is absent. No proof or refutation has been established. Root stopped all research after an HTTP405 renewal-method error and its required diagnostic retry. That error does not establish that the lease was withdrawn; it is distinct from the five earlier HTTP410 withdrawals.

## Exact model and boundary cases

IsAO2 means AND/OR gates only, exactly two backward operands, with repetitions permitted. There are no NOT or nullary constant gates, but AND[x,x] and OR[x,x] are legal identity gates. IsAO2 does not require a valid output index, every gate to be used, or the output to be the last gate. Correctness for a nonempty graph excludes invalid and raw-input outputs, but those facts require proofs when used. For an empty edge set, the empty cover proves the conclusion immediately, including zero-dimensional cases.

The supplied rectangular C4 condition forbids four distinct incidence edges on two distinct vertices of each colour. It permits isolated vertices, degree-one vertices, disconnected graphs and arbitrary parallel circuit reuse. The conclusion does not require a minimum cover; a refutation needs a proven lower bound for every cover, for example an explicit matching.

The two-colour count follows OR paths only to raw inputs and stops at every AND gate. It does not measure semantic support, singleton support, minterms, output relevance or actual input dependence.

## Invalid shortcuts

Even a correct, live T0 circuit may contain a semantically mixed OR with empty OR-reach. For p=l=1, use gates AND[x,x], AND[y,y], OR[the preceding gates], AND[x,y], then AND[the OR,xy]. The output is xy on all four inputs, every gate is live, and T0 holds because the OR's operands are AND gates. That OR computes x OR y and has both singleton inputs in its semantic support. The saved four-row computational fixture is gap4675/status_review/t0-mixed-or-obstruction.json. This only refutes the semantic-purity shortcut; the posted inequality holds for this five-gate circuit. No least-size claim is made for the example.

Singleton support also need not determine a wire's full function: higher-degree terms can contaminate it. The previously frozen C6 example from the L-meta-1884 investigation demonstrates this distinction, including zero empty-support and residual surplus. No pruning argument may silently replace a singleton-supported wire by its literal.

T0 cannot supply the former per-edge star-witness hypothesis: a matching has only degree-one endpoints, hence no valid two-leaf star for any edge, although its direct edge-AND/OR circuit is T0. PostedEdgeBound and other old witness-dependent lemmas therefore do not apply without a genuinely new bridge or a separate decomposition.

Deleting a gate, bypassing an idempotent AND, or minimizing circuit size may expose raw inputs along OR paths and create two-colour ORs. A normalization must preserve T0 explicitly. Leastness among all AO2 circuits is different from leastness among T0 circuits, and the posted circuit is not assumed least in either class.

## Reusable proved interfaces

The previous EssentialStar/EssentialSupport results give the desired cover inequality for star graphs and small sides, and an essential-input lower bound that also handles disjoint stars or matchings once the corresponding graph/cardinality facts are supplied. Those bounds do not require T0. They do not settle graphs with cyclic sharing.

The checked Shield.main_aux transforms a nonconstant AO2 graph circuit C into an equivalent T0 circuit D with D.size + 4 <= 6*C.size. Consequently, assuming the new posted theorem would yield a cover with E.card + S.card + 3 <= 6*C.size for arbitrary such AO2 circuits. This is a conditional strength transfer, not a proof of the T0 theorem. The earlier append-pair construction and witness-supplying overhead are unnecessary for that conditional implication here.

## Final reviewed components

StarForests is a checked Defs-only partial: the exact cover bound holds when either edge projection is injective, with only FanInTwo and correctness assumptions. This covers one-sided star forests and matchings. Its prefix is exactly the old EssentialStar source through active_bound after namespace/import changes. The actual guard rejects only the missing full posted theorem.

ForestCover is a checked standalone partial for all bipartite forests. It preserves the full L_meta_3525 proof after namespace/method renaming and a narrower Acyclic import, with the previously checked bipartite graph/count conversion and a new minimum-cover wrapper. Its 1812-line source has 23 inherited warning lines and no errors. Acyclicity is stronger than C4-freeness; longer cycles are not covered by this theorem.

SurplusCover, BipartiteGeometry, DegreeTwoCard and CycleClass are four checked modular partials. They derive n+cover.card<=size+1 under the explicit semantic graph hypotheses, verify those hypotheses for C4-free bipartite graphs of minimum degree at least two, and replace n by E.card only when every vertex has degree exactly two. That final class excludes leaves and isolated vertices; it is not automatically a theorem for all graphs of degree at most two. No T0 assumption is needed for these restricted results. The development dependencies are checked but must be inlined for a submission. CycleClassStandalone is an UNCOMPILED assembly and is preserved as text.

The prepared search engine derives a bipartite graph from pair rows, compares all input truth rows, computes C4 obstructions and matching/cover certificates, and counts T0 on the actual output-cone-pruned circuit that it saves. Independent replay checked all 72 prepared source/output controls over 3,321,856 truth rows, including the deliberate dead mixed-OR pruning control; all certificates and nonnegative margins agree. All 173 final preparation-file hashes match. The 18 previously saved cone counts and margins also agree. No long search was launched, and no counterexample or impossibility result is claimed.

Only root contacted the desk. All post-STOP work by this reviewer was read-only preservation validation or writing review metadata; no new Lean compilation, theorem search or solver search was performed.
