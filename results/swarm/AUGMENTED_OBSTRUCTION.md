Independent PG(2,5) augmented-component audit

Verdict: the stated 292-gate construction is an exact counterexample to the intermediate inequality augmented witness components <= AND count. It is not a refutation of L-meta-4970 and is not a size-minimal circuit.

Independent construction and verification

AugmentedObstruction.py independently constructs the 31 projective points and 31 dual projective lines over F5, with incidence given by vanishing dot product. It verifies degree six, 186 edges, and exactly one common neighbor for any distinct same-side vertices. It then constructs the actual binary circuit with backward-pointing input indices.

The verifier maintains each wire's exact minimal monotone DNF. OR takes union of monomial families; AND takes all unions of two monomials; removing supersets preserves the Boolean function. The final irredundant family is exactly the 186 two-variable edge monomials. This proves equality on all inputs by exact symbolic computation; it is not a claim to have enumerated all 2^62 inputs.

Algebra

Let c be the anchor point, let Qc be the disjunction of its six neighbors, and let P be their conjunction. The six mixed clauses c OR h_b give H = c OR P. Hence

    K = H AND Qc = (c AND Qc) OR P.

For each point a, its three pair witnesses have disjunction OR N(a), so

    A_a = a AND (K OR OR N(a)).

The ordinary star term a AND OR N(a) supplies every target edge at a. Every additional term a AND K implies the target function: the c AND Qc part already supplies an anchor edge, and a AND P supplies an edge from a to the unique line in N(a) intersect N(c), or any anchor neighbor when a=c. Thus the disjunction of all A_a equals the target edge function.

Witness and component counts

There are 93 pair-witness OR roots. Exactly three further eligible pure-star OR roots occur at the anchor: the two partial/full Qc joins, and the final anchor R_c, where K is absorbed by Qc. There are 102 pure-OR roots in total; the other six are mixed clauses c OR h_b, whose two variables cannot be neighbors of a common vertex in a bipartite graph.

The verifier classifies every OR gate using its exact minimal DNF, then checks the common neighbors of its support. Consequently, the 96 eligible roots are exhaustive. Their edge-support components are 90 pairs at the other 30 points and one six-edge component at c, totaling 91. Every OR's raw reach has size at most one: the six mixed clauses reach only c because h_b is an AND buffer, while all other OR roots reach no raw input. Raw support therefore adds no component connections. The augmented count is still 91, exceeding 68 AND gates by 23.

Circuit properties and scope

The circuit contains 68 AND and 224 OR gates, total 292. Every gate lies on a syntactic path to the output and is true on at least one target edge-pair input. The only AND gates below the target are the 31 A_a gates; no safe AND lies below another AND. The exact posted AO2, T0, and served-witness conditions all hold.

The semantic bad-OR count, with empty operand singleton support or mixed output singleton support as the bad condition, is 67. This is also below 91-1, but no assertion is made against a joint bound that can charge other OR gates or unused AND capacity.

The full posted conclusion holds using the cover of all 31 points:

    186 + 31 = 217 <= 292 + 1 = 293.

Minimality caveat

There is a concrete simplification to 216 gates. Delete the K/H branch and its extra Qc joins; start every R_a at its first pair witness and join the remaining two witnesses with two ORs. Then remove the now-unneeded line identity buffers. This yields 31 ordinary six-neighbor stars, with 31 AND gates and 185 OR gates. It preserves the target function, AO2, T0, and serving, and its witness components collapse to 31. Removing the buffers alone while retaining the mixed H clauses would violate T0; the combined simplification avoids that issue. Therefore this example does not refute a version restricted to appropriately minimal circuits.

Artifacts

AugmentedObstruction.py is the tracked independent constructor and verifier. Run `python3 results/swarm/AugmentedObstruction.py --output-dir /tmp/oec/pnp-swarm-4970-orch/augmented-recheck` and save complete stdout/stderr separately. The generated independent-pg5-audit.json and independent-pg5-certificate.json are written under --output-dir and are not tracked. They record the summary, geometry, actual gates, minimal DNFs, raw OR supports, eligible roots, and components. This is a symbolic finite audit, not a Lean proof of the full construction.
