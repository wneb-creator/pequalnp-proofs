# L-meta-2590 partial lemma work

The three existing reductions are R_meta_2590_1, R_meta_2590_491, and R_meta_2590_932. The last uses novelty and semantic exclusions to split into edge-OR, nonedge-OR, and edge-AND; its edge-AND branch excludes all raw-input OR wires.

Existing normalization: L_meta_4342 gives a size-nonincreasing AO2 circuit from any Monotone2 circuit false on the all-false input (193 lines). L_meta_6276 proves least nonconstant Monotone2 circuits are AO2. These already handle constants, unary gates, and invalid wire reads; no normalization loophole should be assumed.

## Checked bridges

`NineMonoFloorSnippet.lean` contains finite required-input witnesses and `nineMonoFloorOfCert`: Impossible false graph15 inputs.toFinset implies Lower false inputs graph16. Test `/tmp/oec/pequalnp-pilot-103/NineMonoFloorCheck.lean` imported the preserved Binary17.olean and compiled exit0 with empty `2590-nine-mono-floor.stdout/.stderr`. No new axioms are used; the certificate is an explicit theorem parameter. L_meta_4332.monoRoot supplies it, and lower_bound is integrating that independently checked certificate.

`EdgeAnd.lean` compiled exit0 with empty `2590-edgeand-first.stdout/.stderr`. It imports only Mathlib.Data.Bool.Basic and proves a generic fact: for distinctu,v and any monotone Boolean wireh, (x_u AND x_v) AND h either equals x_u AND x_v or rejects EVERY input supported on two vertices. Consequently a fresh wire that accepts some graph edge cannot be an AND gate directly reading a raw edge wire. This is a structural helper for the first-edge-AND reduction, not a full20gate lower bound.

Potential zero-elimination route: the monotone cofactor floor16 means deleting at least4gates after setting some vertexfalse would suffice for20. In an optimal20gate star circuit, cover-center vertices permit4deletions while the remaining vertices permit3. Raw fanout alone misses private OR cones made dead after an AND collapses. No theorem guaranteeing4deletions in an arbitrary least circuit has been established.

Caution: monotonicity alone likely does not allow charging projected duplicate inputs. Identifying endpoints of P7 produces C6, and their apparent optima are both8. This is a proposed obstruction, not a separately machine-checked complexity lower bound here.
