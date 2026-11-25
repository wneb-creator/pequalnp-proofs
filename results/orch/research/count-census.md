## Split AND/OR count census

Scanned 2733 candidate Outside files, extracting 2731 final theorem statements (the two root partial files were excluded). Full candidate metadata is retained in gate-count-final-statements.json; focused candidate sets are in gate-count-lowerbound-candidates.json, abstract-and-count.json, and or-count-rhs.json. This was a local source census, not a new Lean build.

No theorem found deriving ANDcount >= N and ORcount >= N*(q+1)-1 for every incidence-plane circuit from actual correctness alone.

* L_meta_1778:429 gives the strongest directly applicable general plane OR lower bound located: 2*q^2+1 <= ORcount. Its hypotheses require incident-pair acceptance and rejection of independent inputs with at most q active lines; actual correctness suffices. L_meta_3308:429 repeats this for q >= 200.
* L_meta_599:1264 and L_meta_4837:1263 prove |E| <= ORcount+1 only under every induced subgraph having at most its vertex count, as well as no C4. The plane graph violates the induced-subgraph hypothesis already on all 2N vertices, since N(q+1)>2N.
* L_meta_217:7349 and L_meta_2399:7381 prove ANDcount >= minimum vertex cover only for a cover lower bound t <= 5. Plane N >= 7 is outside this range.
* L_meta_1406:289 proves cover <= ANDcount when every AND gate is below the graph function, exactly an unavailable normal-form condition. L_meta_1407 and L_meta_7848 give the resulting total-size bound under the same condition.
* Explicit Fano graph ANDcount >= 7: L_meta_634/L_meta_910. Explicit PG(2,3) ANDcount >= 13: L_meta_1898:7314, or the abstract set-DAG equivalent L_meta_8750:7395. These are fixed labeled incidences, not an arbitrary plane classification theorem.
* PG(2,4) L_meta_7025:298 assumes ANDcount <= 10 and concludes 21 <= ANDcount; it only excludes counts <=10. L_meta_7838 requires every direct variable pair at every AND to be a graph edge and disjoint sides, so it is not an unrestricted lower bound.
* L_meta_7824 gives 52 <= AndCountCircuit.size+1 for 52 negative and four positive tests, but additionally assumes EVERY gate is true on EACH of the four positive tests. This hypothesis is not implied by output correctness, so dual converter L8043 does not automatically yield 51 OR gates.
* L_meta_529 proves unrestricted multiple-output OR-family complexity sum(|S_i|-1) for pairwise intersections <=1. Extracting all line-neighborhood outputs from one incidence-function circuit is still missing; merely dualizing or setting one point input true does not preserve the gate budget jointly.

Potential false-friend: L_meta_1006 refutes a C4-free graph minimum AND count statement for maximal-independent-boundary tests. The graph contains disjoint triangles and is not bipartite; the theorem does not even claim full graph-function correctness. It is not a refutation of the held gap.
