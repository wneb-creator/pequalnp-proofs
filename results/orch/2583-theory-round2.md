# L-meta-2583 theory round 2: shared mixed linear filters

This is a restricted structural result, not the unrestricted circuit budget.

## Setting

Let G be the bipartite incidence graph, with no four-cycle. Write X(P) for the OR of point inputs in P, Y(R) for the OR of line inputs in R. Consider blocks

    H_i = X(P_i) AND Y(R_i) AND Q,
    Q = X(S) OR Y(T),

where the same linear function Q is shared, and every H_i implies the target edge function. The two pure-side factors are a genuine restriction. A chain of two AND gates with three OR-only leaf operands has this form after choosing the factors that vanish on the all-points and all-lines assignments. An OR combining the inner AND with another expression would fall outside this template. More general AND DAGs need not have this form.

The pair inputs accepted by H_i are exactly

    D_i = {(p,l) in P_i x R_i : p in S or l in T}.

If one of P_i intersect S and R_i intersect T is empty, D_i is a single star or empty under the no-four-cycle condition. Focus on blocks with both intersections nonempty and both |P_i|, |R_i| at least two.

## Double-star shape

Choose p_i in P_i intersect S and l_i in R_i intersect T. Every p in P_i is incident with l_i, because the pair (p,l_i) satisfies all three factors. Every l in R_i is incident with p_i. Therefore P_i intersect S has at most one point, and R_i intersect T has at most one line; otherwise two points and two lines would form a four-cycle. They are exactly {p_i} and {l_i}. Thus D_i is the double star centered at the incident pair (p_i,l_i).

Choose an off-center p* in P_i minus {p_i} and l* in R_i minus {l_i}. The three edges p_i-l_i, p_i-l*, p*-l_i force p*-l* to be a nonedge.

For every s in S, the input {s,p*,l*} satisfies H_i. As H_i implies G's edge function, and p*-l* is not an edge, s must be incident with l*. The same argument on {p*,l*,t}, for t in T, forces p* incident with every t. Hence

    S is contained in the neighborhood of l*,
    T is contained in the neighborhood of p*,
    p* and l* are nonincident.

This implication uses the full function inequality H_i <= F, not just correctness on pair inputs. It is precisely the constraint missed by a pair-only circuit search.

## Sharing becomes a matching

Assume |S| >= 2 and |T| >= 2. The line l* is uniquely determined by any two points in S, independent of the block. Dually p* is uniquely determined by any two lines in T. Each block therefore has

    P_i = {p_i,p*}, R_i = {l_i,l*},

with the same off-center pair (p*,l*) for every block.

The edges between S and T form a matching: if p in S has two neighbors t,t' in T, p and p* share both t,t'; if t in T has two neighbors s,s' in S, s and s' share t and l*. Either contradicts absence of a four-cycle because p*-l* is a nonedge. In particular the number of distinct center pairs is at most min(|S|,|T|). Blocks with identical center pairs have identical P_i,R_i,Q and can be deduplicated semantically.

The 59-line candidate 2583_shared_filter.lean formalizes the missing-corner fact and the matching edge-cardinality bound for arbitrary subsets of these opposite neighborhoods. Its assumptions use only the posted unique-line axiom; the dual uniqueness required above follows from it.

## Restricted gate accounting

For t distinct nontrivial blocks under these assumptions, their pair-edge union consists exactly of the t center edges p_i-l_i and the arms p_i-l*, p*-l_i. A read1 star construction costs 4t gates: for each i compute p_i AND (l_i OR l*) (2t gates), compute p* AND OR_i l_i (t gates), then OR these t+1 terms (t gates).

The original isolated template already has t distinct OR gates producing {p_i,p*}, t producing {l_i,l*}, and 2t AND gates inside its blocks, before counting Q and the output ORs. Thus its complete isolated gate count is at least 4t, and the replacement does not increase it.

This is NOT yet a valid global circuit transformation. If these P_i or R_i OR gates have users outside the replaced group, they cannot simply be deleted. Likewise a shared Q cone cannot be charged independently to every group. The semantic matching result is sound, but arbitrary overlap of operand cones and deeper nonlinear factors remains the unresolved accounting problem. No unrestricted gate-budget claim is made.

## Other route assessed

For a linear target OR_S, if an AND gate computes it, both children accept each singleton in S and one child rejects the all-outside-S input. That child already computes OR_S, so the final AND can be bypassed. This explains why linear-output constructions are more constrained. It does not eliminate internal AND gates shared among different outputs, nor transfer directly to a quadratic incidence target. No theorem claiming that transfer was used.

UTC: 2026-11-25T15:01:56.566506+00:00

UTC: 2026-11-25T15:02:39.824263+00:00
Source: results/orch/lemmas/2583_shared_filter.lean
SHA256: 0ed8fcd8f87710b3a98b3562ebfd4360c11806fb515605ff33bb3f3ba000fea1
Lines: 59
Lean exit: 0
Command: PATH=/tmp/oec/pequalnp-pilot-98/toolchain/bin:$PATH PEQUALNP_REAL_LAKE=/tmp/oec/pequalnp-pilot-98/toolchain/bin/lake PEQUALNP_HOME=/tmp/oec/pequalnp-pilot-98/build-home MATHLIB_CACHE_DIR=/tmp/oec/pequalnp-pilot-98/mathlib-cache LAKE_ARTIFACT_CACHE=false ../tools/bin/lake env lean -j 1 -M 2048 /workspace/pequalnp-proofs/results/orch/lemmas/2583_shared_filter.lean
Stdout: empty
Stderr: empty
Scope: three incidence corners exclude the fourth, and edges between subsets of opposite neighborhoods of a nonincident pair form a matching (cardinality bound). No arbitrary Circuit gate-budget theorem.

## UNCHECKED linear-filter drafts at lease termination

UTC: 2026-11-25T15:06:34.357926+00:00
STATUS: UNCHECKED DRAFTS
Reason: root reported lease ended before any build was launched. No Lean check was attempted for either draft.
results/orch/lemmas/2583_linear_filter.lean
SHA256: be755679f00ff0ae00d49a47d853eb96bd324114686dbf67d551889e440a8023
Lines: 94
results/orch/lemmas/2583_linear_filter_plane.lean
SHA256: f46c7397f9d32b2140a98685d107caa9829de30b163b1e3c86e5cdc5c6ef0547
Lines: 35
The first file is intended as a standalone generic lemma bundle. The second is a namespace fragment requiring the main file and first bundle. The previously checked 2583_shared_filter.lean is separate and remains valid.
