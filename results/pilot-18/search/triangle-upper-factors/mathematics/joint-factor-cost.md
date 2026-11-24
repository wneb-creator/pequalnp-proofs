# Joint full-cover factor charge

Status: mathematical derivation for independent review, not a Lean theorem or
an implemented SAT cut. No solver or active CNF is changed.

Consider a binary prefix with m gates, all ANDs clean for ambient graph G and
productive: both operands have nonempty singleton support. Its chosen outputs
W_0,...,W_{k-1} are proper-support full-cover factors, whose product is F_G and
whose family is minimal. Hence every proper subproduct is dirty. Assume k>=3.
Write S_i for their supports. They are incomparable, and W_i=F_G OR OR(S_i).
No chosen output is a raw input or constant.

Fix i and suppose G minus S_i has an edge. Put

    L_i = |S_i| + |E(G minus S_i)| + cover(G minus S_i) - 1.

For j!=i let C_j be the common-neighbor set of S_j. Among the other outputs,
count z with C_j empty. Also count d distinct vertices v in S_i for which at
least one other output has C_j={v}. Then

    m >= L_i + z + d.

This claim needs the productive prefix invariant, not global minimality of
the circuit. It permits repeated operands, dead gates, constants and padding.
For a C4-free simple graph, every support of size at least2 has at most one
common neighbor. The existing full-cover bound rules out supports of size0/1
in a17-gate prefix here, so the formula covers every relevant chosen factor.

## First clean AND below a chosen factor

Suppose W_j is an ancestor of W_i. Its support is not contained in S_i, so a
path from it to W_i cannot consist entirely of OR gates. Choose the first AND
q on such a path. One operand A is reached from W_j through OR gates only.
Thus A covers every edge and its singleton support contains S_j. Let B be the
other operand. Cleanliness gives cross(support A,support B) subset E(G), so
support B is contained in C_j. Productivity makes support B nonempty.

In particular C_j cannot be empty. If C_j={v}, then support B={v}.

If v belongs to S_i, restrict S_i to zero. The restricted B is now false on
every independent input of G minus S_i. On every edge row of that residual
graph, restricted A is true; hence q and B have exactly the same edge values.
Replacing q by B therefore preserves the entire independent boundary and
every residual edge value. It preserves cleanliness of all subsequent gates
and deletes one AND. It is unnecessary to preserve values on larger positive
inputs. The concrete partial-edge lower bound requires only accepted target
edges, empty output support and ambient cleanliness, all of which remain.

## Distinct owners give distinct removed ANDs

Choose one ancestor output for each distinct v that has at least one such
ancestor. Their selected first ANDs are distinct. If two first-AND paths enter
the same operand of q, the other operand would have support contained in
{v} intersect {w}, empty for v!=w, contrary to productivity. If they enter
opposite operands, q dominates W_j AND W_l. That pair is dirty because it is
a proper subfamily of a minimal family of size at least3. This contradicts
cleanliness of q. This argument also handles shared paths and fan-out.

## Gate count, including outputs outside the cone

Prune to the ancestor cone of W_i, with M gates. Let t be the number of
distinct owners v in S_i represented by an ancestor output. The previous
argument supplies t distinct AND gates that can be removed on restriction.

Independently, the standard pure-support OR-DAG component count removes at
least |S_i| OR gates on this same restriction: pure-S components contain all
|S_i| input sources; each pure OR merges at most one component; every remaining
component has a distinct boundary OR that becomes an alias. The output is not
pure-S because the residual graph has an edge. These gates are ORs, so they
are distinct from the t counted ANDs. If simplification already removed one
of the counted ANDs, its deletion is already charged; otherwise replace it
by B as above. Replacements preserve the residual boundary, so they can be
performed sequentially, including when their dependency cones overlap.

There is thus a clean circuit accepting every residual edge, with empty
singleton support and at most M-|S_i|-t gates. Applying the actual-circuit
partial-edge theorem gives M >= L_i+t.

Every output with empty C_j is outside the cone. Each of the d-t distinct
owner groups with no ancestor representative contributes at least one
distinct output gate outside the cone. These gates are distinct from those
z empty-common-neighbor outputs. Thus m-M >= z+d-t. Adding gives the claim.

## Concrete family from the orchestrator

Take S_1=N(1)={4,8}, S_4=N(4)={1,8,10}, S_8=N(8)={1,4,5,9}.
Their common-neighbor sets are {1},{4},{8}; their individual bounds are
16,13,12. For distinguished S_1, the two other owners4,8 lie in S_1 and are
distinct, so z=0,d=2. Consequently every productive clean prefix producing
these three full-cover factors has at least16+2=18 gates.

The support family really does cover all independent inputs and passes the
individual bounds, as checked separately. The new obstruction is joint: it
does not contradict those checks and does not prove AAAA exhaustion.

## Limits

The minimal-factor premise and productivity must be preserved when applying
this to a normalized search. It is not a cut on arbitrary dirty suffix wires.
An edgeless residual needs a separate argument and is excluded above. Owners
outside S_i are not charged. Several factors with the same owner contribute
only one owner charge here. No unnamed structural or solver result is used.
