# Full-edge prefix support cost: mathematical review

Verdict: PASS. For every proper support S of a clean-prefix wire that is true
on all sixteen edge rows, a prefix of m gates producing that wire satisfies

    m >= |S| + |E(G[V minus S])| + tau(G[V minus S]) - 1.

Here tau is minimum vertex-cover cardinality. Full support is exempt because
the augmented model has free TRUE. The argument applies to a clean prefix;
it is not a statement about wires after junk ANDs have appeared.

## Identifying the prefix wire function

Write F for the graph edge function and W for the selected prefix wire.
Monotonicity and the sixteen positive edge rows imply F <= W. On every nonempty
independent input, the clean-prefix support lemma gives W = OR(S). Because S
is proper, some singleton input is false for W; monotonicity then makes W false
at the empty input as well. Consequently, on every input,

    W = F OR OR(S).

Setting all variables in S to zero therefore gives exactly the edge function
of H = G[V minus S]. Every retained AND stays clean for H: a true restricted
AND was a true original AND, hence an original edge was present, and that edge
cannot meet the zeroed set S. Constant propagation and alias deletion preserve
the functions of the gates that remain. Free constants can subsequently be
eliminated without adding gates whenever the output is nonconstant.

## At least |S| OR gates disappear when H has an edge

Consider the OR-only ancestry of W: start at W and follow predecessor edges
through OR gates, stopping at input/constant wires or AND outputs. A clean AND
has empty singleton support. Thus each vertex of S is present as an input source
in this OR ancestry. No input outside S can occur there, since an OR-only path
would put that input in the output's support. Free TRUE cannot occur either,
because it would make the support full. Free FALSE is harmless.

Call an OR-ancestry wire pure-S if its ancestry consists entirely of variables
from S and OR gates. Free FALSE may either be included as an additional zero
source or treated as a frontier source; the lower bound is unchanged. Let k=|S|,
let a count the pure-S OR gates, and let b count the non-pure OR gates with a
pure-S operand. Both operands of a boundary gate cannot be pure-S, since then
that gate would also be pure-S.

The undirected graph of the k S-input nodes and a pure-S OR nodes has at least
k-a connected components. Indeed, in topological order, a new binary OR node
can merge at most two already existing components, decreasing the component
count by at most one. Repeated operands and shared subcircuits do not increase
that decrease. Extra zero sources only strengthen the inequality.

Every such component reaches a boundary OR: all nodes under consideration are
ancestors of W, and W is not pure-S because its restriction is the nonzero edge
function of H. Distinct components require distinct boundary gates. A boundary
OR has exactly one pure-S operand, so it cannot receive exits from two pure-S
components. Therefore b >= k-a and a+b >= k.

When S is set to zero, all a pure-S OR gates become FALSE. Each of the b boundary
OR gates becomes an alias of its other operand and can be deleted as well.
These are a+b distinct original gates. The restricted circuit for H thus has
at most m-k gates. Further simplification can only reduce this number.

No assumption of a tree, unshared inputs, minimality, or distinct operands is
used. The argument counts nodes/components of the actual binary DAG.

## Applying the clean-circuit theorem

H is C4-free as an induced subgraph of G. For nonempty H, L-meta-1407 gives

    |E(H)| + tau(H) <= (m-k) + 1,

which rearranges to the claimed bound. The resulting circuit may be relabeled
to the |V minus S| remaining inputs; this does not change its gate count.

If H is edgeless, every edge of G meets S and W=OR(S). A binary circuit depending
on k distinct inputs requires at least k-1 gates: its output dependency DAG
can have at most one more distinct input source than binary gates. Free
constants do not supply any of these input dependencies. This proves the same
formula in the edgeless case, since |E(H)|=tau(H)=0.

For the present nonempty graph, an edgeless residual requires nonempty S, so
the k-1 expression has no negative exceptional case. S=all eleven vertices
must remain unrestricted: free TRUE is a zero-gate counterexample to applying
the k-1 bound at full support.

## Zero and singleton consequences

For S empty, the bound is 16+7-1=22. For S={v}, every H=G-v has cover number
at least six, and has 16-deg(v) edges. Thus the original prefix needs at least
22-deg(v) gates, which is at least 18 because the maximum degree is four.
Therefore none of the seventeen prefix gate outputs can cover all edges with
empty or singleton support. Free TRUE has support eleven and is allowed.

The explicit singleton restriction proof removes one OR gate, leaving at most
16 gates for H, whereas the clean H lower bound is at least 17. This is exactly
the k=1 instance of the general component argument.

## Table formula and scope of review

For this eleven-vertex graph, tau(H)=|V(H)|-alpha(H), so the bound is

    10 + |E(H)| - alpha(H)

for every proper S. The proposed table uses zero at full support as an
unrestricted sentinel, which is correct. The comparison for prefix gate g is
against g+1, the total number of gates available through that output.

The companion support-cost-math-review.json independently checks all 2048 table
entries and reports a finite structural check of the component argument. The
table review does not certify any particular CNF minimization or solver result;
the implementation has its separate encoding review. This is a mathematical
proof review, not a Lean formalization.
