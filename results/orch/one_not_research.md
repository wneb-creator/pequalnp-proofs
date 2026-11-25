# One-NOT Petersen research

Scope: the remaining possibility of 18 AND/OR gates plus one NOT, computing the Petersen edge function. No unrestricted lower bound is proved here.

## Checked endpoint and OR-family lemmas

`lemmas/OneNotEndpoints.lean` compiled with exit 0 and empty stdout/stderr (`/tmp/oec/pequalnp-pilot-104/one-not/endpoints-02.*`). Independent review passed. Its conclusions are:

- A nonconstant monotone function h has h(0)=0 and h(1)=1.
- A target f with f(0)=0 and f(1)=1 cannot be NOT h itself, `(NOT h) AND q`, or `(NOT h) OR q`. This uses only endpoints, and does not require q monotone.
- If `(OR W AND NOT(OR H)) OR OR R = OR S` for every input and S is not contained in R, then H is contained in R and S=W union R.
- The dual form `(OR W OR NOT(OR H)) AND OR R = OR S` forces S contained in R.
- Consequently the first form cannot produce an OR of at least three variables when every available W or R contained in S has cardinality at most one.

These support the proposed six-output OR-family obstruction. If all distinct output supports have size at least two and pairwise intersection at most one, one output cannot be contained in another. With seven binary gates for six distinct outputs, at most one binary gate is not an output. An essential NOT must first feed such an intermediate gate by the endpoint lemma. A triple output downstream of that intermediate is obstructed by the masking identities. The remaining circuit-counting/topological wrapper is not formalized here; arbitrary Petersen circuits are not known to reduce to this architecture.

Correction to an initial shortcut: the NOT source need not initially be a primary input; it could be an already-computed OR-pair output. The masking identity forces it to have singleton support only in the productive case where the other final operand R is a primary input.

## Stronger essential-cut diamond (hand argument)

Write f(x)=G(x,NOT h(x)), with h and G monotone, and let lo=G(x,0), hi=G(x,1). If both constant replacements fail, choose an edge E with lo(E)=0 and a maximal independent I with hi(I)=1. The existing FewNots proof can be strengthened to retain these strict cofactor values; it currently states only h(E)=0 and h(I)=1.

For K=E intersection I and J=E union I, monotonicity and the cut equation force:

| point | K | E | I | J |
|---|---:|---:|---:|---:|
| h | 0 | 0 | 1 | 1 |
| f | 0 | 1 | 0 | 1 |
| lo | 0 | 0 | 0 | 1 |
| hi | 0 | 1 | 1 | 1 |

Thus opening the NOT wire as a fresh variable yields the majority-of-three function on this diamond: the two diamond coordinates are AND for lo and OR for hi. This is a potentially useful SAT constraint/local structural invariant; no global gate count follows yet. It applies only to essential NOT, so an inessential case must remain separate.

## Failed shortcuts

1. One of the two constant replacements need not compute the monotone target. With h=x and G(x,y,z)=(x AND z) OR (y AND z) OR (x AND y), substituting z=NOT x yields y, whereas z=0 yields x AND y and z=1 yields x OR y. Both constant replacements fail. This four-point identity was checked directly; it does not contradict possible circuit simplification by a different transformation.
2. Charging one extra gate for a duplicate restricted wire is false even in monotone circuits. The four-gate expression `(x AND y) OR (z AND (x OR y))` for majority3 admits a live run starting from [x,x,y,z] (retain y at the first AND). A local exhaustive truth-table enumeration with free constants found no AND/OR circuit of at most three gates for majority3: state counts by depth 0,1,2,3 were 1,7,34,132. **UNVERIFIED by Lean:** the enumeration has no checked completeness wrapper; it is only a warning against this proposed potential, not a submitted theorem.
3. Minimizing over circuits with free negations does not preserve a one-NOT budget. No such transfer is used.

## Existing general elimination results

Primary page read on 2026-11-25: https://pequalnp.com/papers/note-1 (fetched with curl after the web reader failed). Its convention is: “size counts every gate, NOT gates included”. It describes L107 as a disjunction: either some false restriction removes three gates, or some true restriction removes four. For Petersen, the true branch is weak: a vertex-true cofactor is the OR of its three neighbors together with a residual six-cycle function. Therefore the false-branch argument cannot simply be assumed. The nine-vertex total floor16 (L4033) alone only handles a hypothetical false branch up to equality; a one-NOT premium for that cofactor is not currently available.
