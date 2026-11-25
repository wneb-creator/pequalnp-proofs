# A monotone separator for flags and punctured double stars

This argument bounds the information supplied by one family of maximal negatives in L-meta-2583. It is a mathematical construction on coordinate planes. The construction and its asymptotic size have not been checked in Lean.

## The negative test family

Write a flag as an incident point and line `(p,l)`. Use the assignment `Z(p,l)` that selects the points of `l` except `p` and the lines through `p` except `l`. A selected point `r` and selected line `m` cannot be incident because then `p,r` would lie on the two distinct lines `l,m`. This independent assignment is maximal. Every point outside `l` lies on its selected line joining it to `p`, and each line outside the pencil of `p` meets `l` at a selected point. Both omitted central vertices have selected neighbors. There are `N(q+1)` distinct test assignments for `q ≥ 2`, since their selected points determine `l` and the unique omitted point on it determines `p`.

In the associated monotone Karchmer–Wigderson game, Alice has a flag and Bob has a punctured double star. If Bob has `Z(p,l)` and Alice has `(p,m)` with `m ≠ l`, only `p` is a permitted answer. If Alice has `(r,l)` with `r ≠ p`, only `l` is permitted. The full collection of these forced answers, including every other allowed Alice–Bob flag pair, admits the circuit size below.

## A common partition for all these tests

Take `PG(2,q)` for any odd prime `q`, with `N=q²+q+1`. Represent points and line covectors by normalized homogeneous triples in `F_q³`. Incidence means that the dot product is zero. Partition affine points into the `q` sets

```
A_t = { [a : a²+t : 1] | a ∈ F_q }.
```

Make each of the `q+1` points at infinity a singleton block. Each line meets each block in at most two points. For a line covector `[u:v:w]`, intersections with `A_t` are roots of `v a² + u a + vt + w`. This polynomial is nonzero unless all three covector entries vanish. There are `2q+1` blocks. Apply the same partition to normalized homogeneous triples in the dual plane to obtain `2q+1` line blocks. Each pencil meets each line block in at most two lines. In particular, every `Z(p,l)` selects at most two vertices per point block and at most two per line block.

## Circuit construction

Encode each normalized triple with `d = 3 ceil(log₂ q)` bits. For each vertex block and each bit position `j`, form two buckets according to bit `j`. For each bucket precompute its presence bit, the OR of its selected input vertices. For each coordinate bit position `i`, compute two rails by OR over the bucket's selected vertices whose `i`-th bit is respectively zero or one. Any selected vertex contributes its own entire valid code to its bucket. A nonempty singleton bucket gives exactly one valid code.

For each point block `A` and line block `B`, compute the following predicate.

1. Choose a bit position `j` to split `A` and a bit position `k` to split `B`.
2. For each of the four bucket pairs apply a two-rail incidence circuit to their coordinate rails, and AND its positive output with both bucket-presence bits. OR the four answers.
3. AND these answers over all `d²` choices of `(j,k)`.

The circuit output is the OR over block pairs. One ordinary bounded-fanin Boolean circuit tests whether two `O(log q)`-bit triples have dot product zero modulo `q` in `O(log² q)` gates. Schoolbook binary multiplication, three-product addition, and bitwise long division by the fixed modulus suffice. The two-rail translation replaces an AND or an OR by its positive gate and its De Morgan dual. A NOT exchanges rails. This uses only monotone AND and OR gates. Its answer is exact on consistent code pairs. If the rails contain all the rails of a consistent incident code pair, monotonicity makes the positive result true. Hardwired constants and empty ORs can be propagated before counting to obtain a constant-free binary DAG, since the final output takes both Boolean values.

Every true incidence `(r,m)` survives all bit choices in its own block pair on any input containing `r,m`. Each pertinent bucket contains the rails of its selected vertex. Therefore the constructed circuit accepts all true inputs to the incidence function.

On any independent input selecting at most two vertices per block on both sides, fix a block pair. Some bit separates the selected points of its point block, since distinct point codes differ. A singleton or empty block allows any bit. Choose a separating bit independently for its line block. Every bucket on these two splits now has at most one selected vertex. Empty buckets are rejected by their presence checks, and the incidence circuit rejects all remaining pairs by independence. The AND over split choices rejects this block pair. This applies to every block pair and to every `Z(p,l)`.

The shared bucket computations cost `O(N d²)` binary OR gates. For each of `(2q+1)²` block pairs there are `d²` pairs of splits and four incidence tests per split pair. Their gate count together with the outer OR and AND trees is `O(q² log⁴ q)`. Since this is `o(q³)`, along sufficiently large primes it is strictly smaller than `N(q+2)-1`. The full lower bound in the posted gap would need other independent assignments in addition to punctured double stars if it is to hold for all orders.

## An explicit false positive of this separator

For `q=7` choose `A_0` and select the six points `[a:a²:1]`, `a=1,...,6`. Select only the line `y=0`, the tangent at `a=0`. This assignment is independent. Nevertheless the circuit accepts it. Write the affine coordinates with three bits each. For every split position in the affine code, use the bucket matching the code of `[0:0:1]`. For the three positions in the first coordinate, the sets of available `a` values are respectively `{2,4,6}`, `{1,4,5}`, `{1,2,3}`. For the three positions in the second coordinate they are `{2,3,4,5}`, `{1,2,5,6}`, `{1,3,4,6}`. In each case the bitwise AND of both affine coordinates over the bucket is zero, supplying the zero rail for every affine coordinate bit of `[0:0:1]`. A split on the constant third coordinate keeps all six points in the matching bucket. The line bucket containing `y=0` has its exact code for any split. Monotonicity therefore accepts every split pair using the incident synthetic point `[0:0:1]` and the actual line `y=0`.

This example checks the distinction between the test-family separator and an exact circuit. The asymptotic gate comparison concerns sufficiently large primes and makes no size claim at order seven.
