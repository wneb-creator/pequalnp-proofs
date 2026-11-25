# L-meta-2962: mathematical obstruction and next-pilot handoff

No general charging proof or counterexample was found. The obstacle is
an unrestricted monotone Boolean circuit lower bound; it is not merely a missing
finite-graph or Lean-library lemma. This assessment does not assert that no short
new proof exists, or that the conjecture is false.

## Exact mathematical content

For every nonempty bipartite C4-free graph G, consider the bound

    size(A) >= |E(G)| + tau(G) - 1

for every binary AND/OR circuit A computing the exact edge function fG. This
bound and the posted core-cover inequality are informally equivalent:

* From the size bound, compress the union U of maximal-core cones, OR their
  outputs, and add an optimal star circuit for the residual graph G-D. The
  result computes fG with at most |U|+mc+|E-D|+tau(G-D)-1 gates. The residual-empty
  case uses just the OR of the cores. Cancelling gives the posted inequality.
* Conversely, prune A and append q=F OR x, r=q AND F, where F is its output and
  x any input. The new q accepts singleton x, whereas F is below fG. Thus r is
  a repeated-read core containing the pruned circuit. Append an independent
  canonical live output, leaving this block dead. There is one maximal core,
  D=E, and |U|<=size(A)+2. Apply this to three disjoint copies of A, joined by
  two OR gates. The posted statement implies
  3(|E|+tau(G)) <= 3 size(A)+5, hence size(A)>=|E|+tau(G)-1 by integrality.

Pruning, graph/circuit copying, canonical padding and compression remain to be
formalized. The mathematical cost accounting was independently reviewed. The
ReadK support and wrapper-vector ingredients now have checked partial proofs.

## Why the obvious restrictions do not solve it

Lift fixed point restricts the live output cone only. Arbitrary circuits can sit
inside the dead wrapper above. Even ONE maximal core can therefore contain the
entire hard instance. Proving disjointness between different maximal cores, or
solving shared-cone overlap alone, cannot discharge the unrestricted one-cone
case. Unfolding a DAG into a formula duplicates shared gates and loses the needed
size bound. Splitting repeated input occurrences also creates complete bipartite
blow-ups of edges, which need not remain C4-free.

The two proposed separate charges are sufficient but stronger than the requested
total-gate bound. Exact-function inequalities OR(A)>=|E|-1 and AND(A)>=tau(G)
would imply the two core charges by completing missing edges with star circuits.
The total-gate conjecture could still hold even if either separate charge fails.
A free-OR or free-AND counterexample is therefore only an auxiliary result unless
its expanded TOTAL gate count also beats |E|+tau(G)-1.

## Exact failure points of simple charging

* **First edge creation does not charge ANDs correctly.** The function
  ((a OR b) AND (c OR d)) AND (a OR c) is the P4 edge function ac OR ad OR bc.
  Its two disjoint accepted edges are born at the same first AND. The later
  AND removes the bad pair bd without first creating any accepted edge. Any
  matching-to-AND injection must include filters and prove a global Hall
  condition; assigning each edge its first birth gate is insufficient.
* **The forest OR argument misses exactly the cycle rank.** The informal leaf-deletion argument for a monotone h rejecting all singleton
  inputs gives OR(h)>=rank(D)-1, where D is its accepted-pair graph and
  rank(D)=|V(D)|-components(D). This argument has not been formalized in Lean. The desired bound
  is OR(h)>=|D|-1. Thus it must additionally charge beta(D)=|D|-rank(D), not just
  the input leaves or connected components. This deficit is two for theta(3,3,3)
  and eight for Fano. Replacing a shared bottom OR x OR y globally by either
  operand can lose an arbitrarily large star of accepted edges; C4-freeness
  does not itself bound those separate neighborhoods.
* **Pair-only or independent-transversal invariants discard crucial negatives.**
  There are small monotone CNFs that accept a large matching on pair inputs and
  reject the entire left and right sides, yet accept larger independent sets.
  The six-code example in the research notes accepts an independent triple.
  Every candidate must reject ALL maximal independent sets, or prove BelowF by
  another exact argument. Silently deleting nonedge/higher terms is invalid.
* **Free-gate normalization is not total-size normalization.** Factoring common
  source sets from AND operands is complete when OR gates are free; its dual
  is complete when AND gates are free. Both may increase the other gate count.
  Neither gives a bilinear, read-once, or arithmetic circuit preserving total cost.

## Recommended continuation

The most direct refutation target is an exact circuit saving ONE gate below the
canonical star bound: 11 gates for theta(3,3,3), or 26 for Fano. Three-copy
amplification then guarantees a posted-statement counterexample. Direct searches
for a very small core can miss such one-gate savings before amplification.
If a candidate appears, independently check every truth assignment for these
small graphs, then prioritize checked copying/pruning/padding lemmas for the
larger amplified witness. Otherwise a proof needs a new global semantic charge
for filtering independent sets under arbitrary reuse; none was established here.

Finite SAT exclusions and millions of heuristic evaluations are useful scope
checks, not Lean proofs. In particular, the final normalized Fano/six-AND and
variable-graph six-by-six/five-AND runs were interrupted after the environment
reconnect and have NO VERDICT; do not reinterpret them as UNSAT or timeouts.

Primary sources checked during this job distinguish unrestricted Boolean
circuits from single-level, bilinear, multilinear and arithmetic models. Jukna's
[2006 author paper](https://web.vu.lt/mif/s.jukna/ftp/single1.pdf), read 2026-11-25,
provides historical context; its single-level lower bounds and nonbipartite
counterexamples do not settle this class. The current literature status of the
exact unrestricted bound remains UNVERIFIED: no authoritative current theorem
establishing or refuting it was located. The equivalence above, not an assertion
about present-day open-problem status, is the concrete obstruction established.
