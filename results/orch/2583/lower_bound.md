# L-meta-2583 lower-bound investigation

## 2026-11-25, after reassignment from L-meta-2592

The plane hypotheses have no obvious degenerate counterexample. Every line has q+1 points and unique lines join distinct points; with N=q²+q+1 this forces every point to lie on q+1 lines. Existing checked helper `L_meta_1955.lines_through` proves this in lines 6–42; `cover` in lines 58–86 proves any point/line vertex cover has at least N vertices by incidence counting. No Hall theorem is needed.

ReadK is a property of each prime implicant separately: there must be a proof tree using each variable at most once. It does not mean globally read-once circuitry. For incidence functions the prime implicants are the incident point/line pairs.

A Read1 star circuit costs exactly N*(q+2)-1 gates: q OR gates per line, one AND per line, N-1 output OR gates. Existing checked L_meta_7684 constructs the generic edge-cover upper bound E+cover-1. Existing L_meta_4897 gives the matching lower bound for a C4-free bipartite function under Read1, and L_meta_7639 specializes through a perfect matching. Thus the posted normalization is equivalent, under these plane hypotheses, to the unrestricted exact monotone lower bound N*(q+2)-1 ≤ C.size. This is the real obstacle; the existing Read1 theorems do not already prove it.

## q=2

The counterexample agent located `L_meta_7997_aux.ao27` (line 9428), also L_meta_7945: arbitrary AO2 circuits for the cyclic Fano incidence function have at least 27 gates, without a Read1 hypothesis. Consequently AO26 counterexample search for Fano is impossible. I inspected the proof: the source develops binary DAG fanout surplus, eligible/ineligible input labels, canonical independent-set orbits, then eliminates fourteen finite configurations. It is a substantial 9400-line finite proof, not a uniform q argument. General arbitrary q=2 incidence still requires Fano isomorphism if this theorem is used directly.

## Exact-size repair direction

L_meta_8933 defines a dirty gate as an AND gate that is not BelowF. A bad edge is a prime incident pair on which the output has no Read1 proof. If every dirty AND gate is true on at most one bad undirected edge, replacing each dirty AND by its selected edge preserves correctness and makes every AND BelowF. The replacement keeps every gate index and exact circuit size. It does not directly prove the repaired circuit Read1; instead graph_budget proves E+vertex-cover ≤ C.size+1, after which the standard Read1 construction can be used.

A possible stronger route would be a path-preserving selection of one edge at each dirty gate, but a simple matching from bad edges to dirty gates is NOT sufficient: an accepting proof may need several dirty gates, and all selected edges along that proof must be compatible. The existing argument preserves every dirty gate true on the bad edge, hence its strong uniqueness hypothesis. Arbitrary circuits may contain redundant repeated-input gates, so any stronger normalization likely must use minimality.

## Gate pruning observation

Any gate false on all prime edge inputs can be replaced by false and propagated away. The new monotone circuit is pointwise below the old one and still accepts all prime edges, so computes exactly the same incidence function. In a least circuit every gate is therefore true on some incident pair. In particular the first AND joins an incident point and line; same-side, nonincident, or repeated-operand first ANDs are removable. For Fano this leaves four first-gate symmetry types: incident AND, same-side OR, incident cross OR, nonincident cross OR. This helps finite search but does not establish normalization.

No counterexample, closed general proof, or new checked Lean result has been produced by this strategy yet.
