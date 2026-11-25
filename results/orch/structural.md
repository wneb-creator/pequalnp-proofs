# Structural strategy for L-meta-2602

Started 2026-11-25 at approximately 02:53 UTC.

## Interpretation

The output is the bipartite edge function of the cyclic order-three projective plane. It has 26 inputs, 52 edges, and the standard 13-star construction costs 64 gates: 39 OR gates inside stars, 13 AND gates joining centers to stars, and 12 final OR gates.

The two derivative recurrences are formal derivatives evaluated at the singleton endpoints of the incidence (point 0, line 0). Simultaneous vanishing means that no accepting monomial uses either endpoint only once.

## Existing routes

`R_meta_2602_2` reduces the target to a 56-gate lower bound on the face obtained by setting an incident point and line to zero, and a path-counting statement. Lemma search identified these as open children L-meta-5985 and L-meta-5987.

`R_meta_2602_415` reduces via a guarded dead-wire set. Its general guard child is checked, but the geometry/counting face remains open.

Known checked cases L-meta-2067 and L-meta-2069 cover circuits without nested AND gates and circuits in which all AND gates imply the final output. Lemma search is preparing those separately; I am not copying them.

## Failed overly strong count

It is false that double vanishing forces three active AND gates. With distinct earlier inputs, set q = x AND y, t = q OR z, and out = q AND t. On the pair {x,y}, both derivatives vanish although only two AND gates occur. The circuit computes x AND y globally, by absorption. It has three gates rather than the one needed for x AND y.

Likewise q = x AND y, a = q OR z, b = q OR w, and out = a AND b computes (x AND y) OR (z AND w). It has four gates rather than the direct three-gate construction. The identity (q OR z) AND (q OR w) = q OR (z AND w) saves one gate.

These examples locate the missing argument: charge rereading to redundant gates, even when dirty intermediate conjunctions are shared with other outputs/subcircuits. Counting active AND gates alone cannot do that.

## Remaining structural approach

A promising strong statement is that a minimum circuit for a C4-free bipartite quadratic function can be converted without increasing size to one whose AND gates all imply the output. However, this is not immediate: dirty conjunctions may create nonedges that later conjunctions filter out. Treating these gates as independent stars assumes the main theorem rather than proving it.

No full proof or counterexample has been obtained by this strategy yet.

## Checked partial results

`FlagFragment.lean` proves that if point sets A and B each contain at least two points, at most two lines can have the property that every pair p in A, q in B has one endpoint incident to the line. Such lines are exactly the union of lines containing all of A and lines containing all of B; C4-freeness bounds each collection by one.

`CanonicalFragment.lean` proves that every false input is dominated by the canonical false input retaining its point bits and turning on exactly the lines avoiding those selected points. Monotonicity preserves truth at an unclean AND gate. Thus any target counterexample has a dirty-AND witness among 8192 canonical inputs. A separate Python enumeration finds 704 maximal independent inputs after closure, but the 704 count is not Lean-checked.

These partials do not yet connect the guarded-line count to an overall 65-gate lower bound.

## Narrow replacement route

Suppose a dirty pure-point flag g=(OR A) AND (OR B) is read only by clean AND gates that pair it with individual line variables l. For each reader, correctness forces A to be contained in the neighbors of l or B to be contained in those neighbors: otherwise choose one point from each set outside the neighborhood, together with l, to obtain a false graph input accepted by the reader. At that reader, replace g by the contained operand. This enlarges the reader only within the target edge function, preserves every old accepting input, and leaves g unused. A per-reader substitution followed by dead-gate removal therefore saves one gate.

This route excludes a concrete class of dirty flags. The unresolved issue is arbitrary readers and mixed intermediate functions, which need not be individual line guards.

## First dirty AND: rigorous obstruction to factor selection

On four variables x,z,y,w, let F = xy OR zw and use seven gates:

1. c1 = x AND y
2. c2 = z AND w
3. a = c1 OR z
4. b = c2 OR x
5. g = a AND b
6. t = y OR w
7. out = g AND t

Both c1 and c2 are clean; g is the first dirty AND. Its sole reader is a clean AND, but its other operand t is an OR of two line variables. Boolean expansion gives

    g = xy OR zw OR xz
    out = (xy OR zw OR xz) AND (y OR w) = xy OR zw.

On the minimal input xy, the only surviving formal monomial at the output is x^2 y^2, so both formal directional derivatives vanish. The same holds on zw.

Replacing g by a produces the false positive zy. Replacing g by b produces the false positive xw. On false inputs, c1=c2=false, so g reduces to the pure flag xz; substituting that flag globally loses both true minimal edges xy and zw. Thus neither first-dirty status, clean readers, nor double vanishing forces a safe per-reader factor choice or permits replacing the gate by its quotient flag.

There is a broader replacement: use c1 OR c2, then remove redundant surrounding gates. A global proof must track the clean summands and charge the gates that become dead, rather than only the flag's false-input values.

All 16 truth-table rows, the two derivative zeros, earlier-AND cleanliness, and the two false-positive replacement witnesses were checked by a direct Python evaluator. The data is in job scratch first-dirty-obstruction.json. This is not a counterexample to L-meta-2602; it is an obstruction to an overly broad local-rewiring claim.

## Safe semantic lifting and its two obstacles

If t is a clean function (t implies F), replacing g=(t OR s) AND b by g'=t OR (s AND b) preserves the final output F. Pointwise g implies g', and g' implies F OR g. Hence the replacement agrees on false inputs and cannot destroy a true output. It uses the same two gates when the original OR node has no other live users and its other operands can be scheduled before it. Shared OR nodes and dependencies between the two operand cones prevent an automatic same-size rewrite.

The derivative constraint adds a second obstacle. A clean summand t can have a positive derivative at the marked edge; lifting it across an AND may create a derivative path that was previously blocked. If t is false on the marked pair, its singleton values and directional derivatives are zero, so lifting that summand is derivative-safe. Thus one can try to lift unmarked clean summands first and leave marked-edge clean summands for the final count. No global cost bound for that plan has been established.

## Checked first-dirty theorem

`FirstDirtyFragment.lean` now proves the precise first-dirty consequence for arbitrary proper AND/OR circuits. If every earlier AND is clean and gate k is true on a false input, there exist at most two active input vertices whose singleton/pair input is still rejected by the circuit but accepted by gate k. The proof establishes full wire monotonicity and uses an OR-only path from an active input to each true operand of k. The statement permits the two vertices to coincide, covering singleton dirt.

`FlagSemanticFragment.lean` also checks the reader bridge: if (OR A) AND (OR B) AND a fixed line variable always implies the incidence function, then A or B is entirely contained in that line's neighborhood. These are necessary structural ingredients, not the missing 65-gate count.

## Global extraction and the collision obstruction

For a clean internal signal t, there is an exact semantic identity F = C[t := false] OR t. Monotonicity gives the residual at most F; when t is false the residual equals the original output, and when t is true cleanliness gives F. If t has zero ordinary values and zero formal derivatives at both marked singleton seeds, clamping and reattaching it also preserves both output derivative zeros. Every clean signal false on the marked pair has these zero signatures.

The naive size argument is incomplete. Constant propagation deletes the first reader of t, but a bypassed OR reader can become the same wire as another input of a later AND. Removing that duplicate AND by Boolean idempotence preserves ordinary values but changes its formal derivative: the derivative of z AND z is z AND dz, whereas the derivative of z is dz. Retaining distinct inputs by keeping the old OR padding wire can consume the gate saved by extraction. Shared OR dependencies have therefore been reduced to a precise collision accounting problem, not eliminated. No same-size derivative-preserving extraction theorem has been claimed.

A broad normalization theorem for arbitrary quadratic functions cannot be used. Read on 2026-11-25: Jukna, Disproving the Single Level Conjecture, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf, gives counterexamples based on saturated graphs; its cited C4-free gate bound concerns single-level circuits. The companion slides https://web.vu.lt/mif/s.jukna/papers/single-dag5.pdf state a C3/C4-free bound for formulas. These sources do not settle the bipartite circuit case needed here. No further external author-site requests will be made, in accordance with the network restriction.
