# Global OR-count investigations

No global lower bound was obtained. The target needed by the proposed
decomposition is at least51 OR gates for the plane incidence function;
De Morgan duality turns this into at least51 AND gates for the52-clause
vertex-cover CNF. The checked circuit normalization now permits every
gate to be active and essential on some minimal edge, but those conditions
do not supply the missing count.

## Two failed local potentials

For an AND-closed available family A, call a function clean when it is
pointwise below the target graph function. One proposed potential joined
two target edges whenever a clean available function accepts both.
This connectivity rank can drop by two at a single OR even for a path:

F = vz OR wt OR av OR aw.

First form q1=(v AND z) OR (w AND t), then q2=q1 OR a. Before q2 the
components are {vz,wt}, {av}, {aw}. The two clean meets v AND q2 and
w AND q2 connect all three. A later OR v OR w is still required to
assemble the full output. The potential loses this later assembly cost.

A repair used the minimum number of clean available functions covering
all target edges. It also lacks a local decrease-at-most-one property.
For a matching of five edges e_i=x_i AND y_i, form, in the displayed
left-associated order,

- a = x0 OR e1 OR e3;
- b = x0 OR e2 OR e4;
- t1 = y0 OR e1 OR e2;
- t2 = y0 OR e3 OR e4.

Every old clean meet accepts at most one of e1,e2,e3,e4, possibly along
with e0, so four clean functions are needed. Adjoining u=a OR b permits
the two clean functions u AND t1 and u AND t2 to cover all five edges.
All displayed gates are active on a target edge. Earlier dirty ORs have
paid a large cost that this local cover measure does not retain.

The matching construction also has a redundant OR branch: replacing
the first x0 OR e1 in a by e1 preserves the final target edges because
b still supplies x0. A sufficiently strong minimum-OR normalization
could exclude this example. That observation is not a proof that the
local potential becomes valid after normalization. Direct wire aliasing
can create duplicate AND inputs and alter formal derivatives, so any
such normalization needs the checked collision-handling compiler or a
separately justified replacement.

The structural agent subsequently refuted even that proposed repair.
For two disjoint two-edge stars, write

F = l(x1 OR x2) OR m(y1 OR y2).

For each i form e_i=xi AND l, f_i=yi AND m, and
h_i=(e_i OR yi) AND (f_i OR xi). Thus
h_i=e_i OR f_i OR (xi AND yi), with the last term dirty. Before the OR
q=l OR m, the old clean functions cover only individual target edges,
so the cover number is4. After adjoining q, the two clean functions
h1 AND q and h2 AND q cover all four edges, giving cover number2.
Their final OR computes F. The complete14-gate circuit has every gate
essential on a target edge and every OR branch globally essential;
both formal directional derivatives vanish on every target edge.
The full64-row checks, derivative results, and exact clean profiles are
in `results/orch/tau-branch-irredundant-counterexample.json`.
Its six ORs leave ample historical cost: this refutes the local potential,
not the conjectured global OR lower bound.

The same identities scale to two disjoint k-edge stars. Before q the
clean-cover number is2k, after q it is k; the actual OR count is3k.
Thus no constant local-drop bound follows from gate activity, gate
essentiality, OR-branch essentiality, or vanishing marked derivatives.
The target is a forest, so a correction depending only on target cycles
cannot fix this obstruction.

## Completed bounded computations

`dual_cnf_sat.py` encodes the full truth table of a vertex-cover CNF in
the free-OR, paid-AND model. Its disjoint bare-variable constraints use
singleton stripping; all targets reject every singleton, so no bare
output variable is needed. Both AND sides may select any prior ANDs.
The output may OR any selected AND gates. A model, if found, is decoded
and checked independently on every truth input.

The four six-vertex C4-free seven-edge isomorphism representatives in
`c4free-6-7-reps.json` were all UNSAT at five AND gates. Complete solver
logs are `dual6-7-i0-and5-solve.log` through `dual6-7-i3-and5-solve.log`
in the job scratch directory. Their wall times were3.24,5.01,4.67,7.39
seconds, with at most10.25MB resident memory. These checks complete the
previously untested five-OR cases for those four graph types.

The unique three-by-four bipartite C4-free seven-edge type (a six-cycle
with a pendant edge) was also UNSAT at five AND gates. Its full log is
`dual7-7-bip-and5-solve.log`; wall time7.09seconds, memory9.50MB.

`clean_cover_potential.py` sampled148236 transitions in24706 six-variable
trials across the four seven-edge types without finding a local-cover
counterexample. This sample does not rescue the potential: the explicit
five-matching construction above refutes it on ten variables.

All SAT and sampling results here are computational evidence, not Lean
certificates. No smaller-circuit plane counterexample was found.

## Direct plane relaxation under the resource cap

The existing all26-unknown-word, twelve-coordinate signed-code instance
has367558 variables and1195283 clauses (22126888 bytes). Its SHA256 is
`4d80ea4749240cc5e0f11af7666497aea32664a6b63633d1adc400952a831a85`.
An intended180-second run under a hard300MiB address-space cap aborted
after13.20seconds with `std::bad_alloc`/SIGABRT, peak RSS282804KiB.
A single fallback with the documented `--plain` option and identical
caps also aborted, after15.01seconds, peak RSS282644KiB. Both reported
UNKNOWN; neither produced a model or an UNSAT certificate. The address
space limit was not increased.

Complete output and metadata are in the job scratch files
`plane-signed-generic-180s.log`, `.json`, and
`plane-signed-generic-180s-plain.log`, `.json`. The reproducible capped
runner is `results/orch/bounded_solver.py`. No solver remains running.
