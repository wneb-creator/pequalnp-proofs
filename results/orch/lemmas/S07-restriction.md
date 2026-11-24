# S07: vertex restriction and gate elimination for arbitrary circuits

Owner: S04/Huygens taking the authorized S07 backlog. Updated about 03:44 UTC. Scratch remains `/tmp/oec/pequalnp-pilot-18/orch/S04/`. This route does not use a late-junk index or assume clean ANDs.

**Concrete result:** a mathematically justified restriction recurrence, strengthened by a first-gate incidence lemma, gives lower bound **15** for arbitrary monotone binary circuits for this graph. It does not exclude size21. The exact cofactors at vertex0 and a graph-specific obstruction to stronger single-read elimination are given below. Three small algebra/arithmetic helpers compile in Lean; the circuit-normalization/counting argument and the full 15-bound calculation are not yet Lean-formalized.

## Model and a general gate-elimination lemma

Let L(f) be minimum binary monotone circuit size with free FALSE/TRUE sources. This is a relaxation of the raw Monotone2 model, so any lower bound for L applies to the posted model. A minimum circuit for a nonconstant function has no constant-input gates, copies, repeated-input gates, dead gates, or uses of inessential variables: constant propagation, alias deletion or fixing an inessential input would otherwise decrease size. Its gates have two distinct inputs, every gate reaches the output, and the first gate reads two ordinary input variables.

For an essential variable v, let d be the number of distinct gates reading it directly. Fixing v to either Boolean value deletes all d direct readers: each becomes a constant or an alias. Thus, writing f0/f1 for the cofactors,

`L(f) >= d + max(L(f0), L(f1)) >= 1 + max(L(f0), L(f1)).`

If both cofactors are nonconstant, at least one branch deletes two gates. When d>=2 this is immediate. When d=1, let g be the unique reader. If g is AND, fixing v=0 makes g=0 and deletes g and a later reader of g. The latter exists because g cannot be the output: that would make f0 constant. For an OR reader use v=1 and the same argument with f1. These are distinct gates. Consequently

`L(f) >= max(1 + max(L(f0), L(f1)), 2 + min(L(f0), L(f1))).`

This is a lower bound for arbitrary monotone circuits. It says nothing about whether surviving ANDs are clean. Importantly, the second term is a MIN of the cofactor complexities: the absorbing polarity depends on the reader's operation.

## Exact graph cofactor costs

For any graph G and nonisolated vertex v,

`F_G | v=0 = F_(G-v)`

and

`F_G | v=1 = OR(N(v)) OR F_(G-N[v]).`

The variables in the two parts of the second expression are disjoint. For any nonconstant h independent of k variables y1..yk,

`L(y1 OR ... OR yk OR h) = k + L(h).`

The upper bound appends k OR gates. For the lower bound, set those variables to zero one at a time. Each remains essential until removed, each restriction deletes at least one direct-reader gate, and the remaining function stays nonconstant because h survives. Thus at least k gates disappear. If h is FALSE, use the usual k-1 lower bound for the OR of k essential inputs instead. No clean-output or clean-intermediate premise is involved.

This yields an induced-subgraph recurrence. Put `a=B(G-v)` and

`b=deg(v)+B(G-N[v])` if the residual graph has an edge, or `b=deg(v)-1` otherwise.

Then `B(G) >= 1+max(a,b)`. If G-v has an edge, both cofactors are nonconstant and also `B(G) >= 2+min(a,b)`. Start with essential-input bound n-1 and take the maximum over vertices and the first-gate seed below. All induced graphs are C4-free because the original graph is C4-free.

## A first-gate seed independent of cleanliness

**Lemma.** If G is C4-free, has n nonisolated vertices, and minimum degree at least2, then `L(F_G) >= n+1`.

In a minimum circuit let the first gate read distinct input variables a,b. Both a and b must have another reader:

- If the gate is AND and a has no other reader, choose a neighbor u of a different from b. The inputs `{a,u}` and `{u}` give the same first-gate value0 and the same other accessible input values. The circuit cannot distinguish them, but the graph function must. Thus a has another reader; the same applies to b.
- If the gate is OR and a has no other reader, first a,b cannot be adjacent: `{a,b}` and `{b}` would be indistinguishable downstream. For every neighbor u of a, compare `{a,u}` with `{b,u}`. The OR gate is1 in both, and every other accessible input only increases in the second input. Monotonicity forces `{b,u}` to be positive. Hence `N(a) subset N(b)`. Since deg(a)>=2 and a,b are distinct nonadjacent vertices, this would give a C4. Again both inputs have another reader.

There are at least n+2 input-to-gate ports: one for every essential variable plus one extra for a and b. If there are m gates, liveness gives at least m-1 gate-to-gate ports. There are exactly 2m incoming gate ports, so

`2m >= (n+2)+(m-1)`, hence `m >= n+1`.

The lemma gives triangle lower bound4, matching its four-gate construction, and C5 lower bound6. The familiar clean C5 bound7 has NOT been transferred to arbitrary circuits. This is precisely a remaining one-gate gap even before combining components.

## Concrete vertex0 calculation

Vertex0 has neighbors9 and10. Its zero cofactor deletes two edges and preserves both triangles `(1,4,8)` and `(3,6,7)`; the five-cycle becomes the path9–5–2–10. The zero graph has10 essential vertices and14 edges. Its clean lower bound is19, but the arbitrary-circuit recurrence above yields only13.

Its one cofactor is

`x9 OR x10 OR F_H`,

where H has vertices1..8 and edges

`(1,4),(1,8),(2,5),(3,6),(3,7),(4,8),(5,8),(6,7)`.

H consists of the intact triangle `(3,6,7)` and the other triangle with the path2–5–8 attached. The recurrence gives `B(H)=11`, hence the one cofactor has lower bound13. Therefore vertex0 gives

`L(F_G) >= max(1+max(13,13), 2+min(13,13)) = 15`.

All 1024 assignments of the remaining ten inputs were checked against both explicit cofactor identities. The recurrence was evaluated on all2048 induced vertex subsets. Every root-vertex choice currently yields15; there is no hidden better root choice in this recurrence. The full table is preserved, not just the root result. Before adding the first-gate seed, this same recurrence gave14.

The triangle/C5 decomposition suggested by the orchestrator is therefore useful for the seed and preserved-cofactor structure. It does not justify adding the three component complexities: arbitrary circuits may share computations across the five crossedges, and no direct-sum theorem has been proved here.

## Concrete obstruction: a single-read OR can hide dirty higher terms

For this graph let `D=x4 AND x5`. D is false on every singleton yet TRUE on the independent input `{4,5}`. It is therefore dirty, despite empty singleton support. The following identity holds on every input:

`F_G = F_(G-0) OR ((x0 OR D) AND (x9 OR x10)).`

Expanding the additional terms gives `x4 x5 x9` and `x4 x5 x10`. The first is absorbed by the existing edge5–9 and the second by the existing edge4–10. The identity was separately checked on all2048 inputs.

This provides an exact circuit expression in which x0 is read only by an OR, with an earlier dirty sibling D. It is not claimed to be minimum or size21. It rules out extending the first-gate prohibition to every later unique reader, and rules out treating empty singleton support as cleanliness when leaving the clean-prefix setting.

There is also a useful necessary condition: if x0 has a unique OR reader `x0 OR H`, H has empty singleton support. Indeed, any singleton u accepted by H would have to be adjacent to both9 and10, by comparing the positive edge inputs `{0,9}` and `{0,10}` to `{u,9}` and `{u,10}`. The only common neighbor is0, and H is independent of x0 because it precedes its unique reader. The concrete D above shows why this necessary condition does not allow H to be deleted. This is the specific obstruction to making the vertex0 recurrence much stronger without controlling dirty computations.

## Compiling Lean fragments and evidence

Source: `orch/S04/VertexRestriction.lean`, SHA `df8b3db386502c3c1e17d88fa9cfc66ecf41dca4bf3afb5cfee2774447f0fc20`. It compiles under the pinned Lean toolchain, exit0 in6.35s, holding the shared Lean lock. The complete `vertex-fragment.stdout.log` and `.stderr.log` are empty; source/command/time binding is in `vertex-fragment-result.json`.

The exact checked algebraic identity is:

```lean
lemma vertex_zero_guarded_extension (r x0 x4 x5 x9 x10 : Bool) :
    (r || (x4 && x10) || (x5 && x9) || (x0 && (x9 || x10))) =
      (r || (x4 && x10) || (x5 && x9) ||
        ((x0 || (x4 && x5)) && (x9 || x10)))
```

Two arithmetic helpers prove the final port inequality from explicit numeric premises and combine the two cofactor inequalities. Exact statements for all three are in `vertex-exact-statements.txt`. Their namespace is `PEqualNP.Outside.L_meta_1342_aux.S07`. The file uses allowed Mathlib imports, no options, no additional axioms, and no prohibited proof mechanism.

Separate audit: `VertexRestrictionAudit.lean`, exit0 in3.23s. The Boolean lemma has no axioms; the two arithmetic lemmas use only `propext` and `Quot.sound`. Complete audit stdout SHA `5f056aed9a359c15cc96043e91ad46ad041a2fa2ed2af52a1f2b00108f421953`, empty stderr. `vertex-axioms-result.json` binds the audit and original source. The orchestrator received the compilation notice with exact statements and logs before this report.

Scalar recurrence/identity script: `restriction_recurrence.py`, SHA `a76303e36d15f7be6e99a60e309765157ae570ba5d924e18ce079511a235191e`. Result `restriction-recurrence.json`, SHA `2bce9f2dd22c90c35dc3647c46f703b0975e0e00af14dc56f842f1c5799700ca`; full final logs `restriction-final.stdout.log` and `restriction-final.stderr.log`. The result contains all2048 induced-subgraph lower bounds, cofactors, graph counts, and guard checks. Earlier weaker-recurrence logs are retained separately.

The compiled fragment does **not** establish gate deletion on the project Circuit type, the first-gate structural lemma, or the final bound15 in Lean. Those remain explicit mathematical arguments with scalar calculation. No size21 witness, 22 lower bound, or global refutation is claimed.

## Next useful step

Do not replace the arbitrary cofactor bound13 by its clean bound19. A sharper route must charge how dirty subcircuits such as D can be reused, or settle the arbitrary six-gate C5 case and strengthen component-preserving deletion counts. The guarded identity has been sent to S05 as a possible construction ingredient; S01 late-junk work is not duplicated. No further solver or long proof run was started. The named file, active workers, leases, other agents' outputs and git history remain untouched.
