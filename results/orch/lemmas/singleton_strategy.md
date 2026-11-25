# Singleton normalization strategy

## Checked result for formulas

`singleton_formula.lean` uses the existing library type `DMFormula`; it defines positivity and the condition that every AND node rejects every singleton. Its `normalize` lemma gives an equivalent positive formula satisfying that condition, with no more leaves. This holds for every positive Boolean formula, without a graph or four-cycle hypothesis.

The proof first cleans both children. If an AND still accepts singleton x, both children expose an x leaf through OR nodes only. `extract` removes that leaf, leaving either x alone or x OR R, with a one-leaf saving. Replacing `(x OR R) AND (x OR S)` by `x OR (R AND S)` saves one further repeated x occurrence. Strong induction on leaves cleans the smaller expression. Pure-x cases use absorption.

This proves the no-sharing case and provides an exact size credit. It does not establish the circuit theorem: extracting x-free residuals from a shared OR DAG may require copying gates whose original values are still used elsewhere.

## Failed direct bypass

Even for a bipartite four-cycle-free quadratic output, replacing a singleton-dirty AND by either factor need not preserve output. Let `g=(x OR a) AND (x OR b)` and output `(g AND c) OR (a AND b)`, where the target is the disjoint-edge function `xc OR ab`. Replacing g by its first factor adds ac; replacing by the second adds bc. The original circuit is not least, so this does not refute the posted statement or a least-circuit rewrite.

## Remaining ownership route

For an edge ab created by a gate accepting singleton x, with x and a in the same bipartition, a later filter accepting ab via singleton a also accepts xa until some subsequent filter kills it. A filter accepting ab via singleton b can retain an actual edge xb. A filter accepting ab via neither singleton contains another edge-creation event. This suggests charging edge propagation to either a star edge, an independently created edge, or a filter that kills a same-part false pair. No complete accounting for shared gates has been obtained.

The counterexample worker queried minimum circuits with an AND accepting a singleton for P4, P4 plus a disjoint edge, P6, and C6. Those bounded queries were UNSAT at independently established minimum sizes; they are computational evidence only and do not establish the general strict-drop statement.
