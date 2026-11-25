# Guard charging and the unresolved exact-pencil case

This is a research plan for a restricted thirteen-output line-input problem. It does not prove the posted 51-OR bound. `lemmas/GuardCharging.lean` contains checked generic conditional lemmas. Its245-line immutable snapshot is `checked/guard-charging.lean`, SHA2566e2c31baa3ce2f08339feb65bfaa9e5f13da150da828e5bd7f669ca63b52d9be. The check completed with exit0 at05:50:21UTC in the short slot between solver runs; the complete log is adjacent. No finite geometry or unrestricted circuit lower bound is asserted by that snapshot.

## Semantic objects

Let `V = Fin 13` be line variables and `P = Fin 13` be points. Write

```
pencil p = {l | AllRows.incidence p l}
fourCaps = {N : Finset V | N.card = 4 and no three members are concurrent}
```

For every OR gate `j`, let `support j` be the set of line singleton inputs on which that gate evaluates to true. Let `targets j = {p | pencil p ⊆ support j}`. A gate is useful if it is false on at least one four-cap input. Monotonicity implies that a useful gate's support is disjoint from that cap. The avoiding points of a four-cap form a noncollinear triple, so `targets j` has at most three members.

For a target `p`, a guard is a useful OR gate whose support contains `pencil p`. A private guard has exactly one target; a shared guard has at least two. Expanding the final AND cone of an output shows that every outside four-cap must be rejected by a guard: a raw input cannot be true on all four required singleton positives, and a true constant cannot reject a cap. This expansion does not require AND-free OR operands.

Define `exactTargets = {p | ∃ j, support j = pencil p}` and `active = univ \ exactTargets`. The definition intentionally includes every OR gate, even a gate that is never used by an output; this weakens the lower bound safely.

## Local geometric lemma

The desired finite geometry interface is:

```
residual_cover_bound
  (p : P) (A : Finset V) (Q : Finset P)
  (small : A.card ≤ 2)
  (outside : Disjoint A (pencil p))
  (other : p ∉ Q)
  (covers : ∀ N ∈ fourCaps, Disjoint N (pencil p) → A ⊆ N →
    ∃ q ∈ Q, Disjoint N (pencil q)) :
  9 ≤ 3 * A.card + Q.card
```

For zero, one, or two distinct selected lines in `A`, the points avoiding those lines, excluding `p`, lie on four rays through `p` with sizes respectively `(3,3,3,3)`, `(2,2,2,2)`, or `(2,1,1,1)`. Every pair on different rays corresponds to a four-cap whose avoiding point set is exactly `{p,q,r}`. Therefore `Q` vertex-covers that complete multipartite graph. Its minimum cover sizes are 9, 6, and 3. Repeated choices of the same extra line only increase the required cover bound.

For `p ∈ active`, select one extra line outside `pencil p` from each private guard. If there are at least three private guards, the desired inequality is immediate. Otherwise their selected lines form `A`, with `A.card` at most the private-guard count. Select one other target from each shared guard, obtaining `Q`, with `Q.card` at most the shared-guard count. On a cap containing all selected private extras, every private guard is true. A rejecting guard is therefore shared, and its selected other target avoids that cap. The geometric lemma gives

```
9 ≤ 3 * privateGuards(p).card + sharedGuards(p).card.
```

This step uses only monotonicity of the singleton support and remains valid with arbitrary ANDs inside OR operands.

## Global charge

Assign a useful gate weight 3 if it has one target, and weight 1 otherwise. Sum the local inequality over active targets. A private gate contributes at most 3, and a shared useful gate has at most three targets, so it also contributes at most 3. Thus there are at least `3 * active.card` useful OR gates guarding active targets.

The generic finite counting proof is drafted in `GuardCharging.three_per_active_target`. It assumes the local inequalities and target-cardinality bound explicitly. The same source derives the target-cardinality bound from maximality, proves the complete multipartite vertex-cover estimate, and derives the private/shared local inequality from the residual geometry interface.

## Pure-union architecture

In the restricted architecture, every internal gate is the union of two earlier literal-union signals, and the thirteen outputs are free intersections of those signals. If a gate has support exactly `pencil p`, its pure-union ancestry contains at least three nontrivial union nodes with supports contained in `pencil p`. For distinct points these node sets are disjoint: their support would otherwise contain at least two lines in two pencils, contradicting pencil intersection size one. Such nodes cannot guard an active target either.

Consequently the exact targets contribute three additional, disjoint gates each. Combining this with the active-target charge gives `3 * 13 = 39` OR gates. The finite aggregation is drafted as `GuardCharging.exact_and_active_count`. The generic `interiors_pairwise` and `guard_interior_disjoint` lemmas establish the disjointness claims from pencil intersection size at most one. The ancestry lower bound is now drafted in `PureUnionAncestry.lean`: the four-element case uses only two levels of union ancestry. Its explicit `Scheme` allows singleton/empty sources and earlier binary-union outputs, with no AND filtering. The uncompiled `RestrictedUnionBound.lean` assembles the restricted39 conclusion from this scheme and cap-separation; the last requested finite helper is `GuardGeometry.fourCap_avoiding_card`.

## Missing unrestricted argument

For arbitrary ANDs inside OR operands, a support equal to a pencil can arise by intersecting larger supports. The pure-union ancestry claim is then false as an argument: supporting OR gates need not themselves have support contained in that pencil, and may also guard other targets. The precise open task is to replace the three-disjoint-ancestor charge by an amortized charge for the first exact-singleton-pencil wires. No such invariant is currently proved.

The complete posted circuit can also mix point and line variables inside OR operands. A thirteen-output line restriction therefore needs its own reduction before any 39-plus-12 argument would establish the full 51 bound. No such global normal form is assumed here.
