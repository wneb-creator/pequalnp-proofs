# Canonical p10, Bplus14 / Bzero0: finite exploration

This is finite research, not a Lean proof or a circuit witness. Assumptions are StrictLive/Correct Fano, ineligible points {0,1,2,3}, missing point-neighborhood masks {4,5,6}, Bplus=14, Bzero=0, total surplus14.

Local line labels0..6 mean original inputs7..13. Neighborhood masks are [11,69,98,49,88,44,22]. The four required occurring triples are11,69,98,49. The missing triples are88,44,22.

## Justified count premise

The compiled generic equality_hw_mask_family applies with P=all7lines, Oc=I={0,1,2,3}, Ct={4,5,6}, eligible-cardinality10, and Ct-neighborhood union-cardinality6. Thus every occurring family Y of masks of size at least2, whose pair members lie inside one of the four required triples, satisfies

    |Y| +4+6+10 ≤ 2*7+14, hence |Y|≤8.

This specialization has been checked mathematically with algebraic_route, but no new Lean specialization was compiled here.

## Parent-family / closure computation

Each required triple has10 parent choices from the accepted sup_triple_parent statement:3 contained pairs,4 containing four-sets,3 unordered pairs of five-sets whose intersection is the triple. The10^4 choices produce2,408 distinct size8 families; all other choices have size9–12.

For every size8 family, grant empty/singletons and ALL9 pairs outside the required triples, as well as its family masks. Start with every allowed mask of size at most2 and close under BOTH union and intersection whenever the result is allowed. Exactly81 families are constructible. Every one consists of the four required triples plus one contained pair per triple (3^4).

This closure is a sound overapproximation of actual projected support-mask generation once the count saturation supplies the allowed-family premise. The finite closure data are Python-checked only, not kernel-certified.

## Residual4 model

Assuming the preceding family-shape result, each assigned ineligible-point line mask is exactly its own neighborhood. Each residual-unit line support is empty, a singleton, a pair, or one of the four required triples. Among the four unit masks, at most one distinct pair inside each required triple may occur.

For line t, R_t is the set of residual units carrying t. The assigned budgets require |R_t|≥[1,1,0,0,0,1,1]_t. Co-label requires t∈N_i whenever x∈N_i, R_x⊆R_t, and R_x is nonempty or x,t share a required triple. The compiled +9 cofactor wrapper gives

    |R_0| + #{t≠0 : R_t⊆R_0} ≤5.

The older +8 wrapper gives at every other line center t

    |R_t| + #{x≠t : R_x⊆R_t and (R_x nonempty or x,t share a required triple)} ≤6.

Every such center leaves at least one eligible point among4/5/6 free, and the charged sets consist only of line inputs. Thus these cofactor cuts have the required free-point geometry; actual coordinate transfer is still separate.

Enumerating58,905 four-unit multisets gives52,491 pair-compatible states,11,852 satisfying budgets,57 satisfying co-label, and49 satisfying the center+9 cut. Fixed-sharing co-label and the other +8 cuts remove no additional states. The49 survivors form12 orbits under the six Fano automorphisms preservingI0123.

The simplest survivor has unit masks[1,2,32,64], i.e. {0},{1},{5},{6}; R2=R3=R4=empty. Its center cost is4. These are abstract necessary-condition models, not actual circuits. They demonstrate that the present finite constraints alone cannot close the case.

Constructive_route has a possible residual C6+three-private-leaf component obstruction. Its protected-star deletion/preservation-of-eligible-labels bridge is unproved, and was NOT imposed in this census.
