# Conceptual boundary after the finite searches

These are mathematical observations and an exhaustive small graph census, not Lean proofs. The unrestricted L-meta-3457 statement remains unresolved. No new proof or refutation is claimed.

## The requested class is genuinely weaker than output-dominating ANDs

For the two-edge matching function F = p0*l0 OR p1*l1, let

    g = (p0 OR l1) AND (p1 OR l0).
    h = g AND (p0 OR p1).
    out = h AND (l0 OR l1).

This seven-gate circuit computes F. Every AND is false on singletons and on the two nonincident cross pairs. Nevertheless g is true on each same-part pair, and h is true on the two-point pair, where F is false. These gates are live. Thus the desired cleanliness does not imply that every AND implies the output. The matching also has a simpler three-gate clean circuit; this example is not a size separation or refutation.

Similarly, a clean AND can create two cross-edge stars in opposite orientations, together with same-part pairs. It is unjustified to count every clean AND as owning only one star or one edge. The candidate bound |E| + minimum vertex cover - 1 is a stronger route and was never established globally by these searches.

## A valid no-cost local trick and its limit

Suppose A AND B is a dirty intermediate used only in an AND with an independently available clean wire H. Associativity replaces

    (A AND B) AND H

by

    (H AND A) AND B.

This uses the same number of AND gates. Both new intermediates inherit every zero-test property of H. The rewrite requires that H not depend on the deleted intermediate, and that any other uses of that intermediate be handled; otherwise duplication or a cyclic dependency can appear. It is useful for an unshared AND region containing a clean seed, not a general DAG normalization.

A concrete obstruction to mere reassociation is the three-edge matching. Write its eight minimal-cover clauses

    C_e = v_1(e_1) OR v_2(e_2) OR v_3(e_3),
    v_i(0)=p_i, v_i(1)=l_i, e in {0,1}^3.

Their conjunction is the matching edge function. Start by ANDing the complementary all-point and all-line clauses, then AND in the remaining clauses. All ANDs are singleton-zero, but the first AND accepts nonincident cross pairs.

Keeping those eight clause wires fixed, no reassociation can make every AND clean. A bottom AND of two noncomplementary clauses shares a singleton. Complementary clauses avoid singleton overlap, but at least two of their three matching indices have the same orientation; their conjunction therefore accepts a nonincident cross pair. Thus every possible bottom pair violates one of the two cleanliness conditions. The whole function still has the ordinary five-gate clean DNF. The example shows that a general proof must change OR structure or use global cost savings, not merely reorder ANDs. It does not refute the posted existential statement.

## Why the investigated literature constructions do not transfer

The raw Tarjan Boolean-sum trick uses ANDs that are true on original singleton inputs. Substituting disjoint matching products makes them singleton-clean, but also already makes them clean on nonincident cross pairs; its multioutput single-level separation then lies inside the requested clean class. Folding outputs into one function with selectors produces repeated neighborhood overlap and C4. Saturated single-output constructions accept same-part pairs at the final output; the posted bipartite edge function must reject those pairs and all larger independent sets. No cost-preserving filter or incidence-subdivision transfer was established. Exact source URLs and the distinction between verified source facts and our own reconstructions are in RESEARCH.md.

Consequently no known trick examined here either refutes the weaker requested normalization or supplies a full no-growth transformation.

## Exact small graph boundary

Delete isolated vertices and leaves repeatedly from a C4-free4-by-4 bipartite graph. Its remaining 2-core is one of:

- empty;
- the six-cycle;
- the eight-cycle;
- the theta graph consisting of three length-three paths with common endpoints.

An elementary argument explains the list. A nonempty minimum-degree-two bipartite core needs at least three vertices in each part. A3-by-4 core is impossible: four vertices of degree at least two would repeat a pair among the three opposite vertices, creating C4. A3-by-3 core has exactly six edges and is C6. For4-by-4, counting pairs of neighbors gives at most nine edges. With minimum degree two, eight edges give C8. Nine edges force degree sequence3,2,2,2 on each side. The two degree-three vertices cannot be adjacent: otherwise their remaining neighbors force a repeated pair. Their six degree-two neighbors are then joined by a perfect matching, giving exactly three length-three paths.

The preserved exhaustive census checks all65536 incidence matrices, retaining exactly18521 C4-free ones. Their core counts are:

| Core | Matrices |
|---|---:|
| Empty | 16145 |
| C6 | 2208 |
| C8 | 72 |
| Theta(3,3,3) | 96 |

Script: core_classification.py. Complete stdout/stderr and result JSON are saved beside it. Runtime was about0.187 seconds. This is finite graph computation, not a Lean certificate and not a circuit lower bound.

Conditional on completing the separately developed N<=3 normalization proof, the genuinely new leafless4-by-4 cases are therefore C8 and the theta graph. C6 with attached leaves also remains a separate extension problem: the existing existential normal form does not automatically preserve a useful attachment wire, and deleting a leaf can save only one gate when its sole reader is an OR. The current finite searches did not settle these families.
