# L-meta-997 source reuse and exact remaining bridge

The actual sparse-window count is L_meta_782.card_assigned (lines 227–301), rather than L_meta_885, whose CountHyp is a premise. It charges all gate wires whose singleton support has at least two elements and is contained in the target line. Its cut proof needs only binary fan-in, so the proof extends to fan-in at most two, including constants and unary gates.

SparseCount.lean in this directory inlines evaluation, gate-input, cut, and support lemmas from L_meta_986 (lines 1–202), followed by that L_meta_782 proof. The resulting public theorem is:

- monotone AND/OR gates, fan-in at most two;
- output rejects every assignment of weight at most k avoiding T;
- c <= k and c+1 <= singleton-support-cardinality of the output;
- conclusion c <= number of gate wires with support contained in T and support size at least two.

It compiled successfully with the pinned Lean wrapper; SparseCount.log is empty. formal_audit independently read the complete helper and found no issue, specifically checking empty/unary/repeated inputs and forward references defaulting to false. This is a concrete localized light count, not the complete posted theorem. The same file now also contains sum_min_card_le and sum_min_card_le_of_window. The latter assumes exact output correctness below weight k and proves sum_i min(k, |S_i|) <= C.size + m, including k=0 or 1 and empty/singleton lines. These wrappers compiled with an empty log and were independently audited by formal_audit.

Other sources:

- L_meta_986.owned (line 205), countOne (210): |S intersect P|-1 is bounded by gates having at least two singleton points in P and all such points in S; a designated always-true wire is excluded.
- L_meta_988.asg (196), card_le (238): |T| <= assigned gates +1, where a gate is globally sound for T and has at least two accepting background singletons. This is the heavy/background count.
- L_meta_885.local_count (132) packages CountHyp plus a circuit-restriction premise; it does not itself resolve either missing premise.
- L_meta_529.main_inv is a full-monotone partition argument, but also counts proper partial supports.

The 997 refund is smaller than the intersection of these coarse charge sets: it requires the complete light singleton support to equal a posted line and the complete heavy singleton support outside y to equal a disjoint posted line. No cited count lemma gives that stronger condition.

A concrete valid circuit demonstrates the failure of naive intersection inclusion. Let y={a,z}, h=a AND z, N=NOT h, P=b OR c, Q=d OR e, and g=(N AND P) OR (h AND Q). The outputs a OR g and Q OR f compute OR{a,b,c} and OR{d,e,f} exactly. The NOT is true below weight two and false at y. Wire g has light support {b,c} and heavy support {d,e}. Both are proper subsets of their output lines, so g belongs to both coarse assigned sets and neither exact-profile refund family. PartialOverlap.lean encodes the actual nine-gate circuit and checks these facts; its pinned Lean compile passed with an empty log. This is a counterexample only to the naive inclusion, not to the posted inequality: a minimal heavy charge assignment can use Q instead of g.

The remaining mathematical obligation is an exchange/uncrossing argument choosing sufficiently large light and heavy gate sets with overlap restricted to exact profiles, or an amortized inequality that accounts for the proper-overlap gates using other uncharged gates. The existing static assigned sets do not suffice.

## Stronger heavy bound completed and independently audited

HeavyOrCount.lean is a self-contained checked helper (only Mathlib and PEqualNP.Defs imports). It inlines fp3_strategy/meta997/WeightedFrontier.lean and the necessary evaluation machinery from L_meta_988. The final pinned Lean compile succeeded with exit 0 and empty HeavyOrCount.log. formal_audit read the full assembled file and found no flaw.

The central definitions and interfaces are:

- `outside T p = decide (p notin T)`.
- `supp C Y w` is the set of p for which wire w accepts the assignment Y union {p}.
- `charged C Y T` contains actual gate wires w that are OR gates, are false on the maximum outside-T assignment, and have at least two accepting background singletons.
- `decompose`: for a wire false outside T with at least two accepting background singletons, there is a finite set P of earlier wires, all false outside T, whose supports cover the parent support. The size of P is at most 1 plus the indicator that the parent is charged. AND gates select one fixed false-outside child; OR gates select at most two children.
- `card_le_or`: for a monotone fan-in-at-most-two circuit, disjoint Y and T, an output globally sound for T, and acceptance on every Y union {p} with p in T, one has `T.card <= (charged C Y T).card + 1`.
- `charged_disjoint`: for a common background Y and target lines with intersection size at most one, their charged sets are disjoint.
- `charged_false_background`: every charged gate is false on Y.

The abstract weighted frontier theorem processes every paid wire at most once in decreasing order. Its invariant preserves support coverage, not full gate-value equivalence. Thus selecting one child at an AND gate is sound for this counting argument even though it does not generally preserve the gate function. Future wire reads are correctly interpreted as false and filtered out.

This frees AND gates from the heavy charge budget. A possible route to the posted statement is to use uncharged selector/AND gates to compensate for light/heavy OR overlap. That compensation theorem remains unproved. In particular, equal singleton supports do not justify bypassing an arbitrary light AND: such a gate can eliminate higher-order false positives while retaining all singleton behavior. The special AND gates selected by the frozen-true NOT constant are fully redundant and can safely be removed, but no general argument shows that these alone pay every proper overlap.

The source sketch therefore has a precise remaining gap: selecting or amortizing the light and OR-only heavy charges so their shared cost is bounded by the posted exact-profile refund. Existing static partial-support charges do not satisfy that inclusion, as the kernel-checked PartialOverlap example demonstrates. No counterexample to L-meta-997 itself was found.
