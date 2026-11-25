# Two-junk upstream review

Reviewed 2026-11-25; research only. No new Lean theorem, target proof, refutation, or checker acceptance is claimed.

## Established source statements

- Local L_meta_4181 (1474 lines) already converts any public Monotone2 circuit computing a nonempty graph function to an IsLeastAO, TopForm circuit of no larger size. This removes the model-boundary concern for existence of a normalized minimum circuit, though it does not preserve each original AND.
- Local L_meta_3760 (10039 lines) proves junk.card != 1 for every least-AO circuit of a bipartite NoFourCycle graph. No size or TopForm premise is needed. Its rebuild may be expensive.
- Fresh L_meta_5779 preserves size and junk count while reaching TopForm. Fresh L_meta_5781 proves the edge/cover/penalty inequality and bounds a minimum cover after deleting Ustar by the number of non-centreless tops.
- Fresh L_meta_8103 supplies the one-junk cover charge when Ustar is nonempty. Together with L5781 and the plane's cover lower bound13, this excludes size<=63 in that case. Ustar empty follows directly from the min-cover half of L5781.
- Fresh L_meta_7895 assumes exactly two junk gates. It proves either 2*centreless.card + nonlam.card >= 2, or a precise nested chain g -> h -> m, with unique readers, centreless empty, nonlam={m}, and both junk gates true on every Ustar edge input. The first alternative remains a genuine open case; the theorem does not establish at least three junk gates.
- Fresh L_meta_8201 gives exact raw-side/earlier-junk semantics for the first two ordered junk gates, useful for describing the nested chain. It supplies no gate-count contradiction itself.
- Fresh L_meta_6240 proves 2*|Ustar| <= penalty if every relevant centreless/junk/mixing gate accepts at most one Ustar edge. That extra hypothesis is substantial and is not implied by the plane or L7895.

## New mathematical consequence of L_meta_5869

Let U=Ustar, H=G minus U, and P=2*centreless.card+junk.card+nonlam.card. L5869 is an established proof, not a reduction. Under least-AO, TopForm, nonempty graph, NoFourCycle, junk.card>=2, P<=3 and U nonempty, it gives P>=3 and a vertex v with the following property. Each U-edge has an endpoint w adjacent to v in H. For every graph-independent input X containing w there is a cover K of U disjoint from X, with either |K|<=1 or K contained in a neighborhood in H.

For a bipartite NoFourCycle graph this condition forces |U|<=1. Orient any two distinct U-edges as (w,p),(z,q) with H(v,w),H(v,z). Both w,z are on the side opposite v; p,q are on v's side. Neither p nor q equals v because its U-edge would also be in H. If w!=z, noC4 shows p!=q and G(w,q) is false. If w=z, distinctness gives p!=q.

If w=z, choose X={w}. A cover avoiding X must contain p and q. It cannot be a singleton. If both p,q lie in H-neighborhood(a), then a!=w because the two edges were deleted, and a,w have two common neighbors p,q, contradicting NoFourCycle.

If w!=z, choose X={w,q}, which is independent. An avoiding cover must contain p and z. Those have opposite colors, so cannot both lie in any neighborhood of a bipartite graph; nor can the cover be a singleton. This again contradicts the supplied K.

Thus the explicit low-penalty nested exception in L7895 has |U|<=1. The full graph's vertex-cover lower bound13 implies a cover of G minus U has size at least12, by adding one endpoint of the removed edge. L5781 then yields size>=52+12+2-1-1=64. Consequently a target circuit cannot have the low-penalty configuration. This does NOT exclude the other two-junk branch with P>=4, nor does it prove a global refutation.

## Independent finite check

The scratch log reviewer-low-penalty-pair-check.log and reviewer-low-penalty-pair-witnesses.json enumerate all1716 cases for the exact posted plane:26 centers times choose(12 oriented residual arms,2). The indicated independent X was checked, and every singleton and every maximal avoiding H-neighborhood was checked as a possible cover of the two selected edges. None works. H was only the graph with those two edges deleted; removing more U edges can only reduce its neighborhoods. This is computational corroboration, not a Lean finite certificate.

## Non-applicable apparent shortcuts

Local L5226/L5228 and fresh L7467/L7559 specialize a different eleven-vertex graph and particular numerical equality cases. Local L5138/L5391 and the L474x shrinking lemmas require additional lift-fixed-point, private-factor, raw-side and loss-of-edge hypotheses. These are not supplied by L7895's chain alone. Reductions mentioning global repair or zero-junk normalization retain those as assumptions and cannot close the gap.
