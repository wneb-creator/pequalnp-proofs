# Independent branch-rigidity review for L-meta-2592

2026-11-25. Mathematical notes only; no new Lean build or completed gap proof. Frozen when root reported the unexpected lease HTTP410. CofactorRobust.lean separately received semantic/format review PASS but remained UNCOMPILED.

## Cofactor robustness: proved on paper

Let a simple graph have minimum degree at least3 and at mostone common neighbor for any two distinct vertices. Fix disjoint sets T (true) and F (false), with |T|+|F|<=2 and T independent. Every vertex v outside T union F remains essential in the edge function.

If v has a neighbor in T, set every other free input false; toggling v changes false to true. Otherwise choose a neighbor w of v outside F and outside the union of neighborhoods of T. Each fixedfalse vertex excludes at mostone candidate; each fixedtrue vertex excludes at mostone by the common-neighbor bound. There are at least3 candidates and at most2 exclusions. Then T union {w} is independent, and toggling v creates edge vw. Triangle-freeness is not needed for this lemma. The same counting argument works for fewer than d fixed inputs when minimum degree is at least d and codegree is at mostone.

This exactly supports status_1035's finite Petersen witness statement. Repeated fixed coordinates must carry consistent assigned bits. A fixed assignment that already contains an edge is excluded because that cofactor is constanttrue.

## One-bit group separation: stronger than residual twins

The existing finite_branch_bit_factor proof fixes all earlier-label inputs false. It should extend to an arbitrary fixed subset P of earlier-label inputs true: replace each input assignment I union O by P union I union O. The ancestor lemma still makes the boundary bit independent of later-label inputs, and the same cut-agreement proof handles two current-group assignments with the same bit. This extension has NOT been formalized here.

Given that extension, a three-cofactor separator is rigorous. Suppose u,v are in one boundary group, w is a later input with uw an edge, and a is an earlier input such that av is an edge while au, aw, uv are nonedges. Fix earlier inputs to singleton a and all other inputs except u,v,w false. The residual function is v OR (u AND w), possibly with the redundant term v AND w. Current-group assignments empty, {u}, {v} yield the three distinct functions 0, w, 1 of later input w. They cannot factor through one Boolean bit.

For two active residual twins in Petersen, their common future neighborhood has at mostone vertex w. Any prior neighbor a of v is nonadjacent to u (otherwise there would be two common neighbors) and to w (triangle-freeness). For residual-isolated v and active u, choose a among the three earlier neighbors of v, excluding at mostone adjacent to u and at mostone adjacent to w. This separates an inactive vertex from an active one as well. Structural_bound independently checked all1,680 finite candidate cases. The current-group independence / later-position hypotheses must still be carried explicitly when formalizing; do not silently infer a circuit cut from an arbitrary vertex partition.

This suggests every active branch group is a genuine singleton, but it alone still permits six singleton cover vertices and four independent vertices whose first boundary is the output. It does not yet improve the six-branch lower bound.

## First branch signals and a precise obstruction

Conditional on singleton first groups and unique paths up to their boundaries, the new input has a fixed unate sign along its path. The first boundary bit is therefore the new input or its negation. At the second boundary, cofactor robustness under both assignments of the earlier input forces the same conclusion globally.

For a third singleton boundary, the argument still works if the first two vertices are nonadjacent. If they form edge ab, the cofactor a=b=true is forcedtrue and imposes no essentiality requirement. A positively unate boundary bit can be v, v OR (a AND b), or v AND NOT(a AND b); negative variants also occur. Thus blanket claims that all later branch signals are signed bare inputs are unjustified. These masks can carry genuine circuit information on an already-forcing cofactor, and replacing them by v need not preserve the surrounding circuit on that cofactor.

## Possible quantitative route, with the missing step exposed

In the exact six-root case, stronger singleton rigidity would leave a maximum independent set I of four inputs with no branch before output. Their subgraph is a read-once formula with C-only side signals, where C is the six-vertex cover. C consists of the six edges of an abstract K4; its three matching pairs are complementary K4 edges. Write M(C) for those three pair products and Li(C) for the OR of the three K4 edges incident to i. The target is M(C) OR the four terms Ii AND Li(C).

A C-star assignment makes all four I variables active and restricts the target to OR4. After pushing negations conceptually, every node separating two I-containing branches must therefore act as OR, requiring three binary nodes. Incomparability of the four Li on singleton C inputs forces each I leaf to have a private effective AND guard before its first merge. Finally f(C,I=0)=M(C) is nonzero, so some effective OR insertion of a C-only contribution is needed. Under these precise read-once/signed-skeleton assumptions this suggests at least8 I-involving binary nodes. With b=15, at most7 C-only binary nodes remain.

The tempting last step, four exact OR3 guard outputs require8 C-only binary gates, is NOT yet applicable: private guards may combine with shared later guards, and may agree with Li only where M=false. Expanding shared guards into four outputs can increase the gate count. Structural_bound's tiny support-set search found an8-binary floor for the exact four OR3 outputs even with free inversions; that is a separate finite-search claim pending its independent audit/formal certificate, not the required extraction theorem.

Two useful support facts are proved on paper. A shared effective guard G for leaves i,j must dominate Li OR Lj when M=false. If G is nontrivial on that promise, it has at leastfive essential C inputs: when G(0)=0, the five incident singleton inputs force them; when G(0)=1, the only possible rejected promised input is the remaining singleton c, and adding any of the four noncomplementary other inputs changes G back to true, while toggling c from zero changes true to false. If G is true throughout M=false, removing that effective AND increases the positive I-skeleton and cannot break M=true outputs, which were already true.

Also, the private product of guards below the first merge for leaf i depends on allthree incident C variables. For each incident variable x, choose a variable y incident to the other merged leaf j but not i and not complementary to x (two choices, at mostone forbidden). On C=y and C=x+y the shared factors are true and M=false, while Li changes0 to1. This forces private dependence on x. Neither support fact yet accounts correctly for shared ancestors, so neither proves b>=16 or surplus+NOT>=11.

No size-preserving NOT elimination, eight-gate guard extraction, or full circuit lower bound is claimed.
