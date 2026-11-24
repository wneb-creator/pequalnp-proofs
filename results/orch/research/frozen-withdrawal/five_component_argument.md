# Five-output cyclic-component argument (draft, 2026-11-24)

## Exact scope and outstanding formal lemmas

This is a mathematical contradiction for a normalized five-output residual, NOT yet a Lean theorem and NOT the unrestricted 39-gate gap. Assume five distinct Singer lines L_i on13 raw points; allowed monotone fanin2 circuit with at most14 total gates; all five outputs are distinct binary OR sinks, placed after at most9 internal gates; all outputs are band-correct, normal at complement(L_i), and nonordinary. Apply the checked AllFiveCost theorem after every exact-function-preserving normalization, so every final output's capped formal false cost is5.

Normalize constants, unary gates and repeated operands by exact copy/constant propagation without increasing gatecount. Graphs below include all raw vertices and gate-input edges, with multiplicity if needed. Internal weak components partition the used raw vertices. A component C with r raw vertices, g binary gates and cycle rank beta satisfies g >= r-1+beta. A wire belongs to one component and depends only on its raw vertices. A two-wire ancestor union on at most a gates has at most a+2 raw vertices; equality means two tree components.

CHECKED semantic premises already available: each nonordinary band output needs at least8 essential raw points; SharedParent says two outputs sharing one OR parent force each opposite parent to depend on every point of its own line outside the other line; all-five false costs are5. Singer geometry (direct small finite checks/available lemmas): union of5 lines >=11; union of3 lines >=9; union of4 lines >=10; three lines contained in9 points must be nonconcurrent, with union exactly9 and empty triple intersection.

UNFORMALIZED extraction/normalization prerequisites: sink/repeated-operand cleanup with preserved ordinary status; the raw-component graph equality/tree interpretation; tree false-certificate cost <= number of line points; global exact-OR-family gate bound for pairwise-singleton intersections (Tarjan/standard private-core argument); leaf replacement compiler; star/triangle classification of pairwise intersecting component pairs. These must be supplied before calling this a proof.

## Initial component classification

For each root, its two parents lie in either one component (a loop) or two (an edge). Its entire line is contained in that component union by essential dependence. Since every two Singer lines intersect, the five component pairs are pairwise intersecting. They therefore form a triangle or a star; a loop forces a common center. Discard unused components.

If a cross root joins two acyclic components, its whole ancestor graph is a tree; normality supplies a false certificate with distinct leaves contained in its4-point line, hence formal cost <=4. Thus every cross edge touches a cyclic component.

In a triangle, at least2 of3 components are cyclic. The five lines use >=11 raw points, so internal gates >=11-3+2=10. In a star with acyclic center and t total used components, all t-1 leaves are cyclic, giving >=11-t+(t-1)=10. Thus the only survivor is a star with a cyclic center C.

Write c=|C's raw vertices| and G=center internal gatecount, so G>=c. A star using at most2 components already costs >=11-2+1=10; hence there are at least2 leaf components. Every loop line lies wholly in C.

## All leaf parents are globally exact ORs

A leaf output parent h_i belongs to a leaf component D_i. Put T_i=L_i intersect D_i, and R_i=L_i intersect C. Both are nonempty for a cross root: if one were empty, normal global upper forces the opposite parent false and root could be replaced by the other parent, contradicting minimal sink normalization. More directly, a constant-false parent is eliminated in the normalization. Normality/global upper yields h_i <= OR(T_i).

If |D_i|<=4, h_i is exactly OR(T_i): for p in T_i, choose a band-positive assignment whose restriction to D_i is only p, and whose other line points are false. This can be filled to7 true inputs because |D_i minus T_i|<=3. The center parent is false by its global bound, forcing h_i(p)=true; monotonicity gives equality.

Every used leaf has size<=4. If c<=4, every cross output's support>=8 forces its leaf size>=8-c, and two leaves cost at least c+2(7-c)>=10. Thus c>=5. If G>=6, outside-center gate budget <=3, so each leaf has <=4 raw points. If c=G=5 and a leaf has >=5 raw points, it consumes all4 remaining gates; every other leaf is a single raw input and its output has support<=6, impossible. Hence all leaves have size<=4 and are exact OR(T_i).

## Leaf normalization (necessary for formal-cost reasoning)

Exact OR(T_i) semantics alone DO NOT imply formal cost |T_i|, because duplicated/reconvergent certificates may inflate cost. Replace all requested leaf functions by separate direct OR trees. Their target sets satisfy pairwise intersection<=1. The global exact-OR-family lower bound says old leaf component gatecount >= sum_i(|T_i|-1), so this replacement does not increase total gates. It preserves every full output function; singleton repetitions cost0. Reapply AllFiveCost to the rebuilt <=14-gate circuit. Center gates are unchanged. Hence all cross roots still cost5 and their leaf parents now have exact formal cost |T_i|.

The graph component labels used below can remain the OLD components; replacement only disconnects leaves and does not change center gates or which raw points each T_i uses. This is bookkeeping, not a claim that replacement preserves weak-component connectivity.

A cross center-parent cone must now be cyclic: if acyclic, its false certificate at the line complement uses distinct leaves in R_i, cost<=|R_i|; adding the direct leaf gives cost<=|R_i|+|T_i|=4. For a cyclic center-parent cone with s essential raw points, at least s gate vertices occur, so its position among center gates is >=s.

## No-loop star

Let m<=5 be the number of distinct center-parent wires. All are gate wires, since a raw center parent plus a leaf of at most3 target points would make the output ordinary. If two outputs share the center parent, SharedParent forces L_i minus L_j into T_i, so R_i is contained in L_j. Thus each member of a repeated-parent group has |R_i|=1 and |T_i|=3.

The earliest of m center-parent wires occurs by position G-m+1, so its support has size<=G-m+2. Its full output has essential support>=8; hence its T_i has size>=6-G+m. Select this output as one representative of its group. Across the other nonrepresentative outputs there are5-m copies, each with |T|=3. Leaf lower bounds therefore give outside gates >=(5-G+m)+2(5-m). Total >=G+that=15-m>=10. Contradiction.

## Loop star: center sizes and late-parent positions

A loop output needs support>=8, so c>=8. Since G<=9, c is8 or9. Every leaf has <=2 raw points when G=8, and is a singleton when G=9. Thus every cross T_i has size1 or2.

A center-parent wire of a cross output cannot be a parent of ANY other output: otherwise SharedParent forces its opposite exact OR(T_i) parent to depend on3 points of L_i minus L_j, impossible for |T_i|<=2. Thus all cross center-parent wires are distinct and unavailable as loop parents.

Each cross output has support>=8. Its center parent therefore has support>=8-|T_i|. Its cone is cyclic by leaf normalization, so its center-gate position is >=6 when |T|=2, and >=7 when |T|=1.

If c=8, at most2 lines are contained in C (three lines need>=9 points), so there are at least3 cross outputs.
- If G=8, there is at most1 outside gate; at most one cross output can have |T|=2 (two lines cannot both contain the same2-point leaf set). The three cross positions therefore fill6,7,8. Every loop parent is among first5 center gates or raw; two-parent support <=7, contradiction.
- If G=9, all leaves are singleton, and at least3 cross positions fill7,8,9. Every loop parent is among first6. To have support>=8, the union of its parent cones must attain the bound raw<=g+2 with g<=6, hence exactly6 gates/8raws/two tree components. Adding the root gives a tree, so its false cost<=4, contradiction.

If c=9, G=9 and all leaves are singleton. At most3 lines are contained in C (four need>=10), hence at least2 cross outputs. Three cross outputs give the same first6/tree contradiction. The remaining case has exactly3 loops and2 cross outputs. The two cross parent wires occupy two of positions7,8,9. Every loop must use the ONE remaining late wire h, or its two parent cones would lie in first6 and give the tree contradiction. Its opposite parent g_i is therefore among first6 center gates (or raw).

The three contained lines have union9 and are nonconcurrent. All three loop roots share h. For a fixed loop i, SharedParent against each of the other two loops forces g_i to depend on L_i minus L_j and L_i minus L_k. Their union is all L_i because triple intersection is empty. Thus the three early parent cones each contain their full line. Pairwise line intersections join these cones into one connected raw-inclusive subgraph containing all9 points. A connected binary ancestor graph on9 raw points needs at least8 gates, but all these cones lie in first6 center gates. Contradiction.

## Review status

special_status approved initial triangle/star arithmetic, leaf exactness for small leaves, and loop-case position/first6/tree accounting. fresh_proof independently identified the final prefix-rank contradiction. The explicit leaf direct-OR normalization was identified afterward and independently approved by special_status, with the generic subset-family exact-OR lower bound explicitly still requiring formalization. No source theorem yet combines these claims; no unrestricted result is claimed.
