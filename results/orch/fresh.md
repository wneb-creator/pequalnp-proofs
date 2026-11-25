# Fresh full-theorem attempt

Scope: read README.md, CONTRIBUTING.md, exact gap.json, ownership definitions, current global/structural/library notes, and the critical-obstruction/countdown proof in L_meta_2399. No desk, git, publication, or named-file mutations.

## Status

No full proof or counterexample found. No new Lean declaration is proposed for the deliverable. The obstacle remains global sharing between two or more dirty AND gates.

## Routes examined

1. **Global AND cover extraction.** In canonical free-OR top form, each clean AND whose two operands both have singleton supports creates a complete bipartite set of new graph edges. No four-cycle makes that set a star. This does not cover all edges: an edge can be created at a dirty ancestor and inherited through the clean AND, even when an operand has no singleton support. A proof must assign at most one cover vertex per distinct AND across these shared inherited contributions, rather than one vertex per clean output. The C7 four-AND witness in the structural notes rules out demanding that the original gate ownership itself supply that assignment.

2. **Induction by restrictions.** Setting one vertex to zero drops vertex-cover number by at most one, but does not remove an earliest AND with two wide OR supports. Setting a vertex to one removes some ANDs but replaces the target with unary neighbor terms plus a residual graph; the residual cover number can drop by more than one (already on C5). Thus the obvious gate-elimination induction does not establish the desired bound.

3. **Generic normalization of quadratic functions.** Arbitrary monotone quadratic functions do not admit an AND-count-preserving homogeneous normal form in general. The known saturated-graph counterexamples prevent using such a theorem without girth. A subdivision transfer to remove short cycles has no evident savings-preserving construction: the incidence function has fresh edge variables and exactness on independent assignments prevents direct reuse of the code gadgets. Structural_proof independently reached the same obstruction.

4. **Formula unfolding / local distributivity.** Unfolding a shared circuit into a formula cannot use the checked formula lower bound at the original gate budget. At a dirty gate g, the monotone Shannon context has the form (g AND H) OR K. Correctness forces H to block false-positive inputs of g; its other AND gates may share operands and contexts. No argument found that extracts a complete rewritable component with enough input gates to pay for all output interfaces. The existing boundary-count lemma isolates exactly this missing inequality.

5. **Generalizing the small-cover theorem.** L_meta_2399's cover-size-at-most-five bound is a real finite catalogue/countdown proof. Its general critical-obstruction reduction gives a graph on at most 2t vertices, but the concluding AND lower bound still depends on finite enumerations for t<=5. No symbolic induction follows from the obstruction reduction alone.

## Potential next mathematical target

A useful genuinely global statement would be an extraction theorem assigning a vertex cover T to a canonical top-form circuit with |T| no larger than its AND count, together with an independent OR-count lower bound |E|-1. Neither inequality is established here. Even the first needs to handle several dirty cones sharing AND ancestors; local ownership stars and pair-truth constraints are insufficient. Exactness on independent inputs of size three and larger is essential.

## Final targeted common-singleton/component route

For a fixed vertex u, all signals true on singleton u have semantic form u OR H after setting u=0. Their interface to signals false on u consists of AND uses. The existing extraction moves the common u from p mixed-OR source gates to t boundary OR gates, with exact gate saving p-t. Minimality only gives p<=t; neither connectedness nor terminality alone gives the reverse inequality.

A useful semantic observation: if a clean boundary has form (u OR H) AND Q, then Q is false on every independent input avoiding N(u). Otherwise adding u creates an independent false-positive input at that boundary. Consequently the restriction of Q obtained by setting N(u)=0 and u=0 is clean. The obstacle is extracting that restricted clean portion of a shared dirty Q without increasing cost.

Graph structure helps only locally: after deleting u, all edges meeting N(u) form a star forest. N(u) is independent by triangle freedom, and an outside vertex has at most one neighbor in N(u) by four-cycle freedom. This suggests an injection from essential boundary outputs to mixed-OR source gates, but boundaries can use other dirty cones and can have critical edges avoiding N(u). No such injection was established.

Library_route's mixed-support lemma says that a pure-OR support containing at least two neighbors of each of two different centers has no common graph neighbor; any clean top reached through ORs by that support must therefore be centreless. However centreless-reader credit alone cannot pay each incoming dirty cone: an irredundant monotone CNF can have many dirty internal ANDs and a single clean output AND. The |junk| credit for intermediate merges must participate, and fanout prevents naive tree counting.

The general checked budget in L_meta_3760.M1528.prev1 is useful here and does not assume a single dirty gate:

    |E| + #noncentre_tops + 2 #centreless_tops + #junk + #(orN minus lam)
      <= size + |Ustar| + 1.

Thus a genuinely global sufficient target is a vertex cover T satisfying

    |T| + |Ustar| <= #noncentre_tops + 2 #centreless_tops + #junk + #(orN minus lam).

The earlier one-dirty theorem proves a specialized version using forced centers and penalties. I found no general weighted incidence/Hall proof for several interacting dirty cones. Constructing a smaller circuit for the residual Ustar graph would give a possible induction, but removing shared lambda factors is precisely the unresolved operation.

## Lexicographic AND-count / total-size attempt

The P4 obstruction to essential-star peeling is exact:

    (a OR c) AND (b OR d) AND (b OR c)
      = [b AND (a OR c)] OR [c AND d].

The first implementation uses two ANDs and three ORs; the second uses two ANDs and two ORs. Thus minimizing total size among AND minima rejects the unshared five-gate witness. If both initial OR factors are shared externally, retaining them yields an equal-size local repair with two new star ANDs, provided the discarded intermediate AND and the third OR have no external users. This illustrates why another tie-break (e.g. dirty truth-table measure) could help after a global repair is found, but it does not supply the repair under arbitrary sharing.

In canonical top form, a clean source AND immediately has a star essential-edge set: its two pure-OR operands produce a complete bipartite graph, and no four-cycle makes that graph a star. Therefore exposing one clean source AND in a suitable lexicographic minimum would be enough for the proposed vertex-deletion induction. I found neither a proof that one exists nor a counterexample. If all source ANDs are dirty, their shared pure-OR factors again lead to the unresolved component interface count. Minimizing OR count only supplies a contradiction after an OR-saving exchange has been constructed.

## Wegener neighborhood-sum route: decisive interface obstruction

Status: literature-based mathematical argument, not a Lean-checked result. Read on 2026-11-25: Ingo Wegener, *The Complexity of Boolean Functions*, chapter 6 section 6, Corollary 6.1, printed page 166 (PDF page 176), https://web.vu.lt/mif/s.jukna/boolean/blaues_book.pdf . The corollary implies that for a family of Boolean sums whose supports pairwise intersect in at most one variable, AND gates cannot improve the optimal total gate count. No nontrivial OR signal can be shared by two such outputs, so their exact cost is the sum of support sizes minus the number of nonempty outputs.

A size-nonincreasing extraction of **all** neighborhood sums from a graph edge-function circuit is false, even for a connected graph with no triangle or four-cycle. Let G be the incidence graph of K5: its vertices are the five original vertices and ten edge-vertices, and each edge-vertex is adjacent to its two endpoints. This graph has 15 vertices, 20 edges, and girth six.

The graph edge function has a 24-gate circuit. For each of the five original vertices, form the OR of its four incident edge-variables (three OR gates), AND it with the original vertex variable (one AND gate), then OR the five resulting terms (four OR gates). Total: 5*3 + 5 + 4 = 24.

The vector of all 15 neighborhood sums requires 25 gates. The five degree-four neighborhoods require 5*3=15 gates; the ten degree-two neighborhoods require 10*1=10 gates. Their supports intersect pairwise in at most one variable. The cited corollary rules out a cheaper monotone circuit using ANDs, and the support-intersection property rules out sharing any nontrivial OR gate. Thus a universal extraction preserving total size would convert the 24-gate edge circuit into a neighborhood-sum circuit of at most 24 gates, contradicting the 25-gate lower bound.

Each individual neighborhood sum can be obtained by restricting the edge function: set its center to one and all nonneighbors to zero. Triangle freedom eliminates edges within the neighborhood. However these are different restrictions for different centers, so evaluating them simultaneously does not preserve the original shared circuit's gate count. The usual Boolean derivative is also unsuitable: it contains a complement of the center-zero cofactor, while the center-one cofactor alone still contains the residual graph function.

Extracting only the neighborhood sums for a selected vertex cover avoids this counterexample. No cost-preserving extraction with the necessary cover choice and gate accounting was established; that would still require the missing global argument. The obstruction rules out the naive all-neighborhood interface, not the posted theorem.

## Recovery-period global continuation: packing-OR abstraction

No full theorem obtained. The following is a mathematical reformulation and transfer argument, not Lean checked.

For a nontrivial lambda OR support S, the clean top exposing it supplies a center c with S contained in N(c). Choose K to include every such top center (one center per noncentre top suffices). After deleting K, the surviving support S minus K is independent and every remaining vertex has at most one neighbor in it: triangle freedom gives independence, while two neighbors together with c would create a four-cycle. Equivalently its vertices have pairwise distance at least three. Supports attached to different centers have intersection size at most one.

This suggests granting ORs of distance-two packings as free inputs when studying the residual graph. Supports assigned to different centers intersect in at most one vertex, but distinct supports assigned to the same center can overlap in several vertices. Therefore reducing to a linear oracle family requires an additional selection or grouping argument with cost preservation; it does not follow automatically. There is also a semantic caveat: lambda wires can OR in dirty AND signals in addition to their primary support. Those signals entered through charged mixing gates, but a precise contraction preserving this accounting is still needed. A theorem only about pure-OR packing oracles would not automatically justify that contraction.

A hypothetical cost saving with a **linear family** of such oracles transfers to a genuine counterexample to the formula-size lower bound on an augmented triangle/four-cycle-free graph. Suppose G has m edges and cover number tau, and a monotone fan-in-at-most-two circuit computes its edge function with s paid gates when z_i=OR(S_i), |S_i|=k_i>=2, are free. Assume every S_i is a distance-two packing in G and |S_i intersect S_j|<=1 for i!=j. Add for every i a new center c_i adjacent to S_i and to two fresh private leaves. Call the result G'.

The augmentation preserves absence of triangles/four-cycles. A triangle through c_i would use an edge within S_i. A four-cycle through one new center would require a common neighbor of two S_i vertices. A four-cycle through two new centers would require two vertices in S_i intersect S_j. Private leaves lie on no cycle.

Every minimum cover of G' contains every c_i: omitting one forces both private leaves into the cover, and replacing those leaves by c_i reduces its size. Removing all c_i then leaves a cover of G; conversely a minimum cover of G together with all c_i covers G'. Therefore tau(G')=tau(G)+r, where r is the number of oracles, and |E(G')|=m+sum_i(k_i+2).

Build each z_i with k_i-1 ORs, extend it by its two private leaf variables with two ORs, AND with c_i, and combine that star term with the original circuit output using one OR. The added cost is k_i+3 per oracle. Consequently the constructed circuit has size

    s + sum_i(k_i+3),

while the formula upper-bound expression for G' is

    m + tau(G) - 1 + sum_i(k_i+3).

Thus any strict oracle saving s < m+tau(G)-1 survives unchanged. This shows that the linear-family packing-oracle lower bound is another form of the difficult global formula-size bound, rather than an immediate consequence of the Boolean-sum theorem. Applying it to every lambda wire would additionally require the unresolved same-center grouping and dirty-atom contraction steps described above. It does not establish equivalence to the posted star-profile theorem, and no counterexample was found.

A further extraction caveat: even full neighborhood sums restricted to a minimum cover can overcount. For P4=a-b-c-d, cover {b,c} has full sums a OR c and b OR d, costing two OR gates, but |E|-|T|=1. The four-gate star circuit assigns bc to b and uses only the owned-neighbor sum a OR c, with c's owned leaf set {d}. Any sharp extraction therefore needs an edge ownership orientation as well as a cover selection.

Source check during continuation: Jukna, *Disproving the Single Level Conjecture*, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf (read 2026-11-25), explicitly distinguishes total size and AND count; Theorem 2.4 gives an AND-count separation using saturated matching extensions. Thus unrestricted AND-count-preserving single-level normalization is ruled out, not only total-size normalization. This is a primary-source mathematical claim, not a Lean check. It does not by itself refute the weaker existence of one clean source AND: in a general graph such a source can own a large biclique, whereas no four-cycle would force a star.

A scoped alternative to essential-star peeling: a vertex restriction may permit absorption of an AND even when its original essential-edge set is not a star. In the P4 expression, setting a=0 gives g=c AND (b OR d), after which g AND (b OR c)=g. This deletes the second AND by replacing it with one operand. A universal existence theorem for such a vertex/redundant-AND pair would imply the AND-count cover bound by induction, but no such theorem was established here.
