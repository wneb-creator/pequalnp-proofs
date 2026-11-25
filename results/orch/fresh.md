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
