# Fresh Petersen proof attempt

Status: partial mathematics only. No proof of L-meta-2590, no 19-gate counterexample, and no Lean theorem claimed. The argument below isolates a special case of a possible 19-gate circuit.

## From circuit fanout to a read-two formula

Trim dead wires and simplify constants, copies, repeated-operand gates, and invalid forward reads first. A normalized connected binary circuit with 10 essential inputs and s gates has 2s incoming gate incidences. Its s-1 nonoutput gates each have at least one outgoing incidence. If every input has fanout at least two, then

    2s >= 20 + (s - 1),

so s >= 19. At s=19 equality forces every input to have fanout exactly two and every nonoutput gate to have fanout exactly one. Thus this special case is a 20-leaf monotone formula in which every variable occurs exactly twice.

The rest of this note rules out an AND root for such a read-two formula. The root-OR case remains open here. A general circuit may instead have an input of fanout one, which this argument does not handle.

## Basic formula facts

All formulas in this note are constant-free binary AND/OR formulas. Their occurrence counts concern the unfolded formula tree.

1. The graph of two-variable prime implicants of a read-once monotone formula, after removing its singleton prime implicants, is a disjoint union of complete bipartite graphs. Indeed an OR combines disjoint variable supports; at an AND, a two-variable implicant must choose a singleton from each child. A read-once child cannot also contribute a two-variable term using the same variables. This also follows directly by induction on the formula.
2. If a monotone function accepts every edge pair of a cubic graph and has singleton set S, then every vertex v not occurring in the formula must satisfy N(v) subset S. For any edge vw, if v is absent, acceptance on {v,w} is acceptance on {w}.
3. Petersen is connected and nonbipartite; deleting any one vertex leaves a connected nonbipartite graph. It is cubic, triangle-free, C4-free, and has no distinct vertices with the same neighborhood.

## AND root: neither child has a singleton

Let the root be A AND B and suppose neither child has a singleton implicant. Both children accept every Petersen edge pair. Fact 2 forces every variable to occur in each child. Since each variable occurs at most twice in the entire formula, each child is read-once. Fact 1 contradicts connected nonbipartite Petersen being contained in its quadratic-prime graph.

## AND root: both children have singletons

Let the singleton sets of A and B be S and T. They are disjoint because the output has no singleton. Every cross pair in S times T is an edge, so C4-freeness forces one of the sets to have size one; write T={v}. Then S is a nonempty subset of N(v), of size at most three.

B contains every variable: no cubic vertex has its neighborhood contained in {v}. If |S| is at most two, A also contains every variable. Both children are therefore read-once. Setting v=0 in B leaves a read-once formula without singleton terms that accepts every edge of Petersen minus v, contrary to Fact 1.

If |S|=3, then S=N(v). The only variable A can omit is v, since Petersen has no equal neighborhoods. Thus every variable other than v occurs exactly once in B. Set v=0 in B and simplify: the resulting formula is read-once, has no singleton terms, and accepts every edge of Petersen minus v. Fact 1 gives the same contradiction.

## AND root: exactly one child has singletons

Write A for the child with no singleton, and B for the other child. A contains all ten variables. Therefore B is read-once, since the whole formula is read-two.

Let T be the variables absent from B, R its complement, and S the singleton set of B. Then T is independent and N(T) is contained in S, by Fact 2. Setting all T variables to zero makes A read-once and leaves it without singleton terms. Its quadratic graph Q is a disjoint union of bicliques and contains Petersen restricted to R. Consequently:

- every connected component of Petersen restricted to R is bipartite;
- completing each such component across its bipartition cannot add a nonedge incident to N(T). Such a pair would be true in A and, because its endpoint belongs to S, true in B, contradicting the target function.

T cannot be empty: otherwise A itself is read-once and must accept connected nonbipartite Petersen without singleton terms. Enumerating the independent nonempty T gives only five possibilities satisfying the two necessary conditions above:

    {0,2,8,9}, {0,3,6,7}, {1,3,5,9},
    {1,4,7,8}, {2,4,5,6}.

These are the five maximum independent sets. In each case R=N(T) consists of six vertices inducing three disjoint edges. Since S contains N(T), B has all six R variables as singleton implicants and no other variables: B is their OR. All R variables occur exactly once in A, and all T variables occur at most twice.

It remains to apply the following matching-baseline observation.

## Matching-baseline occurrence lemma

Let U be a variable set occurring once per variable in a constant-free monotone formula A; let W contain all other variables. Suppose setting W=0 makes A exactly the edge function of a perfect matching on U, and A has no singleton implicants.

Fix u in U, with matching partner u'. The assignment {u,u'} makes A true. Every AND ancestor on the path from the unique u leaf to the root must have a sibling subtree that accepts this assignment. That sibling cannot contain u. It must contain u', because a constant-free monotone formula is false when all its inputs are false. The sibling subtrees of distinct AND ancestors are disjoint, while u' occurs once. Thus u has at most one AND ancestor. It has at least one because otherwise its path consists only of OR gates and u would be a singleton implicant. Therefore it has exactly one.

The unique AND ancestors for u and u' coincide. Different matching edges have different such AND nodes: otherwise the corresponding singleton leaves in the two children would create extra cross edges. These nodes cannot be nested, because that would give an endpoint two AND ancestors. Thus they are pairwise disjoint subtrees.

If A accepts {u,w}, where w is in W, the child opposite u at this matching AND must contain an occurrence of w. Distinct u-neighbors require distinct occurrences: the two endpoints of one matching edge require opposite children, and endpoints of different matching edges require disjoint subtrees. Hence the number of U-neighbors accepted with a fixed w is at most the number of occurrences of w in A.

For the Petersen configuration above, U=R and W=T. A with T=0 is the three-edge matching because B is the OR of R. Every t in T has three neighbors in R, so the lemma requires at least three occurrences of t in A. The read-two bound allows at most two. This is a contradiction.

## Current conclusion and limitation

The preceding cases rule out an AND-rooted read-two monotone formula for the Petersen edge function. They do not rule out an OR-rooted read-two formula, and they do not prove a lower bound for circuits with an input of fanout one. The finite independent-set enumeration has only been checked in Python, not in Lean.

## Additional root-OR observations before lease pause

Flatten a root OR into AND-rooted blocks, and discard any block accepting no target edge: because the target is a quadratic monotone function, all of that block's accepted assignments are already accepted by some edge-accepting block.

If a productive block has no singleton in either child, every endpoint of every edge that the block accepts occurs in both children. This exhausts its two global occurrences. It can occur in no other block, so all three incident Petersen edges must be accepted in this block. Connectivity propagates until the block accepts all fifteen edges. This reduces to the excluded full AND-root case. Therefore every productive block of a remaining read-two candidate has a singleton in at least one child.

A further potentially useful setup, not a completed proof: in a leaf-minimal formula, every leaf occurrence must participate in some proof of a target edge; otherwise replacing that occurrence by false and simplifying preserves every target edge and hence the full function. For a productive block A AND B with no singleton in A, A contains all endpoints of edges accepted by the block. Therefore every variable occurring in B also occurs in A, so B is read-once, and every B variable exhausts its two global occurrences inside this block. All Petersen edges incident to those B variables must consequently be accepted by the same block. This reduces such blocks to exclusive centers and a boundary of variables shared with other blocks, but no complete charging argument was obtained.

Work paused at the parent's instruction after the confirmed lease HTTP410 at 15:22 UTC. No further development on this gap was undertaken after that instruction.
