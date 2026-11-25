# L-meta-2962 charging route

## Algebraic target

Let D be the union of accepted edge sets of maximal cores and U the union of their cones. A sufficient stronger inequality is |D| + tau(D) <= |U| + mc, since a cover of G-D together with a cover of D covers G. Structural agent is handling cover algebra.

Alternative sufficient inequality: for any fixed maximum matching M of the bipartite graph G, |D| + |M intersect D| <= |U| + mc. The residual graph contains M-D, so tau(G)-tau(G-D) <= |M intersect D|. This needs matching/cover equivalence, likely heavier than a direct cover certificate.

## Main obstruction

Summing one-core bounds overcounts shared gates. A proof must charge overlap against repeated edges or saved cover vertices, or choose an ordering where each newly added core pays its newly added edge/cover contribution from newly exposed gates. No available checked theorem handles this overlap directly. Such an incremental assertion is not yet verified.

The lift-fixed condition constrains only live gates. Dead maximal cores can have arbitrary internal lift sites, so arguments cannot apply fixed-point normalization separately inside every core.

## Useful finite example

Counterexample agent found a tight one-core path example: e=d AND b; s=b OR c; t=a OR e; root=t AND s. It accepts exactly edges ab, ac, bd and has |D|=3, tau(D)=2, |U|=4, mc=1. The root rereads b on edge bd. The internal OR lift site is permitted if this core is dead and the circuit has an independent exact output. Thus no margin stronger than the stated bound is available uniformly.

## Nearby checked counterexamples

L_meta_2969 refutes the companion outside-core count. L_meta_3444 refutes its private-cone correction. L_meta_3446 refutes the private-cone version of the core-cover bound. Full cone cardinality in our statement is essential.

## Primary source checked

Read 2026-11-25: Stasys Jukna, Disproving the Single Level Conjecture, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf, section3.5. The K2,2-free |E| lower bound stated there applies to single-level monotone circuits; it uses limited sharing of OR sums. The paper does not supply our general circuit bound. Its separating examples use saturated, nonbipartite extensions, so do not directly refute this task.

## Lean partial

CoreStructure.lean contains reused wire-evaluation helpers from L_meta_3653 and new core_op_and / maximal_core_op_and lemmas. They use only the AO2 model and graph simplicity, no lift or no-four-cycle hypotheses. Compile passed (exit 0, warnings only); full output in /tmp/oec/pequalnp-pilot-71/lemma-search/core-structure-build.log.


## Strong obstruction: the posted statement already implies an edge-count lower bound

This is a mathematical reduction sketch, not yet formalized in Lean. Let H be any nonempty bipartite C4-free graph, and let A be an arbitrary AO2 circuit computing its exact edge function F. Prune unused gates; write m for its size. Let T be a minimum vertex cover of cardinality t >= 1.

1. Append a binary OR tree z on the inputs in T, costing t-1 gates (or use its sole input when t=1).
2. Append r = F AND z, costing one gate. Because T covers H, r still computes F.
3. r is a core: its F operand is implicant and its z operand is not (z accepts a singleton); every proof tree on an accepted edge includes both endpoints through F, then one endpoint of T through z, so at least one endpoint is reread.
4. Every old gate lies in r's cone after pruning. Hence r is the only maximal core in this component. Its gamma edge set is E(H), and its cone has m+t gates.
5. Make this entire component dead and append a separate canonical star-cover circuit for F as the actual output. The canonical component is lift-fixed and contains no cores: each accepted edge has a read-once proof. This makes the combined circuit satisfy the posted lift-fixed hypothesis, because dead lift sites are ignored.
6. Thus the combined circuit has D=E(H), U of size m+t, mc=1, and the residual graph has empty minimum cover. The target inequality reduces to |E(H)|+t <= m+t+1, or m >= |E(H)|-1.

For projective-plane incidence graphs, this entails a superlinear lower bound in the number of inputs. This deduction explains why a straightforward cone-sharing argument would be unexpectedly strong; the lift-fixed hypothesis cannot make the dead-core case easier.

## Literature check supporting the obstruction

Read 2026-11-25: Jukna, SIAM Journal on Computing 36(1) (2006), author PDF https://web.vu.lt/mif/s.jukna/ftp/single1.pdf, section8 (PDF page17), Problem8.2 explicitly asks for a superlinear monotone-circuit lower bound for an explicit quadratic Boolean function. The discussion distinguishes known superlinear formula bounds from the unrestricted circuit problem. Section3.5's K2,2-free edge bound is only for single-level circuits.

The 2005 primary preprint https://eccc.weizmann.ac.il/report/2005/021/download/ says the same in Problem24 and immediately preceding discussion of explicit K2,2-free bipartite graphs. This is a historical status check. Current2026 status is UNVERIFIED: targeted searches did not find an authoritative recent resolution or survey confirming that the problem remains open. No claim that the posted statement is false follows from this obstruction.


Independent mathematical sanity check: agent single_core reviewed the dead-wrapper reduction and found it sound for nonempty H, contingent on formalizing pruning and the ReadK proof-tree semantics. In particular, the canonical live output adds no core, while every old core lies below the new root. No Lean verification of the whole reduction is claimed.

The obstruction already uses one maximal core: arbitrary DAG sharing remains inside its cone. Disjointness between different maximal core cones does not permit replacing a circuit by a formula without charging duplicated shared gates.
