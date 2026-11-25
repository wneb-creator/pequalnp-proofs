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
