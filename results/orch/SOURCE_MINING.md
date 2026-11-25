# Source mining for L-meta-1772

Reviewed upstream sources locally; references below are source blocks to adapt under the target auxiliary namespace, not additional allowed imports.

## Directly reusable exchange infrastructure

- `lean/PEqualNP/Outside/L_meta_3297.lean` (689 lines): arbitrary fan-out factor substitution. Adapted unchanged except names into `lemmas/factor_substitution_route.lean`, namespace `PEqualNP.Outside.L_meta_1772_aux.factorSubstitution`, helper lemma `exchange` inside the matching auxiliary namespace. Requires AO2, AND c=a∧b, reader-specific choice sigma in {a,b}, pointwise absorption at each frontier AND, consistency when OR paths merge into one frontier input, output outside c's OR-closure, and c live. Concludes unchanged gate functions outside that closure and liveSize decrease by at least one. Geometry must establish these hypotheses; no graph/girth or ownership conclusion is hidden in the source. Compiled exit 0; frozen for review/push. Complete log `/tmp/oec/pequalnp-pilot-77/factor-substitution-route-build-2.log`.
- `L_meta_3453.lean` (172 lines): generic reader-dependent substitution transport. Prefix lines 1-110 supplies wire recursion; `wire_relation` lines 112-154 transports any reflexive/transitive gate-compatible relation if each replacement earlier than the substituted gate and related to its original value. Final theorem specializes to underapproximation and equality. Useful for different replacements at separate readers.
- `L_meta_3720.lean`, `same_off` lines 241-274 and `mono_off` lines 289-313: same-length gate-list replacement at one gate, propagating equality or implication to all wires. Prefix lines 1-240 supplies recursion/AO representation. This directly supports replacing e∧(a∨d) by e∧a while preserving all graph-edge pairs and underapproximating pointwise, independently of fan-out.
- `L_meta_3710.lean` (334 lines), final theorem line 219: if AND g=a∧b in an AO2 graph circuit has b true on singleton v and on every singleton neighbor of v, redirect every read of g to a and retain the graph function. No triangle-free/no-C4/bipartite assumption. Uses adding v to an edge-free input. The theorem leaves the output unchanged, so g need not become unused if g is the output; deletion needs output exclusion or an additional minimality argument. It does not itself delete g.

## Canonicalization and pruning

- `L_meta_3720.lean`, final line 761: for any function with AO2 implementation, obtains an AO2 minimum implementing it, lift-fixedpoint, no AND operand below the output, and all gates live. Does not claim to preserve minimum junk, or TopForm simultaneously. Its `lift` lemma lines 447-560 is a possible stronger normalization source if needed.
- `L_meta_4279.lean` (624 lines), main lines 524-618: after replacing gate k by false, and choosing finite sample X, constructs a monotone underapproximation of the original circuit that equals the modified circuit on X, with size bounded by the number of remaining gates live on some sample in X. It could pay for reattaching lost edges. No adaptation made without a counting plan.
- `L_meta_7602.lean` (390 lines): an essential gate at input x is live at x. It does not prove carriers normalize.
- `L_meta_8415.lean` (365 lines), final 363: assuming n > 0, a minimal gate true at x while the output is false has a downstream AND boundary with a true operand and false gate. This supplies a killing AND path, not repair.

## CarriedProduct / ReadK / SharedOr outcome

Three current L_ proof files reference CarriedProduct or its live/carrier predicates: L1603, L4279, L7602. The reduction files R_meta_4281_1, R_meta_4281_261, and R_meta_2434_1 also reference it. No current Outside file references SharedOr or ReadKJoin's predicates (`IsSharedOr`, `HasSharedOr`, `sharedOrCount`, `joinsInTree`, `joinsInReadKTree`, `isJoin`).

- L1603 assumes every AND is false on every singleton, then every graph edge has a carrier and its carrier operands split the singleton endpoints. It assumes the sought difficult normalization property.
- L2230, L2231, L2235 count read-once graph edges and cover them by top stars. L2237/L6369 assume the entire circuit is ReadK 1 before deducing the |E|+vertex-cover lower bound.
- L7344 converts arbitrary circuits whose prime implicants have size two into ReadK 1 circuits, but only with size+1 <= 3*(old size + number of bad prime pairs +1). This is not a minimum-preserving conversion.
- SharedOr is a multioutput line-conjunction notion, so it would need translation before use for single-output graph functions.

## Important restricted results, not general bridges

- L3653: bipartite + no C4 + fixedpoint/irredundancy/all-live + exactly ONE dirty AND with a true singleton gives a no-larger all-AND-below-output circuit.
- L3700: bipartite + no C4 + least AO + lift-fixedpoint + no AND operand below output + all gates live + exactly ONE dirty AND + all ANDs singleton-false gives a no-larger AND-antichain implementation.
- L8725/L3760: bipartite + no C4 + least AO implies junk.card != 1. Bipartiteness is additional to our triangle-free/no-C4 statement; odd cycles prevent direct use.
- L7895: exactly two dirty gates yields a cost alternative or a rigid single-reader chain. Not arbitrary dirty fan-out.
- L3017: bipartite singleton-cone cleanup with private OR cone, restricted AND readers, and lost-edge filter; its hypotheses do not cover general shared chains.

Full bounded-search inventories and parsed theorem statements remain under `/tmp/oec/pequalnp-pilot-77/mining-*.json` and `mining-*-files.txt`.
