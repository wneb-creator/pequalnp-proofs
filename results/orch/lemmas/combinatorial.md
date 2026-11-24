# Combinatorial strategy for L-meta-5349

2026-11-24. This is exploratory reasoning, not a Lean-checked result.

## Established mathematical observations

For a witness e write e={u(e),v(e)}, t(e)=(a(e),b(e)), and B(e)=side(C,a(e),1-b(e)).

1. If t(e)=t(d), B(e) is nonempty, and v(e)=v(d), the final disjointness hypothesis gives e=d. Thus v is injective within every noncentreless oriented-top fiber.
2. Every cross-pair between A=side(C,a,b) and B=side(C,a,1-b) is a graph edge. Girth >=5 implies either |A|<=1 or |B|<=1. Hence |B|>=2 forces every selected u in the t fiber equal. The rich t fiber then supplies >=3 distinct other endpoints v.
3. For a fixed v, the nonempty B(e) are pairwise disjoint. Choosing w(e) in B(e) gives distinct length-two paths v-u(e)-w(e); these are not enough by themselves to bound the number of witnesses by circuit gates.
4. B(e)=empty makes the disjointness hypothesis vacuous. Any direct proof using it needs an explicit centreless case.

## Existing useful proofs

- L_meta_3805 gives a 54*(C.size+1) bound for the whole single-junk witness family when all junk gates form an ancestor antichain. It has ~1477 lines. General OR-DAG frontier counting and neighbour-cover machinery are inside.
- L_meta_3807 treats the double-junk family under the same antichain assumption.
- Root identified L_meta_4322 as a stronger raw-exposed case without the antichain requirement; do not duplicate its raw-versus-nested cut.

## Obstacle

Four rich label fibers plus the side-disjoint geometry alone do not force emptiness or a linear bound. High-girth projective-plane incidence graphs admit abstract witness labels satisfying these conditions with arbitrarily many edges per oriented-top label. Circuit semantics/minimality must do real work.

## Finite abstract checks

Projective-plane incidence graphs over prime fields; reserve a perfect matching, keep all other edges, use top A={u}, B={matched neighbour}, and one constant junk label. This checks ONLY label/graph geometry, not realizability by a least circuit.

- q=3: vertices=26, selected edges=39, oriented tops=13, each endpoint/top fiber=3, one junk label, disjoint opposite singleton sides verified.
- q=5: vertices=62, selected edges=155, oriented tops=31, each endpoint/top fiber=5, one junk label, disjoint opposite singleton sides verified.
- q=7: vertices=114, selected edges=399, oriented tops=57, each endpoint/top fiber=7, one junk label, disjoint opposite singleton sides verified.

## Candidate reduction needing independent truth checks

A local obstruction would be: every nonempty four-rich witness core satisfying the posted side-disjointness contains an edge with a raw-exposed junk witness. Combine the already checked raw count L_meta_4322 (27*size), remove all raw edges, then peel low fibers (cost at most twice the total role-label count, at most 10*(size+1) once support<=size+1 is known). A surviving nonempty core contradicts the obstruction. This yields a 37*(size+1) bound and turns the hard piece into an existence statement without a counting constant. It is not proved here; absence of a counterexample is not evidence of truth. Must check nested-junk examples before submission.

Circuit_geometry independently sharpened the fixed-v picture: any w in B(e) is private among the u endpoints of that v fiber, because w=v is excluded by Ustar and another selected u adjacent to w would make a 4-cycle. Bottommost true raw junk can be found by L_meta_4005, but its transfer to top context is blocked by v-only masking gates.

## Completed reduction draft

`results/orch/lemmas/R_meta_5349_48.lean` compiles with pinned Lean 4.36.0 (lake env lean, exit 0). It uses exactly three independent proposition hypotheses:

1. Graph support bound, already checked as L_meta_2074.
2. Raw exposed witness bound 27*C.size, already checked as L_meta_4322.
3. Every nonempty four-rich core satisfying the posted semantics/disjointness contains a raw exposed edge. This is the new unproved obstruction. Its conclusion allows arbitrary endpoints/orientation and arbitrary top/junk witness, weakening it as far as practical.

Proof removes all raw-exposed graph edges, peels fibers of size at most two, pays at most 2 per erased role label (two vertex labels + two oriented-top labels + one junk label, budget 5*(size+1)), then invokes obstruction to force survivor empty. Concludes exactly posted statement using witness constant 37. First compile produced only the posted implicit instance x4 unused-variable warning. Full log is `/tmp/oec/pequalnp-pilot-48/reduction-draft.log`.

Counterexample stress reported by root: Heawood nested circuit with 55 gates has raw exposed set empty and meets all other assumptions except leastness; standard 27-gate circuit shows it is not least. Thus leastness is essential to the new obstruction, which is a semantic normal-form claim, not a pure combinatorial theorem.

## Weakened local-degeneracy version

`R_meta_5349_48_v2.lean` compiles,160 lines. The third child now asserts existence of a uniform d such that every nonempty four-rich core has either a raw exposed edge or some role fiber of size at most d. This avoids the unsupported fixed threshold two obstruction. The theorem removes all raw edges and recursively deletes one whole fiber: nonrich cores have a fiber of size at most two; rich ones invoke the new local child. Each step erases one occupied label and costs at most d+2 edges. Final constant is 27+5*(d+2).

The child is local: it asks only for one edge-bearing removable fiber in each core. Existing PR10461 instead assumes a global linear cardinal bound for the entire raw-free rich core. Our proof supplies the missing global induction from this stronger-structured but smaller local task.

The two already-checked support/raw lemmas are retained as independent hypotheses because the desk allows only PEqualNP.Defs as project import. No implication between hypotheses is assumed.

## Cleanup candidate V3

`R_meta_5349_48_v3.lean` compiles,147 lines (V2:160). It drops the rich-fiber premise from the existential-d local child. This has equivalent mathematical burden: a rich-only version with d extends to arbitrary nonempty T using max(d,2), since a failure of richness directly supplies an occupied role fiber of size at most two. The reverse direction is restriction. Thus the stronger pointwise statement under an existential constant does not impose a stronger existence claim.

The induction now invokes the local child directly at every nonempty residual, pays d per erased role label, and concludes with constant27+5*d. It retains all posted semantic, leastness, top-form, and opposite-side-disjointness assumptions in the local child. The original conclusion is unchanged byte-for-byte.

## Continued direct-proof attempt after reduction compiled

Minimal-label strategy: in a raw-free family, an assigned junk gate g has a smaller true AND ancestor on its witness pair; bottommost is internally raw (L_meta_4005). Choosing minimum assigned g only puts this ancestor outside the image of the chosen g labels. AND masks destroy the OrReaches relation from the top operand, so one cannot simply reassign the witness to the smaller gate. Shared smaller ancestors do not provide an injection to role labels.

Singleton-support split: let S_g={v | g(1_v)=true}. Any assigned u is in wmax(g), so every v in S_g is adjacent to u. If S_g has two distinct vertices, no four-cycle implies all assigned u for g coincide. If S_g={v0}, then for any v!=v0, at most one u adjacent to v can occur among all assigned gates with this singleton center, again by no four-cycle. These are rigorous graph consequences, but they do not bound fibers by themselves.

The unresolved semantic issue is circuit reuse outside T. Replacing a masked junk gate by a simpler operand may preserve all chosen one-sided top contexts while changing other readers, notably tops with two junk operands. Leastness applies to a replacement preserving the complete graph function, not merely the selected witness family. A proof of the local-degeneracy child must control those other readers or use a transformation that is safe for them.
