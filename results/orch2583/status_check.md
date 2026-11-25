# L-meta-2583 independent source review

Updated 2026-11-25T14:46:29.442892+00:00

## Exact definitions

`PEqualNP.ReadK.IsReadK n C k` quantifies over each prime implicant S of C. It requires ONE proof tree with all leaves in S and each variable read at most k times jointly. This is not global fanout-one, not a read-once formula, and not separate per-variable minimum counts. For an incidence graph every prime implicant is an incident point-line pair, so read1 asks for a tree containing each endpoint once. `readVectors` caps vector coordinates at k+1; OR unions possible vectors and AND adds them.

`TopForm.IsAO2 n C` (Defs/TopForm.lean:82) requires AND/OR only, every input wire earlier, and exactly TWO inputs at each gate. It disallows constants and unary gates. `Monotone2` instead allows fan-in at most two and hence constants; converting between them needs proof. No logical loophole in the target definitions was found.

## Existing checked source

- `L_meta_7684`: given any bipartite edge set E and a vertex cover A∪B, constructs an AO2 read1 circuit of size at most E.card+A.card+B.card−1. File49,651 characters. This proves the standard plane read1 upper bound N*(q+2)−1 after taking all points.
- `L_meta_4897`: C4-free bipartite graph read1 circuit gives a cover A∪B with E.card+A.card+B.card≤C.size+1. File94,218 characters.
- `L_meta_7639`: C4-free square bipartite graph with perfect matching, read1 circuit implies E.card+n≤C.size+1. File95,442 characters. Useful for refutation if a smaller general circuit is found.
- `L_meta_2237` / `L_meta_6369`: graph form of the read1 vertex-cover lower bound.
- `L_meta_6579`: circuits whose AND operands are pure point-side and pure line-side OR networks are read1.
- `L_meta_7344`: repairing all quadratic prime implicants to read1 has a factor-three plus unread-implicant-count bound; insufficient for size-preserving replacement.
- Existing `L_meta_2797`/2799/2995 are refutations of different oversized read2 claims, not L-meta-2583. No checked L_meta_2583 exists in the local checkout or exact-path history.

## Complete GitHub open-PR census

10 GraphQL pages,905 open PRs, final page hasNextPage=false; response JSON shape verified. Complete raw output and stderr retained under `/tmp/oec/pequalnp-pilot-103/2583-open-pr-pages.*`. Exact target has one open PR: https://github.com/open-goat/pequalnp-proofs/pull/13723 (the configured upstream API redirects to this owner). Desk initially reported zero open PRs, so that field was stale.

PR13723 is from the same user fork, branch pnp/pr-L_meta_2583, head80e523b7ee77818257e60fbd35611ba975d43a4c, adds exactly the target file. It has no build status and an intake comment: **REFUSED before any build: the theorem must stand at the top level, last, written with its full name**. Inspection confirms the file is a partial result, not a complete proof:7090lines,333,774bytes, ending in a namespace-local unrestricted lower bound3*N−1≤C.size rather than the requested theorem. Therefore this PR is not evidence that the gap has been solved. We have not compiled that source.

Saved public source `/tmp/oec/pequalnp-pilot-103/2583-pr13723.lean`, SHA256 01825179e85adb345b8c0a239845547a995c463e6a09d54ce935a209f6ab74ad.

## Reusable partial architecture in PR13723

- line1216: `plane_read_one_upper`, read1 circuit size≤N*(q+2)−1.
- line3395: `read_one_plane_lower`, matching lower bound for every read1 plane circuit.
- line3416: `read_one_replacement_iff_size`, conclusion of our gap equivalent to N*(q+2)−1≤C.size. This identifies the exact unrestricted lower bound needed.
- line4300: `exists_least_lift_normal`, picks minimum-size circuit with lift-to-top OR normalization, preserving size and function.
- line4555: `normal_no_imp_and_top_form`, conditional TopForm route.
- lines4864 onward: explicit27gate Fano star circuit and pair-read certificate.
- line6631: generic neighborhood/cover lower bound.
- line7075: `unrestricted_plane_size_lower`, only3*N−1≤C.size. Thus it remains short by N*(q−1) of the target, even q=2.

The checker refusal is not fixed merely by renaming its final lemma: its conclusion is strictly weaker than the posted target.

No desk, git mutation, push, or proof edits performed by this agent.

## Checked block extraction and lifting sources

- `L_meta_4293` (12,600 characters): one `CircuitMoves.Lift` preserves IsAO2, valid output, exact size, and function.
- `L_meta_4295` (26,835 characters): reaches a lift fixed point where an OR gate with a below-output internal operand has both operands below-output.
- `L_meta_7372` (34,199 characters): given the lift normal form and no input below output, constructs an IsAO2 core D and list B of operand pairs. Every core gate has an input making it true while the original target is false. The target is exactly OR over conjunctions of each pair of core wire values, and D.size+2*B.length≤C.size+1. This is a checked block/core decomposition with precise cost accounting.
- `L_meta_7649` (42,541 characters): for a C4-free bipartite target, if every gate not below-output is OR and all its inputs are not below-output, obtains a list of stars covering exactly all incidences, with sum(star leaf counts)+number of stars−1≤C.size. This closes the clean-core case, but its OR-only assumption is exactly what cannot be assumed for nonstar blocks.
- `L_meta_4742` and `L_meta_4747` give strictly smaller replacement circuits for a unique non-below-target AND under additional detailed reader/edge conditions. They do not eliminate unrestricted multiple junk gates.

Full final statements for these six files are saved in `/tmp/oec/pequalnp-pilot-103/2583-lift-statements.txt`. Parent and lower_bound agent informed.

## Expanded checked-source census 2026-11-25T14:50:21.480756+00:00

Searched115 plane-expression source candidates (91 circuit-related final declarations),139 girth/no-four-cycle candidates (99 circuit-related finals), and135 edge-cardinality candidates. Complete extracted statements retained as `/tmp/oec/pequalnp-pilot-103/2583-{plane,girth}-bound-statements.txt` and `2583-edge-or-statements.txt`. No unchecked conjecture was silently promoted to a theorem; several old L-prefixed files are implications from large unproved premises.

Substantive new results:

- `L_meta_5351`: for q≥200, exact plane circuit hypotheses imply349*N≤100*C.size. Its actual assumptions are AO2, correct on incident pairs, and rejecting false inputs with≤q line inputs; exact computation implies these. This is a genuinely sharper unrestricted large-q bound than3N−1. Source161,968bytes/3204lines (155,896characters). Still far below N*(q+2)−1.
- `L_meta_8805`: the general3N≤C.size+1 bound for allq≥2 is already checked under similarly weaker input conditions.
- `L_meta_3760`: leastAO circuits for bipartite C4-free graph targets never have exactlyone junk gate. Therefore after the zero-junk sharp star case, every obstruction needs at leasttwo junkANDs. However this source is513,510bytes/10,039lines, nearly the512KiB limit by itself; cannot blindly combine whole file with other helpers.
- `L_meta_4767` (49,962bytes/1022lines; duplicated by larger L8149): sharp |E|+vertexcover≤size+1 holds if every AND is either BelowF or accepts at mostone actual undirected edge-pair. It permits junk that is useful to onlyone edge. Thus any obstruction also needs a junkAND accepting≥2distinct useful edge pairs. This is more permissive than the allANDbelow case L1407/L7848.
- `L_meta_599` and duplicateL4837 give ORcount≥|E|−1 only when EVERY induced subgraph satisfies induced-edges≤vertices (pseudoforest condition) in addition to no4cycles. That extra condition fails full plane graphs. No unconditional ORcount≥|E|−1 theorem was found.

Important failed general charging claims:

- `L_meta_2969` refutes a maximal-core charging inequality using a redundant unread core copy; least/live assumptions remove this example.
- `L_meta_3444` refutes an adjusted charging inequality even all gates live, using an8gate circuit for a5vertex path. It is not minimum (baseline5gates), so minimum-circuit charging remains possible.
- `L_meta_3446` refutes a related core-edge/vertex-cover inequality using a17gate circuit on a7vertex forest with4edges. Again strongly nonminimal.
- These counterexamples prohibit deriving additive blockcost from lift-fixed/live conditions alone, but do not disprove a carefully formulated least-circuit version.

No exact target, unconditional sharp plane bound, or unconditional no-C4 bipartite ORcount floor was found in this census. Results and limitations communicated directly to root and lower_bound.

## Minimum bipartite read1 counterexample search

Expanded107-file census using IsReadK/IsLeastAO/IsMinimalMonoCircuit and25positive-junk candidates found no checked counterexample to minimum AO2 circuits being read1 for bipartite+C4-free graphs.

`L_meta_3679` refutes flattening least circuits for arbitrary bipartite graph functions using a39input58gate construction derived from Tarjan monotone networks. Its graph explicitly contains a4cycle: selector vertices29and30 both meet data vertices6and9. Thus it does not obstruct the projective-plane C4-free specialization. `L_meta_4849` has the odd5cycle0–4–7–1–6–0, so likewise not a bipartite counterexample. The forest examplesL3444/L3446 are nonminimal.

This is a bounded source census result, not proof of the universal normalization conjecture. Shared with lower_bound.

## Additional minimality and pivotality source map

`L_meta_5412` contains checked helper lemmas at lines859(`least_inOutputCone`),881(`least_no_equiv_wire`),898(`least_no_belowF_and_opnd`). For leastAO nonempty graph circuits, all gates lie in the output cone; no gate is equivalent to any earlier wire; neither operand of any AND gate can already imply the target. These do not presume that every AND is below the target.

`L_meta_3760` contains `reader_or` at485 and `reader_unique` at522 in its internal least-circuit model: a wire already below output can be read only by OR gates and at mostone reader. This supports top-level OR normalization and charging, but does not eliminate non-below-output junk gates.

The final theorem of `L_meta_5412` excludes exactlytwo junk gates when each is a product of two ORs forming a double-star around an adjacent centerpair: z∈Ci⊆N(z'), z'∈Di⊆N(z), both sides at least2. It does not exclude arbitrary two-junk patterns.

Earlier generic L2668 zero-bypass pivotal-edge theorem is stated for `IsMinimalMonoCircuit`, whose model allows constants/invalid reads. Applying it to `IsLeastAO` needs a model-normalization bridge; do not conflate these minimality predicates.
