# Lemma-search findings for L-meta-2583

The allowed project import is PEqualNP.Defs. Its source imports definitions and instances only: no top-level theorem/lemma declaration was found under Defs. Outside proofs below are available for transplant, not as allowed imports.

## Exact decomposition

For a projective plane of order q with N=q^2+q+1, the target is equivalent to unrestricted AO2 size lower bound N*(q+2)-1, using the existing constructive and read-1 lower-bound results below. Every line has q+1 incident points, every point has q+1 incident lines, |E|=N*(q+1), and every vertex cover has size at least N. The incidence graph has no 4-cycle.

* `L_meta_2393.lean`, helper `Own.upper` (starts line 4673), explicitly constructs a read-1 AO2 circuit with size+1=N*(q+2). The block beginning line 4174 supplies all its machinery. It uses no plane property beyond N>0 and q+1 points per line.
* `L_meta_7684.lean` gives a more general read-1 construction from any bipartite vertex cover, size at most |E|+|cover|-1.
* `L_meta_4897.lean` proves for C4-free bipartite graphs that any read-1 AO2 circuit has a vertex cover with |E|+|cover|<=size+1.
* `L_meta_7639.lean` combines this with a perfect matching to show |E|+N<=size+1.
* `L_meta_2237.lean` and `L_meta_6369.lean` contain the general graph form of the read-1 lower bound.

The extracted constructive block is `results/orch/lemmas/IncidenceUpper.lean`, 635 lines. It has been renamed into the final-file helper namespace, with helper theorems changed to lemmas. It is NOT newly compiled yet; the supplied toolchain was absent and root is arranging it. It is copied from already-checked upstream code, not a new theorem.

## Existing normal-form obstruction

`L_meta_1491.lean`, `L_meta_4183.lean`, and descendants establish for a least AO2 circuit in TopForm:

|E| + t + 2*c + j + r <= size + |Ustar| + 1,

where t=|tops minus centreless|, c=|centreless|, j=|junk|, r=|orN minus lam|. They also bound the minimum vertex cover of the star-covered graph by t. These results leave the unowned incidence edges Ustar uncontrolled. A tight charge of those edges (and the remaining cover deficit) to centreless, junk, and remaining OR gates is exactly what would close the desired bound. No such unrestricted charge was found.

`L_meta_2581` proves only a constant-factor lower bound assuming READ-3. `L_meta_2058`, `L_meta_1942`, and `L_meta_2466` similarly require READ-2. Their proofs do not eliminate the read assumption.

The desk itself describes the open part as replacing nonstar blocks at no greater cost. Current repository evidence is consistent with a substantial open structural result, not a missing convenient Mathlib lemma. I have not verified its status in published literature.

## Public literature context (read 2026-11-25)

Read https://pequalnp.com/papers/note-1, section 7, using the built-in web tool. The site reports that C4-free bipartite edge functions have |E|/2 gate lower bounds in restricted multilinear/tropical/arithmetic models, and attributes the absence of the corresponding unrestricted monotone Boolean bound to Jukna 2014, Remark 10. The cited original paper was not opened, so its exact historical claim is UNVERIFIED at the primary source. It also attributes an explicit-superlinear monotone edge-function problem to Jukna ECCC TR05-021. The exact N*(q+2)-1 unrestricted bound sought here would in particular yield explicit superlinear monotone lower bounds for projective planes. This explains the gap being genuinely research-level.

## Sharper restricted normal-form bounds

* `L_meta_8103.lean` (2832 lines, 145180 bytes) proves the required full-cover charge when there is exactly one junk gate and Ustar is nonempty: there is a vertex cover K with |K|+|Ustar| <= t+2c+j+r. With L1491 this immediately proves |E|+|K|<=size+1.
* `L_meta_1876.lean` (717 lines, 31631 bytes) proves Ustar is empty when junk is empty, for girth at least five.
* `L_meta_6240.lean` (786 lines, 38460 bytes) proves 2*|Ustar| <= 2*c+j+r when every centreless/junk/mixing gate accepts at most one Ustar edge. Extending a star-subgraph cover by one endpoint per Ustar edge then closes the exact lower bound.
* Hence the unrestricted obstacle is genuinely the many-junk case where some contributing gate accepts several residual edges, not the elementary read-1 construction or incidence combinatorics.

A regular-plane refinement: any cover K of E minus U satisfies (q+1)*|K|+|U| >= N*(q+1), by counting covered edges. Coupled with the normal-form budget, the sufficient residual charge becomes q*|U| <= (q+1)*(2c+j+r). This is weaker than the universal 2*|U| condition, but no proof for general least circuits was found.

## Validation

2026-11-25T15:04:48.536620+00:00 `IncidenceUpper.lean` compiled with pinned Lean 4.36.0 through `lake env lean`, exit 0; stdout/stderr empty. Only PEqualNP.Defs is imported. Both tauto calls were replaced by explicit propositional terms. Complete log: /tmp/oec/pequalnp-pilot-144/upper-compile.log.
