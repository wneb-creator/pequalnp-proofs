# Local strategy review for L-meta-2602

2026-11-25. Existing checked reductions:

- R_meta_2602_2: restricted-face lower bound 56 plus a sensitized-path theorem. A 283-line proof packs equal wire columns and transfers the face bound across plane automorphisms.
- R_meta_2602_415: generic guarded propagation plus two specialized finite-row cut obstructions. 81 lines; generic part is straightforward, specialized hypothesis carries the lower-bound difficulty.
- R_meta_2602_926: four cases for repeated-AND witnesses (shared, mixed, one-sided singleton, both singletons). 531 lines.

The lease reports reductions_live=3, so a fourth reduction may be refused.

Parent R_meta_1482_2 splits a general size >=63 bound and exactly our normalized incidence-(0,0) double-reread statement.

Reusable checked components, requiring copying rather than importing (gap allows only PEqualNP.Defs and Mathlib):

- L_meta_2067, 475 lines: derivative survives on every incidence when andPairs=0. Strong induction over wires, tracking singleton/pair evaluations and the derivative.
- L_meta_4803, 1006 lines: size >=64 from IsAO2, exact plane semantics, and no nested AND pair.
- L_meta_1751, 1992 lines: same lower bound under weaker test semantics; L_meta_2059 and L_meta_5158 are related variants.
- L_meta_1500, 4506 lines: size >=64 under line-degree <=1.
- L_meta_4101, 1892 lines: excludes one duplicated AND witness at size <=64 when every AND gate implies the final output (junk-free).
- L_meta_1961, 8880 lines: if size<64 and at most one nested AND pair, gives a smaller circuit with same tested behavior.

No unconditional full lower-bound or normal-form theorem found. Eliminating junk / nested AND pairs remains the key missing step.

## Independent review checklist

Exact desk statement and name; allowed imports only; no sorry, new axioms, native_decide, _root_, quotes, forbidden attributes/options or compile-time commands; regular UTF-8 <=512 KiB; named-module build; checker against exact saved statement; clean single-file PR diff.

05:53 UTC: parent reported HTTP 410; stopped work immediately. Guard.lean is an UNVERIFIED draft of the generic guarded-propagation hypothesis from R_meta_2602_415. It has never been compiled and is not a proof of L-meta-2602. Foundation wire lemmas were adapted from checked L_meta_2067; the new monotonicity and propagation arguments still need Lean checking.

Independent preservation review: git status showed only untracked results/ files, with no tracked-source changes. Reviewed all research Markdown and the Guard.lean draft; no credential/token/lease identifier found. No Lean build or checker result is claimed. This review authorizes only preservation of research artifacts on the owner branch, not a proof PR or acceptance claim.
