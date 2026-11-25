# Independent review: two-cover geometry dichotomy

Reviewed by constructive on 2026-11-25 UTC. Source: `/tmp/oec/pequalnp-pilot-70/lower-bound/CoverStarOrOuter.lean`, 47 lines. Read the full source and empty compiler log; the author reports Lean exit 0. This review did not rerun Lean.

Verdict: PASS. If neither candidate center alone covers the symmetric loopless relation, edges avoiding each center provide an edge into c and an edge out of d. Their outer endpoints avoid both centers, using irreflexivity for their own incident centers. The assumed two-center cover then rejects the pair of outer endpoints. The orientation changes use the explicit symmetry hypothesis correctly.

Distinctness of c and d is unnecessary: if they coincide, the first star alternative already follows from the cover. The outer endpoints need not be asserted distinct; the rejected-pair conclusion remains valid if they coincide. The result supplies exactly the accepted outer pairs and rejected outer pair needed by the mixed-support lemma, without an additional C4-free hypothesis.

The forbidden-format scan returned status 1 with no matches for `_root_`, string literals, attributes, `sorry`, axioms, `native_decide`, or options. The import is `PEqualNP.Defs`.
