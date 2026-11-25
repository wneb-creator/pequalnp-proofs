# Independent semantic join-obligation review

Reviewed at: 2026-11-25T14:25:36.305859+00:00
Source: results/orch/lemmas/direct.lean
SHA256: 04d0f6d7c51b1117091f93fb8ea9e82e9559d626d7f0510e9df16ce3cdcf5d4f

Verdict: PASS for a partial checkpoint. Supplied validation hash matches this source and records Lean exit 0. No Lean command was run in this review.

Exact assumptions: F and G are monotone on pointwise Boolean input order; F(u)=B(u) OR (A(u) AND NOT G(u)) for every u; F(x)=true, B(x)=false, A(y)=true, and F(y)=false. A and B are otherwise arbitrary functions.

The first two conclusions follow from the formula at x: A(x)=true and G(x)=false. The formula at y forces G(y)=true. Monotonicity yields F(x join y)=true and G(x join y)=true. At that join, the formula reduces to F=B, so B(x join y)=true. The proof follows precisely this argument and does not infer any unstated monotonicity of A or B.

An independent exhaustive finite check for n=1 and n=2 covered every A,B,G assignment with the required monotonicity, and all qualifying x,y pairs (4 antecedent instances), with no failure.

Format: three permitted Mathlib imports; one lemma in the correct helper namespace; no forbidden text, strings, attributes, or options. The reviewed source contains no BoolSpace abbreviation, new datatype, or instance. An abbreviation would be a definition rather than a new datatype, but this source needs none.

Scope: the formula is an explicit hypothesis. No circuit decomposition, gate-cost preservation, normalization, or Petersen lower bound is asserted. This is a sound semantic constraint only, suitable for the partial work branch, not a completed proof PR.
