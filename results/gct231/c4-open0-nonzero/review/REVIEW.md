# Independent compressed C4 consequence proof review

Verdict: PASS for the compiled standalone case-0 nonzero proof and the signed-equation symmetry. REJECT the original combined candidate's case-1 nonzero wrapper until its stale h2 bullet is removed. The global option layout is scratch-only and must be scoped before named-file integration.

The standalone source is `C4Case0Nonzero.lean`, SHA256 99a2284e7cb3e67f20d24bf7617d51416f37de56442edcfbd25e14ce770fbf46, 75,298 bytes. The recorded build finished successfully in 39.15 seconds and its axiom audit lists only propext, Classical.choice and Quot.sound.

I independently verified all 26 entries of the unsaturated QQ certificate, including 22 consequence identities and 3,954 rational term products. Its four generator roots equal the first four reviewed nonzero-branch equations exactly; no inverse variable or squarefree replacement is used. The emitter's dependency closure needs only roots 0, 1 and 3. Removing an unused hypothesis strengthens this helper and is sound.

The actual Lean source was then parsed separately. A strict Python-AST evaluator with Fraction coefficients and sparse bivariate polynomials verified every one of its 18 `linear_combination` identities directly from the rendered expression text, and matched each declared polynomial to the certificate. It confirmed the exact two squared consequences `(beta+gamma)^2=0` and `(gamma^2-gamma-1)^2=0`. In the field of complex numbers, the `mul_eq_zero` steps give the unsquared equations. The final identity is exactly

    (gamma^2-gamma-1) + (beta-gamma+1)*(beta+gamma)
      = beta^2+beta-1.

The explicit hypothesis that the right side is nonzero supplies the contradiction. No nonzero denominator or geometric premise was hidden or dropped.

Independent symbolic checks also verified the case-1 substitution gamma -> -gamma on all eight raw branch equations. The zero-branch signs are all positive; the nonzero-branch signs are +,-,+,-. The open beta factor is unchanged. This supports short case-1 wrappers.

However, the original combined source SHA256 98ffc97fdfa13644182260bef945c6f7cd43c7e58a58954d45fc4c96d14d32b8 keeps an obsolete `linear_combination h2` bullet in the nonzero wrapper, although neither that wrapper nor the compressed case-0 theorem has an h2 premise. The other required bullets are h0, -h1, -h3, then h_open. This bug was reported immediately; the standalone case-0 theorem body is byte-preserved and unaffected. A corrected combined source needs a separate build and delta review.

Both scratch sources place numeric heartbeat/depth options globally. The allowed named-file format requires `set_option ... in` scoped immediately above each theorem. No other prohibited syntax, extra axioms, predicate shadowing, or fake full-gap theorem was found in the standalone. Its conclusion is the explicit polynomial-system contradiction, not the full L-gct-231 statement.

Evidence: independent `verify_certificate.py`, `dag.log`, `certificate-verdicts.json`, and `check_lean.py`/`check-lean.log`. No source or certificate was modified.
