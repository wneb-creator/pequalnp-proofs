# Independent isolated-vertex Lean source review

Verdict: PASS for source, mathematical scope, format and the recorded successful build of `IsolatedVertex.lean`, SHA256 46ca6e535347b18b674028d70744585b63112c7e0c98eb6b6479614c59644470.

The final theorem assumes a symmetric complex 4×4 matrix, zero off-diagonal entries at one arbitrary vertex, and constant permanent 24 on the entire affine line J+zM. It concludes that vertex's diagonal is zero. It does not assume the tangent equation or a matrix-rank condition, and does not claim the full gap.

I parsed the actual three block-polynomial definitions from the Lean source and independently checked their expansion using Ryser's formula. The coefficient identities are L=6(s+d), Q=2(r+sd), C=p+dr, F=dp. The displayed four evaluation combinations at ±1,±2 correctly recover L,Q,C,F. The exact final certificate is d⁴=(d³/6)L−(d²/2)Q+dC−F. Thus zero coefficients force d=0 in ℂ.

The displayed permanent expansion contains each of the 24 permutations exactly once. The symmetric block identification and simultaneous row/column permutation argument preserve the assumptions and move the requested vertex to index zero without adding a premise. The only options are allowed numeric limits scoped with `in`; no prohibited syntax or new axioms occurs. The build record reports PASS, exit0. This review does not substitute for any separately requested axiom audit.

Evidence: `check.py` and complete `check.log`. No source was changed and no duplicate Lean build was run.
