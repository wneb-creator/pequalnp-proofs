# Independent review: initial complete modular wrapper

UTC: 2026-11-25T17:47:59.020775+00:00

Verdict: source semantics PASS at SHA-256 `43d4f9ead0dbce48900c4cab4fd7f58d2587d258d590c9666322bba08272f1d8` (283 lines, 17,219 bytes). This snapshot is archived at review-snapshots/CompleteRefutation-initial.lean. Modular compilation and the final standalone checker remain pending; W16256 was reported awaiting export when this review was assigned. This review does not convert computational coverage into a completed kernel-check claim.

The conclusion is exactly the negation of the posted existential statement: a public Monotone2 circuit of size at most24 computing the listed19-edge function on all Fin14 assignments. The final normalization call preserves full semantics and does not increase gate count; it correctly instantiates the strict-live graph lower bound. No strict-circuit premise is added to the final statement.

cap_ten_impossible uses the already checked unconditional Bplus>=10, total-surplus identity and size<=24 to get Bplus=10 and Bzero<=1. Its five branches exactly match tenMasks and use the paired-budget weak exclusions. no_empty_surplus then derives Bplus=11 and Bzero=0. This order has no circular dependence on the later cap11 cases.

I parsed all117 actual shift branches and checked their order exactly matches the complete elevenMasks list. Every stated graph permutation maps the source mask to the chosen representative, and every called certificate/reject theorem matches that representative. The parsed branches agree with complete-wrapper-transport.json. There are37 distinct representatives, covered by19 strong certificates,13 private projections,3 residual-code cases, Projection63, and the side127 bound. The opposite side is transported to127.

The shift helper uses move_case to preserve strict-live exact computation and size, then applies the previously established no_empty_surplus to the relabeled circuit. Thus this initial version does not assume Bplus/Bzero invariance or reuse a cap11 conclusion to prove its cap10 foundation. The exact equality orientation passed to the representative theorem is correct.

The source format scan passes, but its many helper imports are modular test imports. Final single-file inlining, dependency-hash audit, complete build, exact-statement refutation checker, and single-added-file PR diff remain separate required checks. Planned symmetry/compression edits require a follow-up review at their new hashes.
