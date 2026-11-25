# Independent review: complete slim modular refutation

UTC: 2026-11-25T17:49:49.636802+00:00

Verdict: PASS at SHA-256 `fcc32a65996638b4e5a0ad7bdc2dd422e38a15ccba5fe0fcf0078aa36f557949` (293 lines,18,039 bytes). The complete modular Lean export reports exit0, with both full archived streams empty. This is a complete modular proof of the exact posted statement's negation. The standalone single-file build, checker, and final PR diff remain pending.

The full change from the independently reviewed initial wrapper is saved in complete-refutation-slim-review.diff. The exact final theorem and normalization proof are byte-identical. All117 cap11 source masks, target representatives, permutations, and case order are unchanged. Only the two4293 branches now call the independently reviewed analytical residual_exclude4293 theorem with the same premises.

The cap10 proof keeps direct certificates for127,1290,4757. The other two cases transport8488 to1290 by graphPerm1 and16256 to127 by graphPerm2; I independently verified both finite images. Strict-live graph correctness comes from the reviewed rename lemmas. The independently reviewed RelabelSurplus equalities preserve Bzero<=1 and Bplus=10 directly, without assuming no_empty_surplus or any final exclusion theorem. The transported ineligible equality has the correct direction. Therefore these reductions are noncircular.

The revised no_empty_surplus proof explicitly derives10<Bplus from cap_ten_impossible before using the total-surplus identity and size<=24. This is a proof-elaboration clarification with the same conclusion Bplus=11 and Bzero=0. The subsequent cap11 transport remains founded on this independently established result.

All introduced dependencies have separate independent reviews: RelabelSurplus, ResidualShape4293/Residual4293, and Public4293. Their explicit hypotheses are discharged by the wrapper. Source format scans pass. Auxiliary imports still require final inlining and the repository's exact refutation checker; no final-checker or PR verdict is asserted here.
