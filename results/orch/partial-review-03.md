# Independent checkpoint 03 review

Reviewed at: 2026-11-25T14:07:36.084066+00:00
File: lean/PEqualNP/Outside/L_meta_2592.lean
SHA256: 8d8a87cd15c8b970f06b221275dc55b70cb2e42cc7844bec884fc219a1de5060
Lines: 178

Verdict: PASS for a partial checkpoint, conditional on the named Lean build succeeding.

- Exact 15 ordered edges match the posted desk statement.
- Independently parsed all 20 gates: AND/OR only, fan-in at most two, references strictly earlier, output wire 29. All 1024 input assignments agree with the exact posted edge function.
- All 1024 vertex subsets verify independence maximum 4 and cover minimum 6. Explicit witnesses are correct.
- Monotonicity was checked on all covering edges of the Boolean lattice; the neighbor vector proves every one of the 10 inputs essential.
- Three generic Boolean-order lemmas were previously checked with Lean. Their argument compares the two updates of input i, then uses suffix independence from i and monotonicity in the added Boolean input. The bridge correctly instantiates these with ptFun monotonicity and essentiality.
- The bridge assumes H ignores input i entirely when its added Boolean is fixed. This is stronger than merely having a single NOT gate or a single path from NOT to output. It is a sound restricted subcase, not the posted lower bound.
- One permitted PEqualNP.Defs import; helper declarations inside the correct namespace; no forbidden text, strings, attributes, or options. git diff --check passes.

Repository guard result: REJECTED with sole reported reason `the file holds no theorem`. This is expected for the explicitly partial checkpoint and must not be described as guard acceptance. No theorem named PEqualNP.Outside.L_meta_2592 proves the posted statement; no proof PR should be opened for this checkpoint.

Full independent test/guard output: /tmp/oec/pequalnp-pilot-98/structure/review-checkpoint03.log
