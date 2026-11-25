# Independent review: directional monotone live-root lemma

UTC: 2026-11-25T15:47:52.787873+00:00
Verdict: PASS as a checked dependency helper. This file is not a standalone submission and does not prove the posted gap.

Source: `results/orch1884/lemmas/LiveDirectional.lean`
SHA256: `67670687eb363ff1651ddd1c7e40d17227790fd8453c229e785dbf4c9bf8ad7d`
Size: 1686 bytes; 38 lines.

The author reports successful Lean exit 0. Complete logs /tmp/oec/pequalnp-pilot-103/1884-directional-first.stdout and .stderr are empty (SHA256 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855).

The mode is explicitly Live false throughout. Consequently allowed false d gives d < 2 and only the two monotone binary operations AND/OR are possible. A false-to-true change of either gate requires a false-to-true change in at least one operand. The finite Boolean case proof covers this exactly. Induction over Live propagates the directional change through the overwritten gate or retains a surviving root, giving an initially live root with the same directional change. The final theorem uses its explicit isolation premise to identify that root with a. No order assumption on rows is necessary, and none is silently used.

This would be false for arbitrary signed mode, but the source does not claim that extension. The exact Live and signature definitions come from the already checked Binary17 dependency (source SHA256 824549cea61a489c8821209214cf8d631ef13ac9741611f3c21caf9135c72bcd; object SHA256 68483000dc93ad24671d0ab0575de4f9d1c8b28b3291d9acbc719acbcddcf158). Its import Binary17 is allowed for this preservation test but must be replaced by in-file definitions in any final Defs-only submission, followed by a new build.

All new declarations lie in PEqualNP.Outside.L_meta_1884.LiveDirectional. No sorry, axiom, native_decide, forbidden namespace substring, string literal, attribute, option, or unsafe/meta declaration occurs. No credential material was observed. The reviewer did not author this helper.
