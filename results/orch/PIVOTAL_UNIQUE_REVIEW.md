# Independent review: PivotalUnique

Verdict: PASS for partial-artifact preservation.

The helper assumes a monotone circuit computing the graph function, a valid gate index, a genuine edge uv whose test is lost when the gate is forced false, and that every other lost graph-edge test is the same unordered edge. It does not assume the old gate is AND; replacement by AND(u,v) is allowed at any gate.

Pivotality first proves the original gate is true on the uv pair. Monotonicity then shows AND(u,v) is pointwise below that original gate on all inputs. The suffix comparison therefore makes the complete rewritten circuit pointwise below the original. The unique pivotal pair remains true because the replacement gate is true there; nonpivotal pairs remain true because false-to-AND can only increase the modified circuit. The graph sandwich gives exact equality. Gate-list set preserves size; new gate is valid fan-in-two monotone. Its local pair values imply one endpoint is u, yielding a local star. No existence/minimality/global-profile claim is made.

Source scan: one allowed import, correct private helper namespace, no forbidden tokens, quotes, hash commands, attributes, options, or reserved-root text. Both supplied build logs are empty; parent reports exit0. No source changes made.

SHA256: 68ccfeb03c865ecf366728f1d0f4f03c757de4feab8e0d253971bd8051c6dd13
Review UTC: 2026-11-25T07:44:28.895710+00:00
