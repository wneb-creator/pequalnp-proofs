# Independent review: sole-OR nonedge-pair localization

UTC: 2026-11-25T15:46:41.186867+00:00
Verdict: PASS for the extension, finite classification, explicit hypotheses, and format. This is a partial semantic restriction, not a completed proof of L-meta-1884.

Source: `results/orch1884/lemmas/PairLocalization.lean`
SHA256: `7c2b16f0f72f9a6aff93389bf20c612631c0967290cc5ba6c597637620310280`
Size: 7990 bytes; 192 lines.
The complete previous SoleOrPartner body is preserved exactly before the added declarations; its separate review remains applicable.

The author reports successful Lean exit 0. The complete third-run stdout and stderr at /tmp/oec/pequalnp-pilot-103/1884-pair-local-third.* are empty (SHA256 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855).

The finite classification was independently checked directly from the Petersen edge set. Among 216 unordered admissible (v, nonedge-pair) cases with v != 0 and v outside the pair, exactly six lack the required fixed-x0 distinguishing extension: (1,{3,9}), (1,{7,8}), (4,{2,6}), (4,{7,8}), (5,{2,6}), (5,{3,9}). These agree with the explicit symmetric exceptional predicate. Every exceptional pair remains independent after adjoining 0, while adjoining v as well creates an edge. The independent finite results are in pair-independent-validation.json.

The semantic localization first excludes a repeated endpoint and pairs containing v, using the previously proved singleton rejection and the explicit v-independence hypothesis. Any other pair outside the six cases has a z != 0 preserving the x0 fiber and a target-changing extension. Fiber monotonicity preserves H=true on the independent extension, and factorization through v OR H then contradicts the target change when v is added. This matches the lemma hypotheses exactly.

For an accepted exceptional pair, accepting the zero extension would likewise make the OR output agree across the target-changing v extension, so H must reject it. No monotonicity across x0=0 to x0=1 is assumed or used; the resulting decrease in H is the intended conclusion. The file does not establish the factorization or independence hypotheses for a concrete circuit and makes no direct gate-count claim.

Only import: PEqualNP.Defs. All declarations remain in PEqualNP.Outside.L_meta_1884.SoleOrPartner. No sorry, axiom, native_decide, forbidden namespace substring, string literal, attribute, set_option, or unsafe/meta declaration occurs. No credential material was observed. The reviewer did not author this extension.
