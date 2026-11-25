# Independent review: L_meta_1884 preservation assembly

UTC: 2026-11-25T15:47:52.787873+00:00

Verdict: PASS for assembly integrity, reviewed mathematical scope, and forbidden-form scan. Named-file build is still running at this timestamp; no target checker success is asserted.

Named file: `lean/PEqualNP/Outside/L_meta_1884.lean`
SHA256: `e1188365b2fb6f0aa58ce75b2ca8e66a74e1eb71997fc023ecfe4034494e75ff`
Size: 16628 bytes; 395 lines.

The named source is exactly the three already independently reviewed source bodies listed below, in this order, after removing repeated PEqualNP.Defs imports and normalizing only separating blank lines. No declaration, hypothesis, target expression, finite certificate, or proof body was changed.

- `results/orch1884/lemmas/InputEssentiality.lean`: SHA256 `c4b010fe68ff746b09f3f7fa40edc9a7b83471e23f7626ef2af1b9d797f145e2`.
- `results/orch1884/lemmas/KWFormula.lean`: SHA256 `835dfeb7c4c7d691f03cc4e3c7bd9642d3bcf9cb4263c4a7f811229df6325da5`.
- `results/orch1884/lemmas/PairLocalization.lean`: SHA256 `7c2b16f0f72f9a6aff93389bf20c612631c0967290cc5ba6c597637620310280`.

The three namespaces are InputEssentiality, KW, and SoleOrPartner below PEqualNP.Outside.L_meta_1884, so their independently defined target functions do not collide. The bodies establish essential nonzero mapped inputs, a twenty-leaf lower bound for positive formulas, and conditional sole-OR semantic restrictions. They do not assert the exact posted eighteen-gate circuit impossibility. This is an explicitly partial preservation checkpoint; a proof PR and successful checker report would be premature.

The only import is PEqualNP.Defs on the first line. No forbidden namespace substring, double quote, attribute, sorry, axiom, native_decide, unsafe/meta declaration, or unsupported option occurs. The only options are scoped numeric maxRecDepth/maxHeartbeats certificate limits. The source is below 512 KiB and contains no observed credential material.

The reviewer authored none of these three proofs. Their earlier individual review files remain applicable to the assembled mathematical content.
