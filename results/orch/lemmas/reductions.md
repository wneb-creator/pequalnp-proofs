# Reduction and decomposition route

Existing reductions occupy all three slots:

- R_meta_2592_408: normalize all wire reads, trim output, then prove normalized bound.
- R_meta_2592_318: cut at the last NOT, prove a separator against arbitrary prefix plus monotone suffix.
- R_meta_2592_271: prove binaryFloor 15 + notCount ≤ size, then exclude 1–4 NOT gates.

A fourth reduction should not be submitted. The last-NOT decomposition appears provable in about 70 lines from definitions alone. Choose the prefix output to be the first NOT operand, or n + prefix.length if the NOT has no operand. Prefix-plus-NOT then suffix is foldl_append. The suffix has no NOT by choosing the last one.

Finite sanity: 58,920 exhaustive assignments across 6,000 random fan-in≤2 circuits (0–5 inputs,1–29 gates; empty and invalid reads included) matched the split full wire-list and output exactly. Full log /tmp/oec/pequalnp-pilot-114/last-not-sanity.log.

Public child status verified via search shard and individual lemma JSON: L-meta-7389 (normalization from408) checked; L-meta-8295 (last-NOT split from318) checked; L-meta-4725 (15binary floor from271) checked. Hard siblings7391,8297,4727 remain conjectures.

Independent compact last-NOT decomposition compiled successfully with pinned Lean4.36.0, import PEqualNP.Defs, exit0; saved in LastNot.lean. This duplicates checked8295 and is not a new gap proof. Full log /tmp/oec/pequalnp-pilot-114/last-not-build.log.
