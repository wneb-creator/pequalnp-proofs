# Existing-results preservation manifest

Stopped on parent instruction after lease HTTP410; no own build was active. Dual9 build was never launched.

## Checked

- existing_binary16.lean: full source exit0, already checkpointed by root.
- existing_binary17_base.lean: full source compiled exit0; new canonical suffix16 plus copied signed nine-input floor15. Full logs existing-binary17-base-2.stdout/.stderr. Artifact ExistingBinary16.olean remains scratch only; source is preserved.
- existing_suffix17and_snippet.lean: unconditional proof tested by existing_suffix17and_full_test.lean importing the full compiled base; exit0, empty logs existing-suffix17and-full.stdout/.stderr. A used canonical AND or difference output and its positive primary operand become two constant roots under restriction, proving suffix>=17.
- existing_or_and_snippet.lean: unconditional proof tested by existing_or_and_full_test.lean; exit0, empty logs existing-or-and-full.stdout/.stderr. After free OR(i,j) and used primary0 AND OR(i,j), or primary0 AND NOT OR(i,j), suffix>=16. The OR operands avoid primary0.
- existing_or_and_transport_snippet.lean: arbitrary vertex transport tested by existing_or_and_transport_test.lean importing Binary17Integration and including the canonical snippet; exit0, empty logs existing-or-and-transport.stdout/.stderr. Requires each OR operand differ from the positive primary operand; the OR operands may coincide.
- existing_canonical_checks.lean and existing_suffix16_slim.lean: earlier checked finite/conditional structure tests. The later full base is the unconditional source.

## Draft or failed, not checked

- existing_dual9_base.lean: 547200-byte draft engine replacement from L_meta_4033, with signed15 and intended monotone16, plus existing ten-input machinery. Never compiled. Requires review, actual dependency pruning and source-size reduction before use.
- existing_mono9_core.lean: lexical dependency extraction draft, never compiled.
- existing_dual9_compact.lean: unsafe whitespace-minification prototype. Do not use; removing function application spaces before parentheses failed a small smoke test.
- existing_compact_smoke.lean: failed test proving that minification is unsafe, complete logs preserved.
- existing_two_gate_search.py: exploratory finite Python classification only; it is not a Lean theorem.

The first full canonical-base build failed on a witnessB name collision; it was fixed by renaming new rows canonicalWitnessA/B. The successful second build is authoritative. Complete failed and successful logs are preserved.
