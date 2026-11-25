# Independent review: SoleAndRestriction

UTC: 2026-11-25T16:54:44.078926+00:00

Verdict: PASS. Exact source SHA256 `2789dde57ec26df56e426ff5e6c19e076d9037ea362943e8058ea01fa18bbf33`, 4906 bytes/102 lines. Author reported successful check/export; complete ordinary check streams are empty. This reviewer did not rebuild.

The two AND-step lemmas treat both operand orders and directly show that a false operand creates a false status without emitting a gate. constant_with_reader_losses applies the previously reviewed constant-step charge with empty initialK: one selected constant-producing operation plus at leastone later reader of its original wire yields two distinct deleted gate positions. NOk is explicit in the general count lemma, so syntactically unused NOT operands cannot earn a false saving.

and_reader_floor applies that count to raw input2=false in the actual nine-input circuit. Its hypotheses explicitly identify an AND[2,a] or AND[a,2], a later reader of its output, Monotone2, and exact computation of the displayed eight-input cofactor. The input map fixes2false, and Elim preserves that original status through the prefix. RestrictionEight.compiled_floor supplies at least12 emitted gates; the two losses therefore force at least14 original gates. No sole-reader assumption is needed by this stronger local statement, and none is smuggled into its use.

Imports are reviewed scratch dependencies and require assembly under allowed imports for a submission. Correct L_meta_1884 namespace, no options, attributes, strings, forbidden constructs, new axioms, unsafe declarations or secret-like content; below512KiB. It proves the stated conditional local gate lower bound, not the whole posted target.
