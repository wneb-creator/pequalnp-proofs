# Independent review: NoPositiveRail

Verdict: PASS for the stated structural impossibility theorem. Reviewer circuit_search, 2026-11-25T17:04:25.688745+00:00. Reviewed SHA-256 `a4f64b76d8ec77a494152d3495d9b364ecf9fe3d281bb36e8cd352d2af74f805`, 619 lines, 28,508 bytes. No source edits or new compilation were made.

I verified that the complete23,678-byte NotRailOperand.lean (SHA-256 `5d709b17806b632ae45d53b86651735bd90eec5b169dcbecbe6ac7d047a37276`) is an exact byte prefix. I read its existing independent semantic review and the new4,830-byte NoPositiveRail namespace; this review adds scrutiny of the extension without replacing the recorded dependency reviews.

above0 compares every wire except raw positive input0, retains equal lengths, and requires at leastone wire. append_above0 therefore controls every newly appended position, since it cannot be0. The below-length/equal-length/default-read cases are handled separately. run_above0 uses the explicit absence of raw0 in each AND/OR gate to apply the ordinary Boolean gate monotonicity premise only at compared inputs. No unsupported global monotonicity of the negative helper is asserted.

The critical input comparison goes from pair{0,v} to singleton{v}. Raw input0 decreases and is deliberately exempt. Every other primary stays fixed, while the free negative rail increases fromfalse totrue. Thus above0 has the correct direction. The finite11-wire check covers real inputs and helper10; all larger indices defaultfalse.

Correctness excludes output0 using singleton{0}: the output would betrue while the Petersen target isfalse. The main theorem then proves H isfalse both at singleton{v} and at pair{0,v}. The first follows from the displayed factorization plus independence and fiber monotonicity. The second uses independence fromv to reduce to singleton{0}, which is rejected by the corresponding factorization lemma. This does not require the NOT operand list to omit raw0 orv syntactically.

At both compared rows, the sole NOT therefore outputs true. replace_not_false replaces it by the constanttrue gate AND[]; the name concerns its false operand, not a false output. This removes every NOT operand read, including any raw0 entry. The entire replaced circuit consists of AND/OR gates avoiding raw0, so run_above0 compares the two outputs. Returning to the original correct circuit forces target(pair{0,v}) <= target(singleton{v}), i.e.true <= false for v in{1,4,5}, the contradiction. All three neighbor cases are handled.

The theorem's actual hypotheses remain material: one displayed NOT between AND/OR prefixes/suffixes, raw0 omitted throughout those AND/OR portions, full target correctness, semantic independence of the NOT operand fromv, and the explicit sole-factor property. It introduces no size premise, no NOT-operand omission premise, and no full global-classification claim. It establishes that raw positive0 must occur outside this NOT under those guards.

The original1884-no-positive-003 stdout has nine inherited warning headers (unused simp/deprecation/already-closed simp), all at lines below518; stderr is empty and there are no error lines. Root reports the run exited0. No build was rerun. The full source has no sorry, new axiom, native_decide, string literal, _root_ marker, attributes, or options. It is a structural helper rather than the complete posted-gap proof.
