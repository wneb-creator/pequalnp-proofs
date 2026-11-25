# Independent review: OR-footprint incomparability pruning

Reviewed 2026-11-25T17:33:23.953524+00:00 by lemma_inventory. Current source SHA256: a0452a14601aa9d0dc0bf09b74b72d7a367e6be90d394df521fe8eb600b1474f.

Verdict: sound as an existence-preserving restriction for <=k OR-gate circuits, with arbitrary free AND gates, provided the target has at least two distinct edges. This remains an informal encoding review, not a Lean proof or a solver certificate.

For a circuit minimizing its number of OR gates, let an OR have operands A,B whose accepted edge-pair sets satisfy footprint(A) subset footprint(B). Replacing A OR B by B preserves its value on every minimal positive edge assignment. The replacement only decreases the wire pointwise; subsequent monotone gates preserve this decrease, so all independent negative assignments remain rejected. The transformed circuit accepts every edge pair and remains monotone, hence computes the exact graph function on every assignment. One fewer OR contradicts minimality. Swapping A,B gives the opposite direction, so every OR in a minimal circuit has incomparable positive footprints.

A circuit with at most k ORs can first be minimized and then padded to exactly k by unused OR gates. Take two distinct target edges. Their raw-input conjunctions have distinct singleton footprints on the positive edge-pair rows, so their OR has incomparable operands. Free AND cones can express both conjunctions in every extra slot; repeated signals and unused slots are permitted. This padding argument requires two distinct edges.

The implementation adds the two nonzero bitvector constraints positiveMask AND A AND NOT B, and positiveMask AND B AND NOT A, exactly as required. positiveMask is computed from the enumerated target edge-pair rows. Operand ordering and all earlier selector restrictions remain compatible. An initially missing single-edge guard was flagged and fixed: argparse now rejects pruning unless kind=or and len(set(E))>=2. The retained prune-guard-validation.txt confirms rejection of a single-edge request.

Independent positive control: decoded the archived C6 five-OR SAT model, evaluated it on all 64 input assignments, and checked both exclusive positive witnesses for every OR slot. All checks passed. The corresponding four-OR query returned UNSAT; its status is computational evidence only. No large search was repeated.
