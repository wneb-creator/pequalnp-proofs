# L-meta-2583 counterexample investigation

## Definition audit

`ReadK.IsReadK n C 1` means that every prime implicant has some proof tree in which each variable appears at most once. It is not a global read-once restriction on input fanout. The count vectors are joint: the same proof tree must read both endpoints once. `TopForm.IsAO2` requires AND/OR only, exactly two operands per gate, and reads of earlier wires.

No definitional loophole or immediate counterexample was found. The projective-plane hypotheses imply the usual symmetric incidence counts; the absence of a separately stated point-degree condition is not obviously a weakness.

## q=2 finite case

Used the Fano plane on seven nonzero vectors of F2^3, with point-line incidence given by zero dot product. Checked all line sizes and unique lines through distinct points by exhaustive computation.

- 14 inputs and 21 incidence edges.
- 458 independent input sets, of which 37 are maximal.
- 58 extremal truth assignments suffice for monotone AND/OR circuits: the 21 positive edge pairs and 37 maximal independent negative sets.
- Constructed the standard seven-star circuit with 27 gates.
- SAT encoding sanity check succeeds for this pinned baseline; independent evaluation matches all 16,384 inputs.
- Joint capped proof-tree count-vector computation confirms read1 for all 21 incidence pairs in the baseline.

## Search

`counterexample.cpp` is a generic monotone AND/OR exact-synthesis encoder using CaDiCaL. It selects two earlier wires per gate, requires every nonoutput gate to feed a later gate, and optionally orders independent gates by maximum operand then minimum operand. The current run seeks 26 gates, with the first gate OR(point0, point1), using all 58 extremal assignments. Any SAT model is independently checked on all 16,384 inputs and tested for read1 on all incidence pairs.

This is one restricted search branch, not a complete lower-bound proof. A 26-gate circuit would be a candidate refutation only after establishing that no read1 circuit of that size exists. No candidate has been found yet.

Complete logs and graph/circuit data: `/tmp/oec/pequalnp-pilot-104/counterexample2583/`.

Started 2026-11-25T14:53:03.455158+00:00; one SAT process active, 20-minute cap checked between conflict budgets.

## Smaller gadget search (2026-11-25T14:55:52.384126+00:00)

Paused the Fano26 process and started an unrestricted first-gate search for a14-gate monotone circuit for the point-edge incidence graph of K4. It has10 inputs,12 edges,12 maximal independent sets, and24 extremal rows. The standard15-gate star circuit passes full1024-input validation and read1 checks on all12 edges.

A14-gate gadget would immediately give a26-gate Fano circuit. The Fano cap is point indices[0, 2, 4, 6]; the six pair-line input indices are[10, 8, 12, 13, 9, 11], in lexicographic point-pair order. The gadget input map is[0, 2, 4, 6, 10, 8, 12, 13, 9, 11]. All12 incidences of these four points lie on those six lines. Add the remaining three point-stars (9 gates) and3 OR gates to join their outputs to the gadget output:14+9+3=26. This embeds inq=2 itself, so a larger plane is unnecessary.

Only the K4-gadget SAT process is active. Its current cap is15 minutes; no candidate yet.

## Monotone dominance pruning (2026-11-25T14:59:34.188094+00:00)

An earlier wire h dominates a gate g when h is at least g on every positive edge input and at most g on every maximal independent negative input. Replacing g by h preserves the target on all extremal inputs by monotonicity of the downstream circuit, hence preserves the target globally. Thus a minimum circuit cannot contain a dominated gate. A gate that is false on every positive input, or true on every negative input, is also removable by constant propagation.

The new SAT version enforces these necessary conditions on a minimum prefix and permits an identity-padding suffix, retaining representation of circuits of at most the requested size. The standard15-gate K4 baseline passes these conditions and full truth/read1 validation. The original14-gate search was stopped as inconclusive; a new14-gate dominance-pruned search is active with a30-minute cap. Fano26 remains paused. No counterexample yet.

2026-11-25T15:07:34.417843+00:00: stopped all SAT processes immediately after root reported a lease error. No counterexample or target UNSAT result. Complete logs/data preserved in counterexample_checkpoint.txt. No new runs started.
