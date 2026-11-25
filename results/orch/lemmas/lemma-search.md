# L-meta-2602 lemma search

## Strongest nearby checked results

- `L_meta_2613.lean` (2583 lines): in a clean circuit (each AND gate implies the output), size at most 64, every AND gate accepting an incidence pair has an operand accepting one of its singleton ends.
- `L_meta_2615.lean` (2390 lines): under that same clean hypothesis, its helper `main_contradiction` proves each pair-accepting AND gate has an operand accepting either designated singleton; this is stronger than the final printed statement and is useful for killing derivative collisions.
- `L_meta_1500.lean` (4506 lines): no circuit of size at most63, provided line degree at most1. This cannot apply to a double-reread circuit directly.
- `L_meta_4803.lean` (1006 lines): at least64 gates if no AND lies in the cone of another AND.
- `L_meta_1484.lean` (1078 lines): general unconditional plane lower bound38.

## Existing reductions of our step

- `R_meta_2602_926.lean` (531 lines): trace evaluation bridge and double-collision decomposition. Its hypotheses are remaining shared/mixed/singleton collision obstructions.
- `R_meta_2602_2.lean` (283 lines): 56-gate punctured-face lower bound plus a path condition.
- `R_meta_2602_415.lean` (81 lines): backward propagation guard plus a strong face-cut condition.

## Why normalization does not immediately close the gap

`L_meta_3720`, `L_meta_4181`, and `L_meta_4543` give least/top-form circuits but do not make every AND gate clean. They also need not preserve formal derivatives, so finding a clean replacement does not refute the original circuit.

`L_meta_3653` handles a unique junk AND gate when it accepts a singleton, replacing it without growing the circuit. `L_meta_3700` handles a unique junk AND when all AND singleton evaluations are false. Both require every other AND clean.

`L_meta_3655` is a checked q=2 construction with lift fixed point and a double-reread edge at33 gates, whereas the star size is27. Thus lift fixed point alone does not imply no double reread.

A potentially viable argument must charge junk gates and reread collisions against the exact64 budget; existing general normal-form lemmas do not make that charge for free.
