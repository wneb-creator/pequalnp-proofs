# SAT search scope and final status

All search stopped after root reported HTTP 410 from the desk. No 19-gate counterexample was found. All solver and runner processes under this task's SAT scratch path were stopped. `STOP_SEARCH` remains present in scratch. No search was started after the stop instruction.

These are computational searches using CaDiCaL, not Lean-checked lower bounds. An UNSAT result below concerns only the encoded candidate class or neighborhood. UNKNOWN and interrupted runs establish no exclusion. The encoder sources, complete standard output/error files, seeds, converters, runner scripts, solver commit, and SHA-256 inventory are preserved here. Older versions overwritten during preservation are retained under `history/`.

## Common candidate restrictions

The encoders use acyclic ordered gates, binary AND/OR with two different wire indices, and unary NOT. Constants and unary AND/OR are not represented. Unknown gates must be syntactically used by a later gate or an output. A maximum-predecessor ordering removes gate-order choices in unrestricted searches; hinted neighborhood searches omit that ordering. A first-gate condition, when stated below, is an additional restriction. SAT candidates are evaluated independently on every relevant truth-table assignment before they are accepted as candidates. No SAT model with zero errors was found at the requested 19-gate bound.

For one-NOT vector runs after the corresponding encoder update, the NOT gate is forbidden as an output. In fixed-bank scalar runs the NOT cannot be the final gate. These follow from the monotone target's increasing endpoint values but remain explicit encoding restrictions for audit purposes.

## Full Petersen searches

The function is the exact 15-edge Petersen function from L-meta-2592. The initial CEGIS sample consists of 72 assignments: all weights at most two, maximal independent sets, and the all-one assignment. Every proposed model is checked on all 1024 assignments; counterexamples are added if necessary.

- Generic 19-gate first-NOT-input-0, exactly one NOT: interrupted without a verdict.
- First four-error seed, at most four changed gate triples, exactly one NOT: UNSAT in 2 seconds. Six-change attempt was interrupted without a verdict.
- Moving that seed's unused NOT through slots 0–17, then allowing four changed gate triples: slots 3–17 UNSAT; slots 0–2 UNKNOWN at 30 seconds each.
- Second-orbit composed 19-gate seed has no NOT and exactly five false positives: 520, 521, 522, 552, 554. Three changed gate triples with exactly one NOT: UNSAT in 1 second. Four changed gate triples with one to three NOTs: UNSAT in 11 seconds. Five changed gate triples with one to three NOTs: UNKNOWN after 60 seconds.

The JSON summary for the last three cases is `full-repair-summary.json`. A bounded neighborhood result is not a claim about all circuits of that size.

## Six-input vector

Inputs `(a,b,c,d,e,f)` correspond to Petersen vertices `(0,2,6,4,7,8)`. Define

- `A = b ∨ d ∨ f`
- `B = a ∨ b ∨ c`
- `C = a ∨ e ∨ f`
- `D = d ∨ c ∨ e`
- `M = ad ∨ be ∨ cf`

The searched vector has outputs `(A,B,C,D,N)`, where `D ∧ N = M`; N is unconstrained where D is false. An 11-gate vector plus eight outer gates would give a 19-gate Petersen circuit.

The 11-gate, exactly-one-NOT shard with first gate OR(a,b) was UNSAT in 60 seconds. The same vector without the first-gate restriction was interrupted without a verdict. No global six-input vector lower bound is claimed.

## First seven-input orbit: subdivided claw

Add `t = x9` to the preceding six input order. The outputs are `(A,B,C,R)`, where

`R = t(d ∨ c ∨ e) ∨ ad ∨ be ∨ cf`.

A 13-gate vector plus six outer gates would give a 19-gate Petersen circuit. Both 13-gate shards with first gate OR(a,b), one with exactly one NOT and the other with exactly two NOTs, were UNKNOWN after 600 seconds each.

The final fixed-bank batch is THIS subdivided-claw family. It is not the second-orbit C6 family below. It fixes A, B, and C to six OR gates. Each triple's initial pair has three choices, giving all 27 configurations. Those six computed signals and the seven raw inputs are supplied to an unknown seven-gate scalar circuit computing R, with exactly one NOT. The NOT cannot be the final gate. All 128 input assignments are constrained.

All 27 fixed-bank configurations returned UNSAT, with no UNKNOWN cases. See `supplied-summary.json` and the individual `supplied-config*.stdout` / `.stderr` files. This excludes the fixed six-OR-bank architecture only, not arbitrary shared/interleaved 13-gate vector circuits and not arbitrary Petersen circuits.

## Second seven-input orbit: six-cycle

Inputs `(a,b,c,d,e,f,t)` correspond to Petersen vertices `(2,3,8,6,9,7,0)`. Define

- `A = t ∨ a ∨ d`
- `B = t ∨ b ∨ e`
- `C = t ∨ c ∨ f`
- `R = ab ∨ bc ∨ cd ∨ de ∨ ef ∨ fa`

A 13-gate vector plus six outer gates would give a 19-gate Petersen circuit. The unrestricted-first-gate shard with exactly one NOT, whose input is fixed to t but whose position is free, was UNKNOWN after 600 seconds.

The retained near-seed has A/B/C exact, no NOT, and R false positives only at assignments 18 and 82. Neighborhood searches allow the unique NOT on ANY earlier wire, including compound signals. Budgets count changed gate triples or changed output indices. Budgets 2, 3, 4, and 5 all returned UNSAT, in 0, 0, 1, and 6 seconds respectively. See `cycle-repair-summary.json`.

No second-orbit fixed-six-OR-bank search was run. The parent team separately reported a Lean obstruction for that architecture.

## Positive sanity examples

- A supplied exact 20-gate Petersen circuit passed the original encoder when fixed and passed an independent 1024-input check.
- The full six-input five-output vector has a planted 13-gate monotone example that passed all 320 output bits.
- Each seven-input vector has a planted 14-gate monotone example that passed all 512 output bits. Their converted 20-gate Petersen circuits passed all 1024 assignments.
- The fixed-bank encoder passed a planted ten-additional-gate scalar example containing one NOT. This validates that encoder; it is not a 19-gate counterexample.

`PETERSEN_WITNESS20.txt` and its JSON receipt contain a sanity witness of size 20, with zero NOT gates. It does NOT refute L-meta-2592. There is no `PETERSEN_WITNESS19.txt`.
