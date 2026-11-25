# Structural route

Assigned statement: L-meta-2592, Petersen edge function, circuit size at most 19 with at least one NOT gate.

## Findings

- `FanInTwo` restricts every operation to AND, OR, NOT and every operand list to length at most two. Invalid reads evaluate to false; nullary gates are admitted. This is a genuine circuit problem, with no malformed-index shortcut apparent.
- All three reduction slots are already occupied on upstream main: `R_meta_2592_271`, `_318`, `_408`.
- `_271` splits at a non-NOT floor of 15, leaving circuits with one through four NOT gates.
- `_318` cuts at the final NOT gate; its prefix may contain other NOT gates, while its suffix is monotone. The difficult separator remains unproved.
- `_408` normalizes invalid wires, unused NOT operands and output placement, then asks a finite normalized rejection.

## Partial formalization

`results/orch/lemmas/Structural.lean` contains self-contained lemmas:

1. `splitLastNot`: choose the last NOT from any gate list containing one.
2. `wiresLength`: evaluation appends exactly one wire per gate.
3. `cutLast`: the exact generic decomposition hypothesis of `_318`, with exact size accounting and evaluator identity.

The prefix output uses the NOT operand's head, defaulting to `n + pre.length`. The default is deliberately beyond the prefix's wires, so a nullary NOT evaluates correctly. The suffix retains all original indices.

This file is awaiting a Lean executable; it is not yet checked.

## Existing lower-bound machinery

`L_meta_11365` has a roughly 3200-line self-contained framework proving a binary-gate lower bound via branch classes and graph twins. Its final one-NOT elimination theorem ignores the uniqueness hypothesis: any NOT adds enough cost above its binary floor to permit replacement by a fixed monotone witness.

`L_meta_2517` proves a 16-gate lower bound for the nine-vertex Petersen deletion case with at least two NOT gates. It derives a bound on non-NOT gates, obtains a terminal branch class and finishes by a finite cover rejection. Its final specialized proof is around lines 4631–4646.

Neither gives the full 20-gate Petersen bound directly. The `lean_route` agent is investigating adaptation of this machinery, while `case_bounds` handles the weaker weighted-support floor.
