# Small marked-edge experiments

Finite exhaustive proper-circuit enumeration using complete truth tables plus both formal derivative bits. These are computational research results, not Lean proofs or refutations of the plane statement. Each new gate uses two distinct earlier wires; equivalent new-wire signatures are deduplicated only within one fixed prefix, preserving all future gate possibilities. All returned witnesses were independently checked with scalar Boolean and derivative evaluation.

| Graph | Marked edge | Minimum gates with both traces zero |
|---|---|---:|
| One edge, with an isolated third input | its edge | 3 |
| Two-edge star | a leaf edge | 4 |
| Two-edge matching | either edge | 4 |
| P4 | outer edge | 5 |
| P4 | middle edge | 6 |

The last lower bound exhausts through five gates; the six-gate upper witness duplicates a standard four-gate output AND and ANDs the two copies. Full data and search counts are in `small-marked-results.json`; output is in `small-marked-enum.log`.

Every-gate-essential does not imply removable repeated-AND witnesses: the four-gate matching circuit is already optimal under the two-zero requirement. A redundant OR dominated by an earlier gate can instead be overwritten by a copy of that gate, retaining physical distinctness and reducing a well-founded input-index measure while preserving all edge values and decreasing ordinary/derivative semantics. Original-input-dominated aliases need separate treatment; unmarked inputs have zero signatures at both bases, whereas the two marked inputs retain the duplication obstruction.
