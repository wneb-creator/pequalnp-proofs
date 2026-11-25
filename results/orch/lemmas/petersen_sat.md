# L-meta-2590 constraint search

Uses installed Z3 C API version4.13.3 through ctypes. Scratch: /tmp/oec/pequalnp-pilot-144/sat2590. Exact source and SMT instances retained there.

## Validation
Known20-gate monotone baseline is SAT and verified on all1024 inputs. Thirty characteristic rows are15 minimal positive edge assignments and15 maximal independent sets. Every candidate will be verified on the full truth table.

## Running searches
- General19gate AND/OR synthesis, repeated operands allowed, backward reads, connected, canonical gate ordering.
- First gate AND(0,1); later raw OR-of-two-input functions forbidden; each gate true on at least one positive edge assignment.
- Input0 occurs exactly once, at an OR gate; otherwise same canonical19gate model, each gate true on a positive edge.
All runs have20minute timeouts and768MiB Z3 memory limits. UNSAT results would be computational evidence only, not Lean-checked proofs. Root owns normalization lemmas linking this binary model to the posted Monotone2 statement.

Canonical ordering is by larger operand, then smaller operand, then operation, after any fixed first gate. Greedily emitting ready gates by this key makes newly ready gates have larger maximum operands and removes gate-permutation symmetries.
