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

## Additional checked setup
Exhaustive Python enumeration confirms76false assignments,15maximal false assignments, and maximum independent-set size4.

One-gate repair of the19-gate near-witness is UNSAT with repeated operands allowed (see repair1-repeat/result.json); this is only a bounded neighborhood result.

The broad single0OR trial was interrupted to incorporate Lean-compiled helper restrictions from structural2590/dirty-blocks.lean and symmetry.lean. In the new trial the other operand h of the unique OR reading0 is false on all maximal-false rows except201and773; symmetry requires h773 implies h201. These correspond to independent triples200and772 becauseh ignores0. Neither/one/both exceptional patterns remain permitted. The new trial runs with QF_BV-specific Z3 solver.

Two-gate local repair (repetitionallowed) returned UNSAT in6.86s. Three-gate repair has nowfinished; exactstatus in sat2590/repair3-repeat/result.json. The20-gate knownbaseline also satisfies the nonedgeOR-first branch after a checked inputautomorphism, canonical reorder, positive-live pruning, no rawedgeOR, and71truthrows including allrank≤2assignments; full1024 verification stillpasses.

## Lease-loss pause
At 2026-11-25T15:25:32.902641+00:00 root reported no live lease, so all four active solver processes were terminated immediately. General19gate, first-edge-AND, strengthened single0OR, andfour-gate localrepair runs have no verdict. Completed localrepair radii1,2,3 (repeated operandsallowed) are UNSAT in2.45s,6.86s,99.08s respectively. No counterexample found. Awaiting explicit leaseconfirmation before anymore work. Fullproblems/logs retained in scratch/sat2590.
