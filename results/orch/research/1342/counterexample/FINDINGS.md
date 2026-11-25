# L-meta-1342 exact synthesis and local repairs

This directory contains finite SAT/Python research evidence, not a Lean proof or a refutation. No circuit of at most 21 gates has been found. The graph has 11 vertices and the 16 edges explicitly listed in `common1342.py`. Its 16 minimal positive inputs and 24 maximal independent negative inputs form a complete boundary test for monotone circuits. Every candidate and every seed audit additionally evaluates all 2048 Boolean inputs independently.

## Circuit scope

The encoders use legal earlier-wire binary AND/OR gates. Constants, zero/one-arity gates and forward wires allowed by the broader library definition are not encoded. Junk means an AND output is true on some target-negative input, exactly checked by the 24 maximal negative rows. All impossibility claims below apply only to their stated encoding and neighborhood; none exhausts the global assigned two-junk shard.

`effective` merges identical columns on the complete 40-row boundary, then removes dead gates. This preserves correctness for a correct monotone candidate, but can change off-boundary behavior for an incorrect near-candidate, so the reduced candidate is always independently audited on all 2048 rows. Raw and effective counts are distinguished to prevent dead/copy junk padding.

## Baselines and finite audits

- There are 22 minimum vertex covers of size seven. All 22 canonical star constructions are correct 22-gate circuits, verified on all inputs.
- The expanded L-meta-1006 boundary circuit has 20 gates, six ANDs, one junk AND, 39 false negatives and no false positives. It misses six graph edges and is not a witness.
- L1006 has no exact completion among 992 one-gate extensions or 9480 single-gate rewrites with arbitrary output selection.
- The original `near-missing-2-5` has 21 raw gates/two raw junk gates, but only 20 effective gates/one effective junk gate. It misses edge {2,5}; it is not a genuine two-junk near-witness.
- The five `run-51342` row 2/6/7/11/12 snapshots have 21 effective gates and two effective junk gates. Each misses one edge. Each has no exact witness among 1056 one-gate extensions and 10472 single-gate rewrites.
- The strongest near-circuit `run-81342` row39 has 21 effective gates, seven ANDs and two genuine junk ANDs. It computes exactly the target OR the extra pair {9,10}; its four false-positive inputs are 1536,1538,1544,1546. It has no one-gate extension or single-gate rewrite producing the target.
- `unit-prefix22` and `two-junk22` are correct 22-gate seeds, not solutions to the posted 21-gate bound.

## Completed exact local exclusions

- Row39: arbitrary repairs changing at most two gates, with exactly two junk ANDs and arbitrary gate output, UNSAT in 1.373 seconds.
- Row39: at most three changed gates under the same conditions, UNSAT in 21.838 seconds.
- Two-junk22: all 32 variants obtained by deleting one gate outside its two three-gate dirty units and reconnecting all readers to either operand; at most three further gate changes, both units fixed, exactly two junk ANDs, arbitrary output: UNSAT in 42.530 seconds.
- Six counted-AND macro circuit, unlimited ORs, exactly two junk ANDs, and the first counted AND fixed to one of the five specified neutral dirty units: UNSAT in 9.493 seconds. This does not exclude seven-AND circuits or other first dirty units. The macro encoder also imposes explicitly recorded topological/commutativity ordering constraints.

These are ordinary CaDiCaL verdicts. No UNSAT proof certificate was imported into Lean. Full CNFs and full solver stdout/stderr are retained. Positive/negative encoder controls pass: fixing the known correct two-junk22 seed is SAT; fixing the incorrect row39 seed is UNSAT. The control's generated 22-gate `witness.json` is deliberately only an encoder control.

## Unresolved searches

The unrestricted six-AND/two-junk macro query timed out at 300 seconds. Local four-gate repairs of the original missing-edge seed (120 seconds), five trusted missing-edge seeds (180 seconds), and 38 deletion variants of the one-junk22 prefix seed (180 seconds) timed out. A timeout is not an exclusion. The final row39 four-change repair timed out after 180.041 seconds; the final two-junk22 deletion four-change repair timed out after 180.067 seconds. No solver remains active. Detailed results are recorded in `validation.json` and their `*-run.log` files.

The first uncached tiny-audit process was intentionally stopped for poor performance; `tiny-completion-audit.log` is an interrupted run, not a verdict. Its complete cached replacement is `tiny-completion-audit-cached.log`. The earlier environment restart occurred before these final exact-query processes and does not invalidate their completed logs.

## Reproduction

Python 3 and CaDiCaL suffice; no third-party Python packages are used. `macro_two_junk.py` records the solver path; change only that path if replaying elsewhere. The scripts use 512 MiB per local solver, 768 MiB per macro solver, explicit solver/CPU/wall-time limits, and complete file logging.

Run `python3 common1342.py` for baselines. Run `python3 macro_two_junk.py 6 300` for the unrestricted macro attempt, or append the path to `neutral-units22.json` for the five-prefix restricted query. Run `python3 local_repair.py SEED.json CHANGES SECONDS` for a local repair. The combined seed JSON files contain all variant gate lists and fixed-prefix data. The original external seeds are also included under `seeds/` in the evidence archive. Stored CNFs can be replayed directly with `cadical -t SECONDS FILE.cnf`; exact CNF SHA256 hashes are recorded in `validation.json`.


## Unlaunched successor frontier

A smaller synthesis family could allow seven counted AND gates and one or two explicitly shared pure-variable OR nodes, flatten every other OR cone, and bound the total aggregate selector count. With one extra OR gate and seven AND gates the naive unshared aggregate gate count is S-7, so S <=28 implies a valid <=21 circuit. The OR node may be chosen among the 55 input pairs. This is a possible constructive search family, not a completeness reduction; it was not implemented or run here.
