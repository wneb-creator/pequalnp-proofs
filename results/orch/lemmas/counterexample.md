# Counterexample search: L-meta-2592

No valid counterexample has been found. Every reported near-circuit is explicitly an approximation; none is a Lean-checked result.

## Models and tools

The circuit definitions have no immediate semantic loophole: only AND, OR, and NOT gates, at most two operands, sequential evaluation, and invalid reads equal false. Official Z3 5.3.3 is installed in the task scratch directory. Its Python package is `counterexample/z3-5.3.3-x64-glibc-2.39/bin/python` below `/tmp/oec/pequalnp-pilot-109/`.

The first synthesis model uses 19 explicit gates. Each candidate is evaluated independently on all 1024 assignments. The initial 91 samples are all 76 negative inputs and the 15 positive edge pairs. Denser runs use 192 samples. Search restrictions include no constants, nonredundant binary gates, live gates, and output last, so these are witness searches, not exhaustive proofs.

Avoid pseudo-Boolean cardinality in the QF_BV solver: it selected a slower SMT-style engine. Pure bitvector sums keep SAT bitblasting. All diagnostics are retained in complete scratch log files.

## Completed searches

- Generic explicit models with one, two, or three NOTs returned UNKNOWN at 600 seconds. The three-NOT run fixed its first gate to AND of adjacent vertices. A separate four-NOT run with that first gate also timed out.
- Full five-gate repair of the first near-circuit's core, over seven raw variables and eight available OR wires, returned UNSAT in 1.84 seconds. This excludes only that fixed architecture.
- Keeping the final form `A AND (x3 OR H)`, exhaustive search found no suitable three-gate H with a NOT: 2,116,800 terminal sequences checked.
- At most two gate replacements of the four-error near-circuit were ruled out independently: 25,724,328 replacements checked in C++ in 8.43 seconds, and SAT returned UNSAT in 47.59 seconds. These results are not Lean-certified.
- Initial stochastic search tested 2,094,650,000 candidates in 600 seconds, best eight actual errors. A pair-prioritizing run tested 519,100,000 candidates in 300 seconds, best nine errors.

## Four-error near-circuit

`near-three-extra.json` is misnamed: it has FOUR false positives and no false negatives. It consists of 18 live monotone gates and a dead NOT. It agrees with the target on 1020 of 1024 assignments. The false positives are:

- 69: vertices {0, 2, 6}
- 104: vertices {3, 5, 6}
- 521: vertices {0, 3, 9}
- 548: vertices {2, 5, 9}

Removing a maximum independent four-set from Petersen leaves three disjoint edges. The four neighbor ORs can be identified with the four vertex stars of K4 on those six residual variables. Their conjunction detects an edge cover, while the target requires a matching. The four spurious assignments are exactly the four K4 star triples.

This led the definition-audit agent to synthesize a six-input, five-output family: four neighbor ORs and the three-pair matching function. A family with at most 11 gates including a NOT would give a 19-gate Petersen circuit. A 12-gate family may suffice if its matching output ends with the right factored AND.

## Current work

The signed model with 16 binary gates and at most three distinct negated sources, 30 boundary samples, and first gate OR of a nonedge pair returned UNKNOWN(timeout) after600.08 seconds without a candidate. Log: `signed16-n3-boundary.log`.

A stronger successor is prepared in `signed16_branch.py`. The structural agent confirmed that 16 binary gates permit total fanout excess seven but require at least six branches with nonempty first-input classes. The model imposes expanded fanout at most three and propagates ten-bit first-input masks to require those six classes. It was sanity-checked on the known 20-gate monotone circuit: SAT in 0.42 seconds and independently correct on all 1024 assignments. That benchmark is not a new result.

The final stochastic run completed 1,538,600,000 trials in its bounded run. It used the four-error seed, neutral adjacent gate swaps, and simultaneous changes to two or three gates. The best remained four errors. It had already exited normally when root requested CPU reduction; no incomplete result is being claimed.

All sources, candidates, and full logs are under `/tmp/oec/pequalnp-pilot-109/counterexample/`. No desk requests, git mutations, or final Lean file edits were made by this agent.

Resource coordination: the container has four CPU cores. All searches launched by this agent have exited. The single solver slot was handed to the finite-bound agent for its signed15 twins model. The stronger16-binary script is prepared for a later allocation.

## Independent review

Reviewed final-file SHA256 `af3544446f1283c08d107db1a620766ea3a4257c98d5a3eeea1c967a834438e0`:3426 lines,155776 bytes, ordinary non-executable UTF-8. No forbidden tokens, strings, new axioms, instances, data types, or disallowed imports found. New total-budget normalization lemmas preserve total size and non-NOT bounds; the four-NOT specialization correctly forces15 binary gates. The file is still partial: it has no final theorem with the exact target name, so the format guard refuses it for that expected reason. Full guard output is in `red-team-guard.log`. This is not checker acceptance.

Also supplied the maximal-negative/minimal-positive reduction for the library agent’s sole-NOT operand classification: monotonicity reduces17 symmetry orbits to5. The library agent is now checking its Lean certificate.

## Prepared five-case sole-NOT search

Root requested preparation only; no SMT runs were launched. `five_cases/search.py` and its README are in this agent's scratch directory. Cases are (M,e)=(50,3),(50,6),(50,12),(116,3),(116,6), with bit i=xi. The library agent confirmed its checked permutation convention and reviewed the stronger constraints forcing the NOT output to true at M and false at e. Each candidate must pass independent evaluation on all1024 inputs. There is a separate `--monotone18` mode for dead/inessential NOTs, with a dead NOT appended to any verified monotone witness. Default equal-input binary gates permit padding smaller circuits. Syntax compilation and six static dry runs passed; no Z3 search was invoked.

## Draft constant-wire normalization

Root requested a remaining signed-input normalization. Existing `CircuitProof.drop_core` already supports constants through `Sum.inl c`. Draft `/tmp/oec/pequalnp-pilot-109/counterexample/NoComplementaryInputs.lean` proves:

- `drop_constant`: replace a semantically constant gate by a constant status and clean the suffix, strictly decreasing total gate count while not increasing non-NOT count.
- `Least.no_constant`: a Least circuit computing a nonconstant function has no constant gate wire.
- `Least.no_complementary_inputs`: a binary AND/OR gate in such a circuit cannot read pointwise complementary wire functions.

The draft has not been Lean-checked yet. No heavy build was started while the structural/library proof slots were occupied.
