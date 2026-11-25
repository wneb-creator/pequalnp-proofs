# Independent raw-input fanout review

Reviewer: lower_bound. Date: 2026-11-25, approximately 08:20 UTC. Verdict: PASS for the new postprocessor and its append-only composition. This is an encoding review, not a solved 26-gate instance or an UNSAT certificate.

Reviewed source: `/tmp/oec/pequalnp-pilot-70/circuit-search/add_raw_fanout.py`.
Independent audit source: `/tmp/oec/pequalnp-pilot-70/lower-bound/review_raw_fanout.py`.
All three independent audit processes exited 0.

## Mathematical condition

Suppose a circuit gate has distinct raw inputs x and y, and x has no other direct consumer. Fixing y to that gate's canalizing value makes the gate constant, so the output cannot depend on x. This does not require circuit minimality or liveness.

For an AND gate, Heawood's degree-three condition provides a neighbor z of x different from y. Setting z=1, y=0, and all other inputs except x to 0 leaves the exact target dependent on x. For an OR gate, if x and y are adjacent, the assignments with y=1 and every other variable except x zero already distinguish x. If they are nonadjacent, distinct degree-three neighborhoods with at most one common neighbor provide z in N(x) outside N(y); set y=z=1 and all other variables except x zero. Again the target depends on x. The same reasoning applies to y. Thus every such raw-pair gate needs a second direct consumer of each input. The audit independently found all 364 ordered-pair/operation distinguishing assignments.

## Clause review

For every gate i and raw pair a<b, the two added clauses are the implication from `left_i=a AND right_i=b` to another gate selecting a, and the corresponding implication for b. Each consequent includes both selectors of every other gate, excludes gate i itself, and uses the original selector IDs. There is no operation guard because the argument applies to AND and OR. Repeated fanins are not constrained. The base generator already orders left<=right; even without that convention the omitted reverse orientation would only weaken the pruning.

For 26 gates this is exactly `26 * choose(14,2) * 2 = 4732` clauses, each with 52 literals. No variables are added. The independent audit reconstructed every added clause, checked all original clauses and all non-header source lines unchanged, checked all metadata except the expected count/new annotation unchanged, and verified every reference lies within the original variable range.

| Artifact | Base clauses preserved | New clauses | Variables unchanged |
| --- | ---: | ---: | ---: |
| raw-fanout26 | 182397 | 4732 | 7203 |
| raw-fanout27-smoke | 193334 | 4914 | 7615 |
| general-or26-fanout | 365450 | 4732 | 38333 |

The actual next-run final CNF has 370182 clauses and SHA256 `f870da9b0683e0055ee77c830296a760e84b38f9185d2803288ad0a01df26024`. Its base already contains the separately reviewed third-gate symmetry, shadow-three condition, prefix-20 restriction and final-OR condition. This review establishes that the fanout addition leaves that base untouched; it does not independently re-prove those earlier restrictions.

## Known-target smoke

The existing 27-gate model satisfies all 198248 original and new clauses, including all 4914 fanout clauses. I independently decoded/check-matched every left selector, right selector and operation bit against its witness, then evaluated the circuit on all 16384 assignments. Every output equals the posted Heawood edge function.

Complete logs:

- `/tmp/oec/pequalnp-pilot-70/lower-bound/raw-fanout26-independent-review.log`
- `/tmp/oec/pequalnp-pilot-70/lower-bound/raw-fanout27-independent-review.log`
- `/tmp/oec/pequalnp-pilot-70/lower-bound/general-or26-fanout-independent-review.log`

No new solver run or Lean build was launched for this review. No full-instance UNSAT conclusion follows from it.
