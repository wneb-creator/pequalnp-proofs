# Independent unique-input encoding review

Reviewer: lower_bound. Date: 2026-11-25. Verdict: PASS for the alternative unique-input normal form and the prepared CNF. No target-budget solver was launched during this review, and no SAT or UNSAT result for 26 gates is claimed.

## Mathematical normal form

After the standard removal of unused gates and constant/invalid references, a live valid binary circuit with m gates uses at most m+1 raw-input occurrences: its m-1 nonoutput gates each require an internal fanin occurrence among at most 2m total occurrences. All 14 variables of the assigned edge function are essential, so at m<=26 at least one raw input occurs exactly once. The independently checked `RawOccurrence.lean` component proves the counting step under explicit used-input and live-reference premises; semantic normalization remains a separate argument.

The exact assignment graph is vertex-transitive. The independent audit enumerated 168 part-preserving automorphisms, found a part-exchanging polarity, and checked all 336 resulting permutations preserve the 21 edges and send vertex 0 to every vertex. Thus the uniquely occurring input may be relabeled 0. The alternative drops the old full-group canonical prefix. A smaller live witness can be padded with repeated-output OR gates without adding any raw-0 occurrence; the fixed 28-gate regression explicitly tests such padding.

Let the unique consumer be `op(0,W)`. Sorted fanins and exactly one occurrence among both fanin slots rule out raw 0 on the right, including the repeated pair `(0,0)`. W is independent of 0. On each of the 25 maximal false rows omitting 0, toggling 0 makes the target true; maximality ensures a neighbor of 0 is present. The same sensitivity is witnessed at the three incident positive edge rows and their corresponding singleton restrictions. Therefore W must be true for AND and false for OR on all 28 encoded rows. The postprocessor correctly enforces `W = NOT(op)` when the gate's left input is 0, with true operation bit meaning OR.

The independently reviewed raw-pair fanout clauses remain necessary and imply that unique 0's other input is a computed wire, without adding an unproved clean-prefix restriction. Adjacent independent-gate lex ordering and liveness remain enabled; the no-canonical-prefix, repeated-fanin, and trivial-wire settings avoid conflicting with the new normalization or padding.

## Exact artifact checks

`unique_input_base.py` differs from the reviewed `repair_base.py` in exactly one metadata entry: it records the already existing `lv` and `rv` variables. The independently generated permissive 26-gate CNFs are byte-identical. The audit reconstructed every added clause, checked original clauses/IDs and unrelated metadata unchanged, verified all eight consumer/operation/other-value truth assignments, and checked the complete set of critical masks directly against the target graph.

| Instance | Base clauses | Exactly-one additions | Critical additions | Fanout additions | Final clauses | Variables |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| unique0-26-permissive | 201311 | 1327 | 1456 | 4732 | 208826 | 7253 |
| unique0-27-smoke | 213513 | 1432 | 1512 | 4914 | 221371 | 7586 |
| unique0-28-pad | 226073 | 1541 | 1568 | 5096 | 234278 | 7923 |

The 27- and 28-gate fixed-model files append 81 and 84 gate-fixing units, respectively. Both complete model assignments satisfy every clause. Their decoded circuits each independently pass all 16384 inputs; both use raw 0 exactly once. The 28th gate is the repeated-output OR `(40,40)`, confirming padding compatibility.

Final 26-gate CNF SHA256: `86c036aaf5381cf4d574958b036eb8e32fa257d525fb2e4dd4fa2a33f4c86244`.

- Independent audit: `/tmp/oec/pequalnp-pilot-70/lower-bound/review_unique_input.py`
- Complete exit-0 log: `/tmp/oec/pequalnp-pilot-70/lower-bound/unique-input-independent-review.log`
- Source/artifacts: `/tmp/oec/pequalnp-pilot-70/circuit-search/unique_input_base.py`, `add_unique_input.py`, and `unique0-26-permissive-*`.

These checks support this complete alternative search architecture mathematically and computationally. They are not a Lean formalization of every normalization step or an UNSAT certificate.
