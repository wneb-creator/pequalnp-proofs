# L-meta-997 — checked partial results

The general light/heavy overlap compensation remains unproved. Exact full-signature refunds cannot be inferred from arbitrary partial-support overlaps. The separately preserved fresh/SmallWindow.lean covers only |y|<=2.

- `RefundOutputs.lean`: Exact output-gate refund injection and bounded-heavy-size arithmetic.
- `BoundedCase.lean`: Self-contained proof under the additional assumptions that |y| is positive and every disjoint piece has size at most |y|+1.
- `WeightedFrontier.lean`: Abstract shared-DAG frontier bound with free unary and paid binary expansions.

The complete successful compiler logs are preserved beside each source; empty logs mean the compiler emitted no stdout or stderr. `manifest.json` records exact source hashes and the preservation recheck. These files do not constitute a completed target proof, and the posted-statement checker has not accepted them as one.

The accompanying reports distinguish checked helper lemmas from unproved strategies and restricted finite searches. No failed diagnostic logs or large SAT artifacts are included.

KIT-MESSAGE-ID: msg-9574e75c4a2464ba7a74e928
