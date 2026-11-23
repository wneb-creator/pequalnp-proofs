# Resume state after lease expiry

Work stopped when the parent reported the expired lease and completed the required diagnostic retry. This note preserves already completed work; it does not authorize a new desk request or further work on that lease.

The parent reported complete computational exhaustion for all 31 cases. The full posted conjunction has not been assembled and kernel checked. Generic checker proofs and several concrete/structural results are checked; they must not be described as the complete gap proof.

## Current checked APIs

All helper namespaces below start with `PEqualNP.Outside.L_meta_982_aux.Finite`.

- `Reduced.lookupBar_all_le` and its `_from_leaves` variant, in `Indexed982`: the hint receives the actual child and returns an index plus oriented list. The checker always verifies the returned index bound and actual list permutation. Arbitrary lookup mistakes or collisions can only prevent a certificate from checking. Rejection is an abstract Boolean predicate with a no-run soundness premise.
- `Reduced.orbitLookup`, in `OrbitLookup982`: tries each supplied action and stops only after both an in-range index and an exact list-permutation match. `orbitLookup_run` proves transport independently of the lookup algorithm.
- `Reduced.binaryFind` / `binaryOrbitHint`, in `BinaryHint982`: structurally sorts a short child list and lexicographically searches the supplied state accessor. The accessor is abstract and can use radix32 storage. Search failure returns the bound. The transport theorem does not assume sortedness; the concrete closure checks still must succeed.
- `SliceOpt.scr k p s ws`, in `SliceOpt982`: bit-sliced value6 rejection with early termination. `scr_no_le` requires `3*p <= k` and rejects no actual run of budget at most s.
- `OldCoverage.covers k p s ws`, in `OldCoverage982`: checks only the original pair columns, not duplicated score columns. `covers_ok_le` is unconditional in p. `OldCoverage.bad` combines this with SliceOpt.scr; `OldCoverage.reject` uses the checked generic `Reduced.rejectWith` DFS.

The re-encoded word has half-width k. D/E/F score blocks occupy offsets 0,p,2p; A/B/C occupy k,k+p,k+2p. Original negative columns begin at 3p, and original positive columns at k+3p, each with width k-3p. Keeping score copies below old columns preserves old numeric word order when the copies are consistent.

## PairReplay integration

`PairReplay982` is checked and contains no per-bit symmetry computation in its evaluator. It uses existing pairs of naturals, not a new datatype.

1. Choose a certified symmetry function f. Supply f(0)=0 and its preservation of XOR(mask), AND and OR. The symmetry agent is exposing these for Grouped.word, together with arbitrary-run transport of List.map f.
2. Build root pairs `(original input word, certified image input word)`, in the original root order, and prove `PairReplay.Rel f rootPairs`.
3. Reuse the Huffman decoder's parent/tag records. `PairReplay.state cap mask rootPairs records s i` applies gates componentwise and sorts only by the original word. `rel_state` proves `snd = f fst` throughout, including default getD pairs.
4. `PairReplay.child ... s i tag` applies the proposed transition. `child_rel` supplies the same relation for that child.
5. `PairReplay.guarded child ys` checks `ys.isPerm (child.map Prod.fst)` at runtime. On success it returns the image list; on failure it returns ys. `guarded_run` proves arbitrary-run transport. No proof that the tag or replay agrees with the actual transition is assumed.
6. Search the returned image using binaryFind and retain lookupBar's final exact permutation guard. Per-parent/tag action closures can be formed for the finite symmetry family and passed to orbitLookup.

The checked PairReplay.state is direct recursive replay. A radix-cached paired-layer implementation still needs its own Rel preservation proof or an equality to direct replay. Do not assume global memoization from a pure definition.

## Dependencies and integration cautions

Use the import-free append files for the final standalone proof. Cached scratch modules import one another only to accelerate development. The final project import remains PEqualNP.Defs, plus Mathlib imports.

The newest preferred direction is finite-only proof infrastructure, roughly 92 KB before newer evaluator/hint helpers. The earlier 244,917-byte `Combined982Compact.lean` includes a 158 KB structural prefix and was superseded as a size strategy when all 31 finite searches closed. It remains a valid checked checkpoint.

Complete sources and stdout/stderr logs are listed with hashes in `proof-strategy-stop-manifest.json`. Slice, SliceOpt and OldCoverage had independent PASS audits. PairReplay and Binary were being independently reviewed by the parent-appointed auditor at the stop.

## Measured limits

- One concrete core28 binary lookup among 1,439 states passed in 10.890 seconds, including imports and source elaboration. See BinaryCore28Lookup.timing.json. This is not a full-closure throughput measurement.
- A monolithic earlier reduced-seed0 DFS was killed with exit137 and proved nothing.
- The scalar 108-node core28 DFS was stopped after about177 seconds without a proof; the first bit-sliced version subsequently checked that leaf. The root recorded its timing and later evaluator benchmarks.
- Kernel Array getD can expose backing-list access costs; use the tested radix32 decoder variants.
- Packed extraction should use division by powers of two rather than shiftRight. List.mergeSort failed kernel reduction even on `[3,1]`; structural insertion sort passed. Nat.log2 itself passed the isolated tiny test.

A final proof still needs concrete closure assembly, full independent review, the named-file lake build, the local checker, the source-size check (512 KiB), and validation under the CI time/memory limits. No claim that these whole-proof checks passed is made here.
