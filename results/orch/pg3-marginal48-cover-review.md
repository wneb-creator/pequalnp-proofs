Independent review verdict: PASS for the extension-cover lemma and the two fixed-base cover obstructions.

Let f_i be a fixed finite collection of old Boolean wire functions, P a nonempty set of positive samples, and v one negative sample. An append-only extension uses these functions, arbitrary AND gates and at most K binary OR gates. Suppose its output is true on P and false at v. Then P is covered by the positive-sample supports of at most K+1 old wires that are false at v. No monotonicity assumption on the underlying old functions is necessary.

Proof: maintain a set-valued OR frontier whose disjunction pointwise dominates the original output. Initially it contains only the output wire, which is false at v. Expand the highest-index new gate still on the frontier. For an AND gate false at v, select one operand false at v and replace the gate with that operand; this preserves domination and does not increase frontier size. For a binary OR false at v, both operands are false at v; replace it with both, increasing frontier size by at most one. Deduplicate the frontier. A nullary false OR can be removed, while a nullary true AND cannot occur on the false frontier. Processing in descending gate order ensures that no expanded new gate can reappear, so at most K expansions increase size. The final frontier contains at most K+1 old false wires, and its OR is true on every positive sample.

Consequently, if the smallest old-false-wire cover has size c, every such extension needs at least c-1 appended OR gates. For separating P from this one v, the bound is exact: OR together a minimum cover. If desired, AND that OR with the existing base output; this adds no OR and preserves the positive samples when the base already accepts them.

The scope is a fixed old-wire collection and append-only extension. The claim counts only new ORs. Turning it into a total 48+K bound requires retaining all 48 base OR gates. Arbitrary changes to the base, replacement of its internal functions, or deleting unused base OR gates are outside that total-count conclusion. The exact one-negative upper bound does not establish an upper bound for repairing all generic negatives simultaneously.

Independent finite audit rebuilt all 98 old wires of the stated circuit: 26 primary inputs, 48 OR gates and 24 AND gates. It verified the affine/infinity labels directly against Singer incidence p-l in {0,1,3,9}, and verified that the supplied positive samples are exactly the 52 distinct incident pairs. It then recomputed all old-wire positive supports and their values at the two selected negatives. Zero supports were discarded; replacing a support by a larger available false support preserves covering ability, so considering only the 12 maximal supports is exact.

For the mixed triple with points{2,5} and line{3} (input mask 65572), there are 64 distinct nonempty false supports and 12 maximal ones. Enumerating all 4096 subsets independently by dynamic programming gives maximum covered-flag counts for 1 through 8 selected supports:

16,28,36,43,46,49,50,52.

The minimum cover is 8, and the report's eight-support witness covers every flag. Thus at least 7 appended OR gates are needed to fix this one triple.

For the generic row with points{0,1,5} and lines{3,6,7,8} (input mask 3735587), there are 54 distinct nonempty false supports and 12 maximal ones. The audit also verified directly that this row is maximal and generic. The maximum covered-flag counts for 1 through 9 supports are:

21,30,36,42,46, 48,50,51,52.

The minimum cover is 9, and the report's nine-support witness covers every flag. Thus at least 8 appended OR gates are needed to fix this one generic row. Keeping the 48-OR base therefore forces at least 56 total OR gates, ruling out a repair to 50 by this append-only strategy.

These are ordinary finite Python checks accompanying the mathematical lemma; no Lean theorem or solver was invoked during this review.

Pinned source and audit artifacts:

- Reviewed pg3-marginal48.py SHA256: 353ff8743b256c85f35c4b134b891180cab3e0476ac3d9f79f2d588b961a7d95.
- Reviewed original report SHA256: 160ca256470458c9c3ab56239fb2ccbdd5fd9e18c75c332a6d4f1fa1604b3cad.
- Portable audit script results/orch/pg3-marginal48-cover-audit.py SHA256: 120b2ccf3d5c4cd6ecaf43d53ba7833e89e8b154a7f7b8e999f980cb6106384e.
- Audit input data SHA256: 3a317ab2c4571d7d3aac97317d4f8f98e2fc96117881d5017c1dd6a1a398a20b.
- Complete audit stdout/stderr results/orch/pg3-marginal48-cover-audit.log SHA256: 0fb0cf4323d8da1d53d41987d664f0f197592335cc369397f8fb385caffd7e18; exit 0.
