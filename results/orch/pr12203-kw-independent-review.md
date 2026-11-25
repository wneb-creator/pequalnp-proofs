# PR12203 KW and panel review

Source: 0xshuzo PR12203, revision 0d2bbcdeb511ffff33552e155db3526648d8575b; SHA256 5bc7f362c1cf08ca49a34dea07ed4ff386f2b393efb6261efa57a20c37f10348. Read-only mathematical review of lines3401–3827 and3906–4170 on2026-11-25.

Verdict: PASS at the source/mathematical level. No logical blocker found. This is not a claim that the complete Lean file or repository checker has passed.

The structural derivation has the necessary explicit assumptions:

- `kwFork` and `freeFork` apply only to AND/OR (`d=0` or `d=1`), with both expanded operands absent from the remaining support and the replaced output fresh. The AND selector depends only on the negative row; the OR selector depends only on the positive row. This preserves rectangle closure. Freshness prevents a replacement owner from colliding with a retained owner.
- `kwTight` assumes a false-mode live run and support cardinality exactly one more than the gate count. The width inequality forces both consumed operands to disappear at every step, yielding a tree-style rectangle partition.
- `oneShare` assumes a false-mode live run with gate count at most support cardinality. Its case split covers both operands retained (contradicts width), exactly one retained (the suffix is tight, allowing `factorKeep`), and neither retained (induction followed by `factorExpand`). There is no unproved assumption that a general circuit is a formula.
- `SingleFactor` partitions the support into disjoint inner/outer sets. Its inside rectangles separate the pivot; outside rectangles either separate the final target or defer to the pivot. `freeHide`, `supportSide`, and the two expansion cases preserve this cover and disjointness.
- `onlyWire` is used with room totality or explicit support membership. The proof does not assume that its designated signal exists or separates merely from its universal uniqueness clause.
- `hornRule` and `parityRule` follow from rectangle closure, totality, uniqueness, and partition disjointness. They need no monotonicity assumption on the individual supplied signals; the operation-mode restriction is on the live run itself.

For all seven panel lemmas, an independent script checked that each referenced cell belongs to the declared tag list, all wire indices lie inside the declared arity, every parity rectangle has the correct shared row/column coordinates and distinct wires, and every Horn implication uses matching target-row/column corners. Exhaustive enumeration of128 total Boolean inner-membership assignments found no satisfying assignment for any panel's derived constraints.

Structured panel results: `results/orch/pr12203-panels-independent.json`. Audit script: `/tmp/oec/pequalnp-pilot-61/audit_panels12203.py`.
