# Prefix cover-cost encoding review

**Verdict: PASS. No blocking encoding concern found.**

Reviewed source: `search_l1342_shard17_cost.py`, SHA-256
`f3236024e27aed9aa90356e442d4644e5f8920609a3f922cac9ddab5387a5d06`.
This review checks implementation and finite CNF projections. The gate lower
bound is a separate mathematical obligation; main reports that the companion
mathematical review and all 2,048 table entries independently passed.

All definitions inherited from the reviewed copy-chain generator are
AST-identical. The only new helpers are `support_cost_bounds`, `forbidden_cubes`,
and `add_prefix_cover_cost`; the main entry point applies the new cut before
writing the base CNF and allocating lex flags.

## Cost table

For every proper support S, the table implements
`|S| + m(G-S) + tau(G-S) - 1`. The expression counting edges correctly selects
edges with neither endpoint in S. Minimizing `|C-S|` over global vertex covers C
equals the minimum cover size of the induced graph G-S: restriction gives one
direction, and extending any induced cover by S gives the other direction.

The review independently computed each induced cover number by branching on an
uncovered induced edge, rather than enumerating global covers. All 2,048 entries
match. Empty support has bound 22. Full support is assigned sentinel zero and is
never forbidden, preserving the free-TRUE exemption. The sentinel is not a claim
that every full-support function can be computed with zero gates.

## Cover flags and cube clauses

For gate g in 0 through 16, `cover_flag` is equivalent to the conjunction of its
sixteen exact minimal-edge values: sixteen forward implications plus one reverse
implication. The audit exhausted all 131,072 assignments to the sixteen edge bits
and flag. The indexed wire is `13+g`, and the available gate budget is `g+1`,
including the current gate.

Quine–McCluskey merging combines adjacent forbidden cubes of equal care masks;
each merged cube is precisely the union of its two children. The greedy cover
selects only forbidden cubes and covers every forbidden minterm. Independently,
the audit evaluated both the chosen cube union and the actual signed CNF clauses
on all 2,048 supports at each of the seventeen budgets. Both match exactly
`bound(S) > g+1`. This checks 34,816 support/budget pairs.

The emitted clause is `not cover_flag OR mismatch_with_cube`. A cared bit whose
cube value is one contributes a negative support literal; a zero contributes a
positive literal. Thus a covering wire is rejected exactly on forbidden patterns.
When the cover flag is false, every support pattern remains permitted. Full
support remains permitted at every budget. Empty and universal forbidden sets
were also checked directly against the cube helper.

The delta is **17 fresh variables and 1,287 clauses**: 289 cover-equivalence
clauses and 998 forbidden-cube clauses. Cover flags occupy IDs 6134 through 6150.
The 32 lex equality flags start at 6151, so the allocations are disjoint.

## Saved artifact audit

All ten saved CNFs and metadata files were read: base, lex, distinct, and seven
tail templates. Every SHA-256, header count, clause count, and literal range
matches. Each complete clause sequence equals its previously reviewed copy-chain
counterpart with existing lex flag IDs shifted by 17 and the exact 1,287-clause
cost delta inserted at the expected position. Existing clauses are otherwise
unchanged. The seven tails retain the entire cost cut and still disable the
suffix junk requirements explicitly. Source hashes and metadata copies agree.

The audit writes no CNF, modifies no generator or repository file, invokes no
solver or build, and makes no desk call. Full diagnostic output is retained in
`cost-encoding-review.stdout.txt` and `cost-encoding-review.stderr.txt`; the latter
is empty. `review_cost_encoding.py` reproduces these bounded checks from the saved
artifacts, and `cost-encoding-review.json` records their hashes and counts.

The generator uses assertions for its internal projection checks, so those
checks require ordinary Python rather than `python -O`. This independent audit
ran with assertions enabled. The SAT witness validator already checks every
cost clause through its full CNF audit, but does not yet expose a separate
semantic `prefix_cover_cost` report field. Neither point blocks use of the
reviewed, hash-verified instances. No SAT, UNSAT, exhaustion, Lean proof, or
posted-gap acceptance verdict is established by this encoding review.
