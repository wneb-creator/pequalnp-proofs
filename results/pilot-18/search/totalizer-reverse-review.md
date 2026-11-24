# Reverse totalizer clauses: PASS, not integrated

The proposed clauses are sound and preserve the existential projection of
the reviewed forward totalizer, including signed input literals and its
truncated counters. This audit does not change any generator or search CNF.
The source audited was `search_l1342_shard17_ancestorcost.py`, SHA256
`60a37d85580f1190e3dac3793610a6d90197c90f2cde08520ec79269be3f5997`.

For each merge, use zero-based array indices and add exactly:

    for i = 0 .. len(left), j = 0 .. len(right), i+j < len(out):
        NOT out[i+j]
        OR left[i]  (only if i < len(left))
        OR right[j] (only if j < len(right))

This says that threshold `C_(i+j+1)` implies `A_(i+1)` or `B_(j+1)`.
The terminal index is included in each loop; a missing child threshold is
false, not true. Use the same positive cap throughout the recursive tree.

## Projection argument

Assign every auxiliary threshold its exact meaning: at least that many
signed input literals in its subtree are true. If the parent count is at
least `i+j+1`, one child count exceeds its chosen index. Therefore this exact
assignment satisfies every reverse clause as well as every old forward
clause. Truncation does not invalidate an omitted child literal: if its
array ended because it reached cap, choosing that terminal index would give
`i+j >= cap >= len(out)`, and this reverse clause would not be generated.
Otherwise the child's entire subtree is exhausted and its next threshold
really is false. Thus every old admissible input assignment still has an
extension, with all final overflow guards preserved.

Conversely the enlarged CNF includes every original forward clause, so it
cannot admit a new projected input assignment. In fact it makes all stored
thresholds exact. Inductively suppose both children's thresholds are exact.
Forward clauses force each parent threshold up to the actual count. For a
threshold above that count, distribute its predecessor index between the
children, with each index at least that child's actual count and no greater
than its array length. Such a distribution exists because the parent stores
that threshold. The associated reverse clause has both child literals false
or absent, forcing the parent threshold false. This also explains why input
fixing propagates every auxiliary flag in the finite controls.

Signed or repeated input literals cause no special problem: counts are over
literal occurrences. The exact assignment remains well defined even when
two occurrences are complementary. No new variables are introduced.

## Finite audit

`review_totalizer_reverse.py` extracts the actual forward helper and compares
it with a separate merge implementation. All original forward clauses,
variable allocation, and output arrays agree exactly. Controls passed:

- 135 gadgets and 12,291 input assignments, sizes 0 through 8, caps 1 through
  size+1, with positive, negative, and alternating signed inputs.
- 36,327 complete auxiliary assignments exhaustively tested for the 387
  small input cases through size 4: exactly one extension in each case.
- 85 additional assignments with repeated and complementary literals.
- 1,088 assignments at the actual 17 ancestor-counter sizes: 38+g leaves,
  cap g+3, with negative ancestor literals. Includes all-false and all-true
  underlying assignments as well as deterministic random assignments.

For every control, the exact extension satisfied every clause; unit
propagation fixed all auxiliary variables to that extension; all represented
at-most thresholds matched the direct literal count. JSON records per-gate
counts and source hashes. Full test stdout/stderr are preserved separately;
the test exited 0 with empty stderr. No SAT solver was started.

For these seventeen counters, the change would add 10,325 clauses and zero
variables to the existing 10,920 forward-counter clauses. This roughly
doubles the counter clauses, although it is a smaller fraction of each
complete search CNF. Better propagation is plausible; runtime and memory
effects have not been measured and may be unfavorable. The change remains
an optional future variant, pending main's review. It has not been added to
the constant variant or any running case. No SAT/UNSAT search conclusion is
drawn from these finite encoding controls.
