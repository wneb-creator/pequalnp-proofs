# Independent review: compact RUP checker and semantic bridges

Verdict: PASS for the checked generic checker and its ordinary, weak,
and paired-budget initial-clause bridges. This review does not yet
certify the final packed payloads or final assembly. Those payloads were
still being minimized when this review was written; only an earlier
untrimmed ordinary case 177 had then been reported Lean-checked.

Exact reviewed source/log hashes are preserved in
`rup-framework-independent-hashes.json`. Framework hashes:

- `CompactFramework.lean`:
  `1e63cb9679d9b1dc38b3a2dea7646a142219c06e7029ba1af55c1060174e95f1`.
- `WeakCompactFramework.lean`:
  `8305e2baa3d8c2f55930736fe662276301249dce306ab8f88140c5b2acf3ef51`.
- `PairedExactFramework.lean`:
  `3d7527bb8d4d7f158c741193428aeeedd67b2608dd0e6de87234ea8c963fa093`.

The ordinary and weak framework check logs contain only deprecation
warnings in stdout and empty stderr; their validation record reports
successful exports. The paired framework logs are empty, with export
exit 0 recorded. The archived printed-axiom audit for `paired_exact`,
`book_start_budget`, and `book_end` lists only `propext`,
`Classical.choice`, and `Quot.sound`. I did not rerun compilation.

## Literal and propagation semantics

A literal is `(variable : Nat, sign : Bool)` and means `v variable =
sign`. Its bit key is `2*variable + sign.toNat`; positive literals use
the odd key, negative literals the even key. `initial` records the
negations of all literals of the clause being proved.

`allowed a (some p) c` requires every literal of the reason clause to be
either the proposed propagated literal or already falsified by the
recorded assumptions. Its soundness theorem derives that `p` is true
from semantic satisfaction of the reason clause. Repeated occurrences
of `p` are harmless. With `none`, every literal must be falsified, and
the same theorem derives contradiction from a *known satisfied clause*.
The checker does not treat an arbitrary inconsistent set of assumptions
as an unsubstantiated conflict.

Every reference checked by `checkReasons` must be strictly less than the
current book length. Invalid references return false; arbitrary values
of the total `book` function beyond the proven prefix cannot be used.
An earlier fully falsified reason can end propagation immediately; this
is already a genuine conflict and safely makes later hints irrelevant.

`rows_sound` proves each learned clause by contradiction under its
negation, extends `ValidThrough` by exactly one row, and then recurses.
The new row cannot justify itself because reason indices are checked
against the previous prefix length. `book_end` runs with bitset zero,
so the final conflict has no extra assumptions. All SAT/LRAT calculations
outside Lean are discovery mechanisms; these semantic theorems and
kernel-evaluated Boolean checks are the proof boundary.

## Initial clauses and circuit interpretation

`localCheck` requires an enabled, semantically proved scheme and requires
every literal of its expansion to occur in the candidate clause after
mapping indices to facts. This direction permits only weakening by extra
literals; it does not silently strengthen a proved clause. Fact-array
out-of-range reads have one consistent default interpretation in both
`atLit` and `truth`, and the soundness proof uses that same interpretation.
Thus defaults cannot create a free axiom. `inputsOK` also checks exact
alignment of the scheme list and the initial clause list.

`construct_layout` applies to `Bplus = 11` and
`card(mask I) = k+3`. `construct_layout_budget` instead requires the exact
identity `Bplus + card(mask I) = 14+k`. They derive the residual-unit
enumeration and slot capacities from the DAG hypotheses; they do not
assume a satisfying Boolean assignment. The generated final exclusion
must call the constructor with the correct budget identity.

The ordinary `book_start` uses `Bzero = 0`, including the `exactAt`
scheme. The weak bridge rejects `exactAt` explicitly and consequently
needs no `Bzero` assumption. The paired-budget bridge wraps only weak
plain schemes and adds the disjunction of the two permitted exact-slot
families under `Bzero <= 1`. Its finite enabling condition matches the
geometric premises of `Layout.paired_exact`. The graph-theoretic paired
lemma is independently reviewed by `status_check`; here I checked its
connection through `enabledBudget`, `expandBudget`, `localSound_budget`,
`inputs_sound_budget`, and `book_start_budget` to the same RUP checker.

## Encoder, LRAT core, and original serializer

The reviewed encoder uses the exact new 19-edge graph and emits only
named scheme instances. Its old-graph switch is separate; final initial
clauses must still pass Lean's check against the new graph. Restricting
exposure sets to maximal independent sets omits constraints, which is
safe for an UNSAT argument. No synthesis symmetry restriction is added.

The extractor independently replays every LRAT addition through the
first empty clause. It accepts only positive, earlier RUP references,
requires an actual falsified reason clause, and rejects tautological
learned clauses. Ignoring deletion lines is safe because deleted clauses
remain proved consequences. The dependency closure is sorted in earlier
ID order; initial and learned IDs are remapped to consecutive zero-based
book indices. The empty final row is omitted from the book and becomes
the assumption-free `book_end` chain.

The original serializer packs literal keys little-endian in fixed-width
fields; clause length uses six bits and the unit-hint count uses nine.
It checks the corresponding length bounds, computes widths from the
fact/book sizes, and preserves positive/negative signs. Its ordinary
exclusion theorem uses `book_start` with `Bzero = 0`. Its `no_exact`
branch deliberately emits data/checks only and omits that exclusion.
It must not be mistaken for a checked weak or paired exclusion. The
author is supplying a separate final packed emitter using
`inputsOKBudget` and `book_start_budget`; that exact version remains to
be audited with the frozen payloads.

The reviewed Lean frameworks contain no new axiom, `sorry`,
`native_decide`, unsafe declaration, forbidden root marker, or string
literal. Options are resource limits only. A final result still requires
the final serialized data checks, complete case coverage, assembled
theorem, printed-axiom audit, and repository checker.
