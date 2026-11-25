# Independent review: frozen packed certificate set

Verdict: PASS for all 25 selected, individually Lean-checked certificate
modules at the frozen snapshot below. Complete case coverage, the
assembled final theorem, its size/format check, and the repository
checker are separate obligations handled by the other reviewers.

Snapshot manifest:
`search/compact-packed/SNAPSHOT_MANIFEST.json`, SHA-256
`12af7ad3021bedbb6afce8367219d96fba9255b89f0b81349c1fb1029adfd131`.
All 57 entries (28 Lean sources, 28 semantic JSON cores, and summary)
were rehashed and matched. Per-file exact hashes, independent results,
and selected check-log records are preserved in:

- `review-rup/packed-independent-validation.json`;
- `review-rup/final-selected-validation.json`;
- complete `review-rup/packed-audit-final.stdout` and `.stderr`.

I independently parsed the *actual emitted Lean text*, rather than
calling the author's encoder. The decoder matched every packed fact and
scheme to the semantic JSON. It decoded every clause, parsed and
evaluated the generated balanced book-lookup tree at every used index,
and decoded every row's unit reasons, final conflict reason, and
assumption-free last chain. Clause lengths, reason counts, bit widths,
signs, chunk offsets, and proof-prefix lengths all matched exactly.

The literal convention is positive = odd key and negative = even key.
Packed constructors use five tag bits and six bits per field. The exact
36-entry maximal-independent-set table matches the graph's table.
Vertex/edge modular decoding agrees with every original semantic value;
the independently reviewed decoder range checks also confirm that the
emitted values require no wraparound. Budget tag 21 is `pairedExact`;
other budget tags are plain weak schemes.

A separate dictionary-based unit-propagation implementation reconstructed
all initial scheme expansions from the exact 19-edge graph, checked
their finite enabling conditions and clause weakening, and replayed all
learned and final chains. Across all 28 archived modules it checked
6,379 initial clauses and 4,086 learned clauses. Every chain ended at an
actually falsified earlier clause, and every final conflict began with
no assumptions. This is additional independent validation; the proof
does not trust the Python or SAT result in place of Lean.

The final emitter's ordinary exclusions use `Bplus = 11`, `Bzero = 0`,
and `k = popcount(I)-3`. Budget exclusions use `Bplus = 10`,
`Bzero <= 1`, and `k = popcount(I)-4`, calling
`construct_layout_budget` and `book_start_budget`. The initial-clause
checker, fact interpretation, every `rows_sound` call, and final
`book_end` call use the same book and exact prefix lengths. Overlapping
masks have distinct `P...` and `W...` names and the appropriate budgets.

The 25 selected modules are:
`P1034`, `P1038`, `P11`, `P111`, `P1216`, `P1220`, `P1290`, `P164`,
`P177`, `P197`, `P2087`, `P2213`, `P266`, `P298`, `P400`, `P416`,
`P4293`, `P432`, `P47`, `P4757`, `P525`, `P645`, `W127`, `W4757`,
and `W1290`. Each has an exit-0 Lean check record whose source SHA-256
matches the reviewed bytes, and all 50 complete stdout/stderr logs are
empty. `P63`, `W16256`, and `W8488` also passed the independent data/RUP
audit but are explicitly superseded, uncompiled artifacts; they are not
included in this Lean-checked selection.

Reviewed packed decoder SHA-256:
`aa30d04d050bab40f52e50928599876d94042f1be3011754a785c34ec2bdf6a0`.
Reviewed final emitter SHA-256:
`f4a1df758b11802a73892f3ecd11794cd6e167c5f284eabb60041dad3b7f66ac`.
Its new per-row dependency trimming retains reason order, computes the
backward dependency closure from a real conflict, and independently
replays the trimmed chain before accepting it. The final output is
additionally protected by the same kernel-evaluated initial/row/conflict
checks audited in `REVIEW-rup-framework.md`.

No generated module contains `sorry`, a new axiom, `native_decide`, a
forbidden root marker, string literals, or attributes. All finite proof
checks use `decide +kernel`; the shared framework's printed-axiom audit
contains only the three permitted standard axioms. A final printed-axiom
audit of the assembled theorem remains appropriate after assembly.
