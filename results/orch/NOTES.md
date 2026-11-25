# pequalnp-pilot-60: L-meta-2602

Sole lease acquired 2026-11-25T02:52:22Z. Two null desk answers preceded assignment. Root owns desk and git operations.

Exact statement and assignment: /tmp/oec/pequalnp-pilot-60/assigned.json and statement.txt. Imports allowed: PEqualNP.Defs and Mathlib modules. All final helpers must use namespace PEqualNP.Outside.L_meta_2602 or _aux. Final target theorem full name top-level and last. No forbidden syntax, quotes, new axioms, sorry, native_decide or _root_.

Strategies write separate notes here and separate scratch Lean files under results/orch/lemmas; do not edit the final file. Append short findings to this file. Root will consolidate.

Toolchain: /tmp/oec/pequalnp-pilot-60/toolchain/lean-4.36.0-linux/bin. Cache setup ongoing with checker_review.

- Derivative route: candidate uniqueness and repeated-AND certificate written in `lemmas/Derivative.lean`; not yet checked pending shared definitions build. Both directional zero derivatives imply local repeated-read structures, but global 65-gate counting remains.

- Structural strategy: see structural.md. Three-active-AND shortcut is false via q=x AND y; t=q OR z; out=q AND t. Existing face≥56 and path obligations remain open; mixed dirty AND gates are the real obstacle.

- 2026-11-25T02:56:45.120860+00:00 lemma_search:2067 flat and2069 cleanAND copied into lemmas/Clean.lean; appended counterexample_shape (not yet compiled). Any target counterexample must have nestedAND and an uncleanAND gate. Face bound5985/path5987 remain open.

- Counterexample route: no index/derivative witness loophole. Small exact semantic search found matching xy OR zw has double-re-read in4 gates versus minimum3, via (xy OR z) AND (xy OR w). Thus no two-gate penalty. Plane star64 gives analogous double-re-read65. Details in counterexample.md.

- 2026-11-25T02:58:48.029919+00:00: Derivative.lean CHECKED, exit 0 under the allowed PEqualNP.Defs import. Includes derivative uniqueness, repeated-AND certificate, actual wire recurrence, and valid-output bound. Root notified immediately for partial push.

- 2026-11-25T02:59:37.255070+00:00: reduction_design: focused route is face≥56 plus double-zero restriction removes≥9 gates. Exact small search supports matching/P4 cases and disproves the analogous claim for C4, so C4-free hypothesis is essential. No fourth reduction slot. Details in reduction-design.md.

- 2026-11-25T02:59:42.487917+00:00 lemma_search: Clean.lean COMPILED exit0. counterexample_shape eliminates flat and all-cleanAND cases; remaining case must contain an uncleanAND gate. Root notified for early push.
