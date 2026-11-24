# Reverse-counter variant: ready for independent main review

Standalone source: `search_l1342_shard17_ancestorreverse.py`, SHA256
`b10d8832060d1c554fd3daa563b7159d515a3c55adc49718989eaa9bd0c2f24f`.
Parent: the independently reviewed constant-canonicalization source, SHA256
`b4ebb9509ecd7278f417ee2f0c4ebfc1c15288006942fcf90006e63d88ce8720`.

Only `totalizer_atleast` changes among function/class definitions. Each merge
retains its complete forward loop and appends the reviewed reverse loop.
The main block additionally sets `prefix_totalizer_reverse = True` in metadata.
All other definition ASTs and the remaining main block match the parent.

The projection argument and earlier exhaustive auxiliary controls are in
`totalizer-reverse-review.md` and its JSON. This audit tests the implemented
helper itself: its clauses, outputs and variable counts match the independent
merge implementation, including signed leaves and cap truncation. It passes
12,291 small input assignments, 85 repeated/complementary-literal assignments,
and 1,088 actual-size assignments. Exact thresholds satisfy all clauses and
are forced by unit propagation in every control.

A separately traced full base replay identifies all 10,325 inserted clauses.
Removing exactly those positions reproduces the parent base clause sequence.
The three prefix intermediates and all seven tail formulas preserve every
parent clause and every selector/auxiliary variable ID. Each adds 10,325
clauses and zero variables. Full metadata hashes, counts, parent links and
unchanged semantic fields are checked in `ancestorreverse-review.json`.

Fresh formulas are under `tail7-ancestorreverse/`. Reproduction from scratch:

    python3 search_l1342_shard17_ancestorreverse.py --distinct-prefix NEW_DIRECTORY

The separate one-junk variant is produced by `lean-setup/add_suffix_some_junk.py`
and reviewed in `suffix-some-junk-review.md`. It is not hidden in this generator.
No solver was started; no running case or repository file was changed.
Runtime improvement remains unmeasured. These are encoding controls, not a
search-exhaustion or Lean checker verdict.
