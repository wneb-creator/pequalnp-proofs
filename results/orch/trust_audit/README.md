# Major partial theorem trust audit

The following exact source snapshots were copied to job scratch, given an appended `#print axioms` command, and compiled with the pinned Lean 4.36.0 toolchain through `lake env lean`:

- `Witness65.size65_double_read`: the complete 65-gate witness.
- `PlaneOrBound.plane_or_lower_bound`: the 13-input, 13-output lower bound of 39 OR gates.
- `CofactorProductive.cofactor_productive_lower_bound`: the 26-input bound of 39 productive OR charges counted with point multiplicity.

All three compilations exited 0. Each theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. The complete combined stdout/stderr logs are preserved, including warnings. The manifest pins source hashes, audit-copy hashes, exact theorem names, command arguments and log hashes. The audit copy is reproducible by appending a newline, `#print axioms <theorem>`, and another newline to the source bytes.

These are partial theorems. This audit neither proves L-meta-2602 nor runs the repository submission checker.
