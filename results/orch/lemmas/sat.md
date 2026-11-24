# SAT strategy

## Tools

- Installed libz3.so.4 (4.13.3) works through ctypes, without downloaded bindings.
- Lean distribution includes CaDiCaL at `/tmp/oec/pequalnp-pilot-42/lean-dist/lean-4.36.0-linux/bin/cadical`.
- Host has 5 CPUs. Per root request, only two solvers remain active.

## Complete encodings

`complete24.py` generates a complete circuit model: exactly 14 gates, two one-hot Fin28 source selectors per gate, future/out-of-range sources interpreted as zero, 24 selected original bit rows, no normalization assumptions. It has 1806 variables and 35836 clauses. Selecting a subset of rows suffices for refutation: every actual circuit witness must satisfy those rows.

Rows: `[21,4,23,5,10,11,28,25,7,8,19,20,46,13,32,14,15,17,38,37,42,53,55,57]`. For gate i, block size 129: operator offset 1; A selector offset 2+j; B selector 30+j; A value 58+r; B value 82+r; output 106+r.

`complete.py` is the analogous 58-row encoding (3234 variables, 71570 clauses). The 15-gate version satisfies all 77548 clauses under the known star witness. The 58-row solver was stopped to reduce CPU contention; logs and incomplete LRAT retained.

The optional `complete24-and4.cnf` adds 364 clauses forbidding any 11 OR gates, justified by the separately Lean-checked AND >= 4 result. This run was stopped for CPU availability.

## Free-AND route

`free_and.py` allows arbitrary conjunctions of available sources as each OR operand, plus a final conjunction. Sources 0..12 are initial inputs, 13 is false, and 14+k is OR output k. Ten OR gates produce 3538 variables and 15783 clauses. Empty conjunction is true. The normalizer agent has a Lean-checked bridge to this model.

`free_and_closed.py` adds canonical conjunction constraints: select every available source that is true on all target-positive rows where the operand is true. This preserves positive support exactly and can only remove negative rows. Induction through all OR gates therefore preserves an exact final target. The resulting encoding has 4738 variables and 18577 clauses and is the currently active free-AND run. Formalizing this stronger normalization remains outstanding.

## Completed searches

- Two QF_BV 14-gate searches, all 58 bits: both unknown after 120 seconds.
- Basic normalized 14-gate CNF: unknown after 300 seconds / 2.19 million conflicts.
- Exactly 4 AND gates: unknown after 120 seconds / 0.88 million conflicts.
- Exactly 5 AND gates: unknown after 180 seconds / 1.09 million conflicts.
- S4 symmetry, incomparability, target-error dominance, and sharing variants: no result before timeout or CPU-reduction stop.
- Free AND / 10 OR baseline: unknown after 300 seconds / 1.75 million conflicts. A longer retry was stopped in favor of canonical closure.

No SAT witness or UNSAT certificate as of 2026-11-24T22:05:50.561524+00:00.

All generator scripts, CNF files, full stdout/stderr logs, and incomplete LRAT traces are under `/tmp/oec/pequalnp-pilot-42/sat/`. Only a completed UNSAT trace would be a certificate.

## Final search status

At 2026-11-24T22:08:18.550810+00:00, root requested stopping the two remaining searches after the reduction checker accepted. Both were terminated without SAT or UNSAT. All source generators, metadata, complete stdout/stderr logs, and hashes are archived in `results/orch/sat-archive/`. Incomplete LRAT traces were excluded and are explicitly not certificates.
