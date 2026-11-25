# Ordered-CNF delta packaging and passed streamed controls

The reviewed ordering cut is appended to the original global50 CNF using17,672 fresh variables2385579–2403250 and62,760 clauses. All original signature variable IDs remain unchanged. The1.44MB raw delta is compressed here; the original213MB base input remains archived once in batch0512. The resulting stream has2403250variables and9769618clauses, with SHA256d6f839f5b3c6b3592ebadf6bfc296cd6c3dc2dc9abab8692e0a78c67083cfc0b.

An independent review streamed and counted every base/delta clause, checked every old/new variable ID, retained mapping data, all three composed hashes, and the runner's reader cleanup. Its complete report is preserved. The runner verifies the composed stream before feeding it through an owned reader process group and refuses SAT/UNSAT interpretation if that reader fails.

Both sealed runtime controls pass: C4 returns SAT and reconstructs its two-OR witness; C5 returns UNSAT. Both readers exit0. Complete logs, manifests and control bases are included. These validate packaging and do not settle the posted global statement.

Runner v10 has one independently reviewed change from v9: the permitted positive address-space ceiling is4GiB instead of3GiB. Default remains3GiB and all shared-memory guards are unchanged. Parent authorization selects the actual cap. No ordered full solver query has started at this batch's creation.
