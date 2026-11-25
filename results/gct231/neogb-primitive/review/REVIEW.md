# Primitive-row exact QQ adapter review

Reviewer: global_normal_form, 2026-11-25 UTC. Verdict: PASS for the isolated
normalization delta, control traces, and exported exact certificates. No
full-chart run or heavy solver was started by this reviewer.

The complete source delta from the compact adapter is preserved in
`source-diff.txt`. The new helper computes a positive gcd over every retained
coefficient and all not-yet-processed dense entries. It divides exactly those
logical row coefficients and emits the rational scale 1/gcd. The call occurs
after every eight actual pivot eliminations, with future range [i+1,ncols).

The retained sparse coefficients have already been moved out of earlier
nonpivot dense columns and are therefore essential to the gcd. Earlier pivot
columns, including the just-eliminated column, are absent from the logical
row even when the engine leaves stale physical values there. Future pivots
cannot read or alter those earlier logical columns. The selected partition
therefore scales the entire logical polynomial exactly once. Zero coefficients
and negative signs are handled by GMP's nonnegative gcd; content zero or one
causes no division. Early exit upon gcd one is sound. A null retained pointer
is never read when its count is zero, and all GMP temporaries are cleared.

An isolated harness contains the exact frozen C helper body. It passed 7,488
combinations of retained-count and future-range boundaries, signed/zero
coefficients, and gcd values, under AddressSanitizer and UndefinedBehaviorSanitizer.
It checked every post-operation coefficient, unchanged consumed entries,
and the explicit trace scale. Build and execution both exited zero without
diagnostics. Complete output is `harness-build.log` and `harness-run.log`.

The independent direct polynomial-state verifier was extended with the
compact M operation: it requires a previously published output and shifts
its exact polynomial by the stated nonnegative monomial. It does not use the
author's vector representation. All toy traces and all 43 rowzero output
identities pass. Rowzero records 11 initial seeds, 141 monomial references,
209 scales, and 566 additions. Its final constant is one.

The separate certificate-DAG verifier also passes every toy certificate and
all 51 rowzero steps. Source roots remain the exact original 11 equations and
98 terms after sparse conversion/renaming. The complete sequence of 43
rowzero output polynomials equals the compact baseline; the variant records
29 additional scales. These checks establish the control identities without
trusting the engine's Groebner-basis claim.

The runner retains time, address-space, core-dump and per-file output caps,
and labels a file-size signal as UNKNOWN_OUTPUT_FILE_SIZE_LIMIT. A successful
process still requires exact replay before its output is used mathematically.
The variant is serial, characteristic zero, and isolated from active prior
engines. No existing engine or named Lean source was changed by this review.

Frozen hashes:

- cert_trace_primitive.c: 2ab5d0c46f1c9fee998122f58e959f38c72391d3f666af1bcfc279a7276c1676
- make_cert_trace_primitive.py: 6bee4ca3cf45891420ee77bc182d109e8753f2b456aa5ecdb9bef99b9c77f0d1
- run_neogb_trace_primitive.py: 4623b7e6c2cd506a2043a7afc5a0905816d5a6976f64ab468b420c7a097869ba
- generated la_qq.c: 9f9d0f95939606164ae8838a364fde08d28837b05a985d356863eec688483294

Reviewer sources and complete logs are preserved here. This review contains
no new geometric theorem or characteristic-zero full-chart conclusion.
