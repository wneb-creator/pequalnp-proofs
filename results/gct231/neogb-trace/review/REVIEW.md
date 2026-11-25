# Independent neogb exact QQ certificate-adapter review

Reviewer: global_normal_form, 2026-11-25 UTC.

Verdict: PASS for the frozen serial characteristic-zero adapter and the
exported toy/rowzero ideal-membership certificates. No heavy solver was run.
This is not a full-chart result and is not a Lean compilation verdict.

## Two independent arithmetic checks

The separately written certificate-DAG verifier checks every original
generator, every shifted rational polynomial-parent identity, strict earlier
parent references, the nonzero final constant, and its exact ancestor closure.
All three toy certificates and every one of the 51 rowzero steps pass. Rowzero
has 11 roots and 40 derived identities, with 10,342 exact monomial
contributions. Its unit dependency contains 22 steps, 239 displayed polynomial
terms, and 168 parent terms.

A new direct trace verifier maintains actual sparse rational polynomial
states. It does not use the author's vector-of-inputs representation or
certificate extraction algorithm. Every seed is independently matched by
exact shifted/scaled equality to an already established polynomial. It then
replays every scaling and addition and checks every raw output. This passes
all toy traces and the rowzero trace: 11 source records, 152 seeds, 180
scalings, 566 additions, and 43 published outputs. The final constants are 1.

The original 11 equations with 98 terms match the sparse neogb input and the
renamed x0,x1,x2,x3 companion exactly, preserving coefficient denominators
and monomial exponents. Thus the source-root normalization does not change
the ideal or silently substitute a different problem.

Complete logs are `certificate-review.log` and `direct-replay.log`. The
reviewer implementations are `verify_certificate.py` and `direct_replay.py`.

## Source review

The overlay diff against the preserved qqfix/pristine engine sources is
recorded completely in `source-diff.txt`. It adds tracing calls, captures
the already computed divisibility predicate, and leaves the underlying
arithmetic operations unchanged. The adapter is restricted to one thread,
exact characteristic zero, and sparse linear-algebra option 2.

Input generators are logged before internal basis normalization. Normalized
initial rows and subsequent monomial multiples must pass exact seed matching
against an established polynomial. This accounts for leading coefficient
normalization and denominator clearing without treating them as new roots.

Dense-row reduction records the correct transformation: in the divisible
case, target minus mul2 times pivot; otherwise, mul1 times target minus mul2
times pivot. Content removal and sign normalization are recorded by the
ratio of the new and old nonzero leading coefficients. Sparse/dense row
pointer transfers preserve the trace-node identity. Missing row associations
or invalid scales abort. Pointer reuse and any missed engine operation are
not trusted for mathematical soundness: each published polynomial must still
pass the exact direct replay and certificate identity checks.

The runner preserves complete stdout/stderr, enforces address-space and time
bounds, and labels a nonzero exit or timeout without a mathematical verdict.
COMPLETED records process success; replay and Lean checking remain separate.

The existing reviewed Lean emitter reproduced `NeoTraceRowzero.lean` exactly:
9,528 bytes and 46 lines, SHA256
`d39e7504d7591248b27a37320f6ce9589021360e7582b17edc4b8c0d9a6cfce8`.
Its theorem assumes the explicit 11 complex polynomial equations and derives
False via kernel-checkable `linear_combination` steps and `norm_num`. It does
not assume or assert a full geometric chart classification. At review freeze,
this emitted Lean file has not yet compiled; only a later successful build
may upgrade that status.

No reviewed engine, adapter, source equation, or named Lean file was changed.

## Frozen source and certificate hashes

- cert_trace.c: 3e2d3e359c84849a3ad654832071d0b0924351740152963ce70568dc9ef8d77d
- make_cert_trace.py: d3595fc47de09a46fcf9770fbdc47e7186957e4a56ce3860f72c3386ef86a5f2
- run_neogb_trace.py: 671ac84e56c766f835127d533eb0bafe407c03a59a8028d337048a711a589a01
- f4_to_neogb.py: 1d9d19e42324a932b1611f99531a2f41e938a0d1f22a2d48704f42f99833491e
- neogb_cli_trace: ad11d46ffee62adcdf3579460bf10774cccc6ee94e6b4755fb47cd687cd120f7
- libneogb_trace.so: 241fe098e1a068c519cb2ee544d87edac7e91290bcaeefb04111ab6c77f3ebef
- rowzero.trace: 59d579e8e4bc61584147945f37b79ee966d51eb792c75e8456916f1de2555796
- rowzero.certificate.json: 4c337f6ae640d3283c6c85437c4e8dcf6af7bce54456aced51056c3f949ed2e7
