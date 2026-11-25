# Sparse full-star chart diagnostics

The independently reviewed full-star chart has 18 variables and 31 equations.
Its source JSON is the frozen `finite/star-full-generate-equations.json`, SHA256
`805790ef29f0a42c6a57f50e05ef991bd0c2bce219fcd951a4b0965cafcfa1af`.
The converter clears rational denominators and divides each row by its integer
content. Every actual row scaling is invertible both over QQ and modulo 1009.
The resulting sparse inputs have 2,450 terms. Independent reconstruction of
every input row passed; see the adjacent `sparse-engine/converter-review.log`.

Both runs used the official msolve neogb core through the separately reviewed
standalone wrapper: degree reverse lexicographic order, exact sparse linear
algebra option 2, all critical pairs per degree, one thread, a 120-second wall
limit, 4 GiB address-space limit, and disabled core dumps. The QQ run used the
isolated three-assignment bookkeeping correction documented in
`sparse-engine/qqfix.patch`; the finite-field run used the pristine core.

| Field | Outcome | Wall seconds | Peak child RSS, KiB |
| --- | --- | ---: | ---: |
| QQ | UNKNOWN_TIME_LIMIT | 120.053 | 1,765,656 |
| F1009 | UNKNOWN_TIME_LIMIT | 120.027 | 773,672 |

Both runs completed the same first four rounds and stopped during a degree-6
reduction with a 46,990-row, 120,229-column matrix. Neither produced a basis or
a mathematical verdict. The finite-field initial rounds were faster, but the
large reduction still exceeded the cap. A finite-field unit result would in
any event require a separate characteristic-zero argument; no such result
was obtained here. These are computational diagnostics, not Lean proofs.

The separate `sparse-star/` archive preserves exact inputs, provenance,
complete stdout/stderr, wrapper results, converter, and roundtrip checker.
The existing 82-file `finite/` archive is unchanged. The native engine,
wrapper, fixes, and independent six-control tests are preserved by the
engine owner in the adjacent `sparse-engine/` archive.

The archive also contains an independent exact check of a conditional
off-diagonal minor stratification. With path coordinates fixed, vanishing
all eight star/triangle minors is equivalent to four linear equations and
four products, giving two strata. This calculation does not establish that
the star/triangle charts vanish for a permanent-constant candidate, and does
not exclude either stratum by itself.
