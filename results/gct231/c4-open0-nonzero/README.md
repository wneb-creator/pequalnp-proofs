# Checked scalar certificate: C4 open case 0, nonzero extension parameter

**Lean PASS**, exit 0 in 39.152 seconds, peak sampled process-group RSS 4,380,152 KiB. `C4Case0Nonzero.lean` is 75,298 bytes / 61 lines, SHA256 `99a2284e7cb3e67f20d24bf7617d51416f37de56442edcfbd25e14ce770fbf46`. The exact-source audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Complete output includes harmless tactic-sequencing linter warnings.

The theorem proves a contradiction from explicit two-variable necessary resultant equations and the open-factor hypothesis beta^2+beta-1 != 0. Exact QQ replay derives (beta+gamma)^2=0 and (gamma^2-gamma-1)^2=0. The Lean proof uses no-zero-divisors to remove those squares and a checked polynomial identity to contradict the open factor. It omits the unused generator h2 and uses only roots 0,1,3.

Independent review PASS, copied unchanged in `review/`, verifies all 26 rational certificate entries, parses and checks all 18 actual Lean linear-combination identities, checks the source roots and final identities, and confirms the successful build and standard axioms. The original geometric/resultant review is in sibling `c4-open0-zero/`.

This is a scoped scalar helper for an open fixed-C4 branch, **not** the full C4 theorem or the posted gap. The scratch file has global heartbeat/recursion options; named proof-file integration must scope them with `in` above each theorem. A separately corrected combined/scoped source handles this layout and the case1 substitution wrappers. The old combined wrapper's unused-h2 error is explicitly recorded by the review and is not part of this checked source.

The two-variable consequence method replaces an oversized 580,542-byte saturated proof emission with this 75,298-byte proof. Exact engine inputs, full solver/replay/emission/build/audit logs, certificate, source, and review are preserved. No engine binaries are included.
