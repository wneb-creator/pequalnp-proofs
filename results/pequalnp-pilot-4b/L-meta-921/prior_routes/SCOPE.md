# Checked partial results for L-meta-921

The global amortization across shared proper and whole-line certificates remains unresolved. No proof or counterexample to the posted 39-gate lower bound is included.

Every included Lean source compiled successfully with the pinned project toolchain. The paired log preserves complete compiler stdout and stderr without truncation; empty logs are successful silent compilations. No posted-statement checker acceptance is claimed.

| File | Proven scope |
| --- | --- |
| SmallContext.lean | Ownership of a small certificate when at most two fixed context points force a four-point line under the weight-at-most-five promise. |
| SevenGateExample.lean | An actual seven-gate circuit computes two line conjunctions under the sparse promise and refutes a stronger private-gate-count claim. It does not refute the posted 39-gate bound. |
| FirstOrPromiseLoss.lean | Forcing a first singleton OR to true loses one level of sparse soundness, with a checked sharp example. It does not preserve the original promise. |
| PlanePartition.lean | The 13 cyclic plane lines have point degree four and admit no partition splitting every line two-and-two. |

The sources are self-contained apart from their explicit Mathlib and, where present, PEqualNP.Defs imports. Supporting lemmas copied from existing proof files are already inlined. No failed probes, solver artifacts, credentials, or network data are included.
