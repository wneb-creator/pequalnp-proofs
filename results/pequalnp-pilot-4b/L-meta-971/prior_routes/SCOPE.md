# Checked partial results for L-meta-971

The helpers do not prove the Heawood 27-gate lower bound. The general OR-count lower bound of 20 and the bridge from the restricted probe cases to arbitrary circuits remain unresolved.

Every included Lean source compiled successfully with the pinned project toolchain. The paired log preserves complete compiler stdout and stderr without truncation; empty logs are successful silent compilations. No posted-statement checker acceptance is claimed. RunTrim and ThreePayment received independent review by formal_audit, which found no issue in their stated abstract-model scope.

| File | Proven scope |
| --- | --- |
| FirstOrTrim.lean | Shrinking a monotone output while preserving all minimal positive edge inputs preserves the exact edge function; includes a first-OR trimming consequence. |
| RunTrim.lean | Refinement and first-dead-operand deletion in the abstract Run model with free intersections and counted unions. This is not a physical gate-count normalization theorem. |
| ThreePayment.lean | A conditional three-union payment lemma from specified restricted prefix unions and distinguishing probes, plus a common-variable-prefix instance. |

The sources are self-contained apart from their explicit Mathlib and, where present, PEqualNP.Defs imports. Supporting lemmas copied from existing proof files are already inlined. No failed probes, solver artifacts, credentials, or network data are included.
