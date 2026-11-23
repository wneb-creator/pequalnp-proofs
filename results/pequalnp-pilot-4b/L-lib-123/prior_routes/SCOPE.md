# Checked partial results for L-lib-123

These lemmas do not establish the posted FP3 existence claim. The central uniform short-trace or checkpoint-polynomial compression premise remains unproved. No unconditional alternating-time speedup is claimed.

Every included Lean source compiled successfully with the pinned project toolchain. The paired log preserves complete compiler stdout and stderr without truncation; empty logs are successful silent compilations. No posted-statement checker acceptance is claimed.

| File | Proven scope |
| --- | --- |
| ExponentBudget.lean | Uniform exponent slack and absorption of machine-dependent polynomial factors; assumes an exponent strictly below one. |
| CubeExpansion.lean | A Boolean-cube edge-boundary lower bound; does not prove a circuit or alternating-time lower bound. |
| StackPointer.lean | Correctness of a retained stack-cell pointer under explicit height and no-overwrite assumptions; not a complete machine simulation. |
| StackSummary.lean | Finite-state transition summaries for reversed stack consumption, including paired equal-length streams. |
| BatchVerification.lean | Semantic universal-table batching of point queries. Finite encodings and runtime bounds are separate obligations. |
| AdaptiveUnionBound.lean | A seed rejecting all adaptive certificates exists when the explicit finite union bound holds. |
| FingerprintCancellation.lean | An invalid push/pop trace has identically cancelling endpoint hash errors. This refutes that endpoint-only protocol, not FP3. |
| QuotientChallenge.lean | A nonzero non-root yields a bounded-degree rejecting minimal polynomial with constant coefficient one; also proves invertibility of X from the quotient relation. |

The sources are self-contained apart from their explicit Mathlib and, where present, PEqualNP.Defs imports. Supporting lemmas copied from existing proof files are already inlined. No failed probes, solver artifacts, credentials, or network data are included.
