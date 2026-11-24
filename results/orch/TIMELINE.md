# L-meta-670 timeline

- 2026-11-24T15:14:49Z Job started.
- 2026-11-24T15:16:25Z Lease acquired, L-meta-670; reductions_open=true; zero desk nulls.
- 2026-11-24T15:17:30.297067+00:00 Six agents assigned: toolchain, structural proof, finite cases, reduction design, graph bounds, independent review.

- 2026-11-24T15:24:07.705434+00:00 direct_structural first checked result: terminal normalization and degenerate terminal-gate exclusions,181lines, Lean exit0.
- 2026-11-24T15:24:22.765227+00:00 First checked results: named partial vertex-cover bound and16gate witness; conditional3child reduction; terminal normalization. Preparing immediate preservation push after independent review.
- 2026-11-24T15:26:37.568461+00:00 Global exact-function monotone-normalization reduction rejected on quality review: effectively original bound once monotone optimum is known. Replanned toward bounded-NOT cases plus AND/OR counts, with high-NOT cases solved by essential-input count.
- 2026-11-24T15:27:53.634173+00:00 Checked all9 essential-input witnesses; independently reviewed; preserving immediately.
- 2026-11-24T15:28:28.386169+00:00 Generic essential-support bound checked and independently reviewed: n essential inputs require at least n-1 non-NOT gates.

- 2026-11-24T15:29:01.373956+00:00 direct_structural essential-input bound excludingNOT compiled; single-declaration local version also checked.

- 2026-11-24T15:29:37.615779+00:00 graph_bounds: OR-count proof route stalled; finite single-vertex deletion probe search stopped at100019 unresolvedfour-prefixstates (cap100000), no Lean proof.
- 2026-11-24T15:29:41.170958+00:00 Checked support-count proof with all helpers local to one theorem; checked NOT count assembly facts; independently reviewed and preserving.
- 2026-11-24T15:31:14.204208+00:00 Four-child reduction compiles (304lines); independent review passed. Placed named R_meta_670_32.lean for build and checker.
- 2026-11-24T15:33:02.019734+00:00 Checked12 graph automorphisms and shortened local-support proof independently reviewed; finite search logs preserved.
- 2026-11-24T15:35:09.206532+00:00 Initial local checker rejected compiler-generated auxiliary declarations (reduce-extra). Rewriting local pattern matches and avoiding lazy evaluator equation lemmas; mathematical children unchanged.
- 2026-11-24T15:36:16.426358+00:00 Corrected reduction builds (299lines), independently reviewed: avoid generated auxiliary declarations through if/decide and direct rfl evaluator steps. Second local checker running.
- 2026-11-24T15:38:02.293864+00:00 Local checker ACCEPTED(reduce):4children,1664constants,onlystandardaxioms. Started cappedcleanup, deletingunusedlocalproofs andsimparguments.
- 2026-11-24T15:42:11.579263+00:00 Final localcheckerACCEPTED(reduce),270lines; cleanup299→270 completeunder4min. Preparingone-filePR; supportingresearchwillremaininpreservedcommithistory.
