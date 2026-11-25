# Independent RawOccurrence review

Reviewer: lower_bound. Date: 2026-11-25. Verdict: PASS.

Source: `/tmp/oec/pequalnp-pilot-70/formalization/raw-occurrence/RawOccurrence.lean`, 80 lines, SHA256 `4bd8cf3baa635ec75176034a0c0c48359762aacc2821a7a2dbceea50940ae4c3`.
Author-reported Lean exit 0; complete `raw-occurrence-check-2.log` inspected. It contains one unused-simp-argument warning and no error. The independent forbidden-format scan returned status 1 with no matches. No second Lean build was run for this review.

The proof correctly bounds multiplicity counts over a finite set by the reference-list length. Raw indices below n and the m-1 designated internal indices from n onward are disjoint; the explicit live-reference hypothesis contributes at least m-1 occurrences to the latter range, while fanin at most two bounds all references by 2m. Natural subtraction at m=0 causes no problem. The resulting raw count is at most m+1.

The unique-input corollary explicitly requires every raw input to occur and m+1<2n. If no count equals one, positivity makes every count at least two, contradicting the bound. Its 14-input, size-at-most-26 specialization is correct. Appending a repeated-output OR preserves raw counts under the explicit output>=n condition; that lemma does not claim semantic normalization by itself.

The component does not silently assume or prove that essential inputs occur, that a circuit is live, that its output is last, or that arbitrary invalid references have been normalized. Those remain separate prerequisites. It does not establish the full Heawood lower bound.
