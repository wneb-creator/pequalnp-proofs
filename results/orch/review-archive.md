# Independent historical-archive review

Verdict: PASS for preservation only. ARCHIVE.md accurately labels the nine listed historical files as superseded source variants, unvalidated/unsubmitted draft, research notes, or solver diagnostics. None is an additional proof submission or evidence that the unrestricted posted theorem has been solved.

The five Lean wrappers/fragments contain the earlier pruning, sensitivity, and surgery declarations under the same auxiliary namespaces. Their stronger replacements are in the audited main. Historical wrappers that import the current main can now redeclare names already present; they should be treated as snapshots rather than independently buildable current targets. The main source remains the validation target. No new build or acceptance claim is attached to these historical bytes.

The reduction draft explicitly assumes two unproved universal hypotheses: singleton cleanup and subsequent pair cleanup while preserving singleton rejection. It is a conditional argument, not a proof of either hypothesis or the posted theorem. ARCHIVE.md correctly labels it unvalidated, unsubmitted, and outside the step-specific reduction permission. Preservation does not imply approval for a reduction PR.

The singleton strategy notes correctly summarize the checked positive-formula theorem and its leaf-count scope, and explicitly leave DAG sharing unresolved. The direct-bypass example computes xc OR ab, while its two replacements add ac or bc; it is explicitly nonminimal and does not refute the posted theorem. The remaining ownership route is described as incomplete. The Z3 capability log is only a tiny contradictory-equalities proof diagnostic, not a circuit certificate or repository checker result.

All selected files were checked for credentials and live lease identifiers; none occur. The five historical Lean helper files contain no sorry, new axiom, native_decide, unsafe implementation, forbidden root spelling, string literal, or nonsimp attribute. This source scan is not a substitute for compiling historical files.

| File | Bytes | SHA-256 |
|---|---:|---|
| results/orch/ARCHIVE.md | 1649 | ce97461df633f93623ec42d35d4e5736fd2280f2b9072f42ed5a614668ce3426 |
| results/orch/lemmas/global_prune.lean | 11925 | f07cabd3377ba91359ff2ba8e978504be6e0b2bceee4c637a669bb1ee2a801b4 |
| results/orch/lemmas/global_sensitive.lean | 4674 | b1fd1d617b3f867b523863d4ce85c23d5139a2d5320b3c34dab3a1f17386c7c4 |
| results/orch/lemmas/global_sensitive_fragment.lean | 4637 | 09ddf2205df280b76d646b6a0a7b2ccf9274ad0d13b05b8b3700efe5e6644900 |
| results/orch/lemmas/global_sensitive_min.lean | 5444 | be5ad99210e18c794ce85959f25750923c88555139db2b6d50f4322d2e4a1259 |
| results/orch/lemmas/global_surgery_corollaries.lean | 16089 | 94dc3f777eaa63c3c2e315dada304c7513aaf93b422973b7dd77c04c595e6182 |
| results/orch/lemmas/reduction.lean | 4525 | 06ff44b496ade3e2ac39820d22eda6d1ac8993ee84b8537174584cdab1a139e3 |
| results/orch/lemmas/singleton_strategy.md | 2390 | b2f2744f6096202d2d145ba47c883a7bbcaab46d41b51e0113ed35b5a84e7fd0 |
| results/orch/lemmas/z3-proof-capability.stdout | 309 | 10b792ea723a3d11deac6d48e362a88a1bbf61144b58f2d4416be6a89764eced |
| results/orch/lemmas/z3-proof-capability.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |

Reviewer: status_review. No proof or archival source was edited.
