# Upstream refresh 006

Read-only scan at 2026-11-25T07:31:13.855565+00:00. Baseline d4b3433bdf0f53b899c2806479d6f27a565d2e37; fetched upstream main b4b27af110a7b1d350d8a3e4c4c890d1381dec60. No worktree source, merge, branch, or desk change.

88 Lean paths changed. At this head, lean/PEqualNP/Outside/L_meta_650.lean is absent; no new650 commit was found. The fully paginated open-PR census contains713 objects; the only title/head-ref650 match is the existing R-meta-650-42, PR11223, last updated2026-11-25T02:08:39Z. This is a title/ref census, not a proof that no unrelatedly named PR mentions650. GitHub returned its canonical link https://github.com/open-goat/pequalnp-proofs/pull/11223. No accepted proof/refutation of650 was located.

Relevant new accepted statements:

- L_meta_7249: the cyclic projective-plane graph on26vertices, leastAO+TopForm, singleton junk, and explicit budget/coverage/residual≥2 premises implyFalse. The theorem lists size≤64, but its proof does not use that premise. The new closure classifies one-junk sides into thin/overlap cases. It does not handle multiple junk gates or higher penalty and is already subsumed for our purpose by the checked at-least-two-junk partial.
- L_meta_8748: arbitrary Monotone2 circuits have a semantic list of at most the original ANDcount sets, each the intersection of unions of previous sets, raw truth sets, anduniv; every original wire truth set is a union of such sets. This is representation machinery, not a lower bound or size-saving extraction. Our tighter checked conversion already preserves gate values when counts are tight.
- L_meta_8744: if every inclusion-minimal accepting point/line rectangle of a strictAO circuit is singleton onbothsides, it computes exactly the induced incidence relation. Its proof uses monotonicity and minimal accepting witnesses; it supplies no gate-count bound.
- L_meta_8379 andL_meta_8734 contain an explicit empty-gate-list hypothesis. Their projective-plane bounds therefore do not apply to a63gate candidate.
- L_meta_6111 is a concrete LRAT-unsatisfiability statement for a14input24gate encoding with an added unit clause; it is not a global650 theorem.
- L_meta_8445/8507/8511/8515 are small8input graph lower bounds. The remaining main additions are5input monotone truth-table results; the only reduction isR_meta_3231_1.

Conclusion: no newly accepted higher-penalty/equality closure or useful63gate circuit extraction was found. The current full target remains unresolved by this scan.

Reproduction: git fetch https://github.com/brilliant-hq/pequalnp-proofs.git main; compare the pinned commits withgit diff --name-only; obtain each source usinggit show HEAD:path with the pinned new hash. Complete extracted sourcecopies and everygit command stdout/stderr are in /tmp/oec/pequalnp-pilot-57/upstream-refresh-006. The openPR read used gh api --paginate and a structured JSON projection; all713 NDJSON records were shape-checked before filtering. Initial --slurp use was rejected by this installedgh version, then replaced by supported --jq streaming. No networkwrite occurred.

No Lean builds were performed for this scan; accepted-source statements were read, not locally rechecked.
