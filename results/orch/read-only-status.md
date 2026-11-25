# L-meta-2448 public-status check after lease loss

Read-only review at 2026-11-25T08:39:37.632554+00:00. No desk calls, lease actions, git mutations, external messages, or credential access were performed by this reviewer.

No accepted proof or withdrawal was found. The public evidence does not establish the cause of the reported HTTP 410.

## Public feed

The [current public head](https://data.pequalnp.com/head.json) was generated at 2026-11-25T08:36:42.919Z. Its referenced [meta-complexity map](https://data.pequalnp.com/data/map/program/meta_complexity.a4cf0b3945f7.json) still has L-meta-2448 in status `j`, with record hash `64b0fc4c2f44`. The complete node record is identical to the snapshot read at job start; its record timestamp is 2026-11-24T08:32:49Z. Thus this source shows no intervening accepted/refuted/retired transition. The latest two public feed pages, covering events from 07:31:55 through 08:34:00 UTC, contain no event for this gap.

## Upstream GitHub

The original brilliant-hq repository endpoint redirects to open-goat/pequalnp-proofs. A fully paginated structured GitHub search for this gap returned all 11 matching PRs, with `incomplete_results: false`: one open PR and ten closed PRs. The upstream commits API for `lean/PEqualNP/Outside/L_meta_2448.lean` returned an empty list. No full-proof merge was found; the older merged item in the search is a reduction.

The newly opened [PR 13028](https://github.com/open-goat/pequalnp-proofs/pull/13028) was created at 08:34:34 UTC by wneb-creator, with its body identifying pilot 74. It is open and unmerged at head `82089343e5c56f395b4cf4859f5765597b0da866`. The [authoritative intake comment](https://github.com/open-goat/pequalnp-proofs/pull/13028#issuecomment-7157234631), posted at 08:35:51 UTC, says: **REFUSED before any build: the file holds no theorem**. It links [checker run 45577537228](https://github.com/open-goat/pequalnp-proofs/actions/runs/45577537228). This is not proof acceptance.

The earlier [PR 12779](https://github.com/open-goat/pequalnp-proofs/pull/12779) was closed without merging at 07:23:12 UTC. The merged [PR 10684](https://github.com/open-goat/pequalnp-proofs/pull/10684) is explicitly a reduction and predates this job.

## Limit of this finding

The lease failure is not explained by an observed accepted proof, refutation, or withdrawal. The review cannot infer server-side lease state from public records. The other pilot's PR and any leases it holds were only read and were not modified.
