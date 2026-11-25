# Targeted PR census

Read at 2026-11-25T01:01:05.223085+00:00. Read-only gh API calls; no writes, comments or issues.

The historical upstream qualifier brilliant-hq/pequalnp-proofs returned422 in GitHub search. Existing PR metadata identifies its canonical name as open-goat/pequalnp-proofs; searches used that canonical name.

All searches used --paginate. Every page was checked as an object with total_count/items; incomplete_results=false; the total returned item count equaled total_count. Counts:2585=11;4895=4; read+cover=156(two pages); read-1+normalization=15;2583=7;2628=2;4896=1. Numeric PR-number collisions are included in those rawcounts and were excluded from gap conclusions.

No complete proof or closed unrestricted charge theorem was found among the inspected sources.

- PR9697 unchanged head9a7b2ba1647d0d43e87d2ff4017b977e6fd7e044. Conditional matching bound + star construction, with locallyproved read1 bridge.
- PR9707 unchanged headc19bca0988052aad6ddf9527332f310ae3770d8b. Conditional vertexcover charge + read1 construction.
- PR9659 head dc41ae82824be3ff75ea03c39d249f88f7d0b320 adds R_meta_4895_215.lean,126lines. Actually a three-child reduction: unrestricted matching-size charge, separated-side star builder, separated-side⇒read1. Its126line source was read in full. Bot comment says ACCEPTED checkerexit0; this verifies the conditional reduction, not its charge child.
- PR11141 head086d43d3a867537563a7b5e4f6c62af40d717257 adds R_meta_4215_521.lean,81lines. Actually a three-child Fano reduction: route dichotomy, mixed-OR exclusion, first-AND-collision exclusion. Its81line source was read in full; final proof only case-splits the supplied dichotomy. Body refers to2585 cover arguments but the file does not prove them. No comments or check runs at readtime.
- PR8618 head320008fedea4437b9cd42f01fcd0e7fe439db52c adds R_meta_2585_1.lean,13lines. Two-child lift-fixed normalization reduction. Source read in full. Closed, unmerged.
- PR11018 head38e6ab827fe9543379b65bf7dd77eae9a5349677 adds R_meta_2585_427.lean,50lines. Three-child star builder + least block normalization + block cover budget reduction, similar toour decomposition. Source read in full. Closed, unmerged.

Fresh explicit reduction eligibility evidence:

https://github.com/open-goat/pequalnp-proofs/pull/11110#issuecomment-7149020857

Closed: this step is not open to reductions (its row in the desk file does not say reductions: true), so this reduction will not be checked. A proof of the step is still welcome. This is an automatic message.

Comment created 2026-11-25T00:55:01Z on PR11110, a new2585 reduction. The full response is comments-11110.json.

RawAPI responses, stderr, source patches, and extracted complete additions are saved alongside this report. No Lean source from these PRs was compiled in this census.
