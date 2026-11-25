# Final job record

Message: msg-76e9e7cc2ecd8e7693ec45e9

No complete posted theorem or refutation was obtained. No PR was opened. All checked partial results, search sources, complete diagnostics, and interrupted-build status records were preserved on pnp/pilot-107 in the fork.

The three own leases for L-meta-2592, L-meta-2583, and L-meta-2590 ended with HTTP410 before their last displayed expiry. Each failure was repeated once with curl -si, reported, and preserved. Work stopped on each dead lease before recovery. No other pilot’s lease was released.

## Checked partial results

| Gap | Preserved result | Verification | Final file lines |
| --- | --- | --- | --- |
| L-meta-2592 | For fan-in-at-most-two AND/OR/NOT circuits computing Petersen, 17 + NOT count ≤ size; hence a size-at-most-19 candidate containing NOT has one or two NOTs | Complete self-contained lake env lean compilation passed; axiom audit uses only propext, Classical.choice, Quot.sound | 5240 |
| L-meta-2583 | Exact equivalence of the posted READ1 normalization with the unrestricted sharp lower bound; the READ1 bound and standard construction are checked | Named lake build passed; full local checker rejected the missing final target theorem | 3374 |
| L-meta-2590 | Monotone circuit normalization and separate AND-count compression, with further conditional counting lemmas | Canonical source and the named checked components compiled; full target checker not run | 260 |

These are partial results, not submissions. Interrupted large certificate builds have no claimed local success. The search approximations are not counterexamples. This branch is an archival checkpoint with results folders and three partial named files, not a valid single-file PR diff.

The cleanup pass was not applicable because no full theorem passed the checker. Before/after cleanup line counts are respectively 5240/5240, 3374/3374, and 260/260.

## Final desk status

There were three null responses: two checker-backlog responses and one rejection of a specific already-proved component request for L-meta-2239. The public feed had still marked that step as open, but the desk said exactly:

> That step is not open: it is checked already, withdrawn, or not a step. Do not send its proof.

The next general request returned another pilot’s existing L-meta-4970 lease. The single required retry returned the same existing lease and exact note:

> you hold 5 gaps, the most one handle may hold at once; release one to get another

The explicit instruction to stop after the failed existing-lease retry applies. No live own lease remains to release, and no work was performed on L-meta-4970. Complete null messages and redacted final responses are in polling/desk-log.txt and polling/final-held-*.json.

Sub-agents: 6 reused agents (existing_results, counterexample_search, lower_bound, one_not, semantics, status_1035), covering independent proof strategies, finite searches, semantics, and red-team review.

Record UTC: 2026-11-25T15:43:44.367296+00:00
TIMING total=103.8 subagents=6
