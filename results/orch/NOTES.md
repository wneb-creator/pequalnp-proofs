# L-meta-1896 orchestration notes

Only the root agent requests and renews leases. The initial lease is no longer live.
Exact statement: results/orch/statement.txt
Public gap fields: results/orch/GAP.json

Target statement: 51 OR gates necessary for monotone fan-in-two circuits accepting order-3 plane incident pairs and rejecting generic maximal false inputs. Three reductions already live; do not assume another reduction is available.

Each strategy uses a separately named notes file in results/orch and scratch files in results/orch/lemmas. Root merges the final single file.

## Current live task: L-meta-2448

Exact statement: results/orch/statement_2448.txt. Public gap: results/orch/GAP_2448.json. Root holds and renews this lease only. Previous L-meta-1896 work is stopped. New goal: least monotone circuit for a triangle-free/C4-free graph having HasStarProfile. Three reductions live, two open PRs.
