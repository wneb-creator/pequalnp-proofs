# Independent review: PrivateProjection finite witnesses

UTC: 2026-11-25T17:35:39.190320+00:00

Verdict: PASS for all 44 finite witnesses at source SHA-256 `44b9b39221be13e8502eeaf2b3393ee1b2201151c98159b58e4f8373e8b413f4` (637 lines, 40,391 bytes). Generic partial_exits/local_merge/private_bound proof review is recorded separately.

I parsed each theorem's actual Lean mask arguments and all 14 entries of its witness array, independently of the author's JSON. For every theorem I verified the exact ineligible mask in its hypothesis, independent P with cardinality at most 7, Q contained in P, projected degree-three/two membership for U/W, all J adjacency/private-witness conditions, and every A[f] independence/containment/adjacency premise. The computed natural-number left/right cardinality totals match the literal Lean claims and yield a surplus lower bound at least 12. All 44 actual source records also match the separate author data. Full independent replay records are in projection/private-projection-independent.json.

Each theorem explicitly assumes StrictLive, complete graph-function computation, Bzero=0, and equality of one particular mask with the actual ineligible set. No coverage of arbitrary masks or removal of the zero-surplus hypothesis is claimed. Some witnesses yield 13 while conservatively concluding 12. The older validated-exclusions.json scope says not yet Lean checked; it is a historical finite precheck, superseded for these 44 exact witnesses by the successful source validation record.

The two complete archived success streams are empty; the validation record reports Lean dependency compilation exit 0. No compilation was repeated for this review. Prohibited proof/string/attribute scans pass; all limits are locally scoped. The helper import requires inlining and a final standalone check before a one-file submission.
