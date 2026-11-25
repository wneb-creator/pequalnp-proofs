# Fresh-proof checkpoint at lease loss

Root reported confirmed HTTP410 at2026-11-25T17:04:43Z and ordered all proof work stopped. This agent stopped immediately. There are no active build or search processes owned by this agent.

The latest completed sources below all compiled and exported with exit0. The listed checked logs are preserved under lemmas/. The two actual-case wrappers are author-checked; independent review was still pending at pause.

| Source | Status | SHA256 |
| --- | --- | --- |
| TwoFilterRailUsage.lean | Checked; proves raw0 is read outside the NOT and free10 is read before the NOT, under explicit actual two-sole-filter assumptions with one vertex in N(0). | d7fd13ad9d92c73a246a8bffdafc6696e90d1a2b0df975c397a9a1803f136e0d |
| TwoFilterOutsideNeighbors.lean | Checked; excludes an actual at-most18-gate two-direct-sole-filter circuit when one filtered vertex is outside N(0). | def007e250c782c90e03daa836590e19070c4ccd4b72aea25ac27a72dbdcffc5 |
| DirectFilterStructure.lean | Checked; packages root's actual-circuit factorization and independence bridge for an explicit sole-filter post-list decomposition. | 87167501ccac988e2e0c3e3ea14471c36467f24f3cee9b0c41dc723a301f8107 |
| NoPositiveRailCore.lean | Checked compatibility slice of root's checked NoPositiveRail namespace, with common bases supplied by imports. | c765ba6de87ed00e4178ec96157166a8b240871962cd5a7db47f759ec5dcf3e2 |

Logs: TwoFilterRailUsage-checked.stdout/.stderr, TwoFilterOutsideNeighbors-checked.stdout/.stderr, DirectFilterStructure-checked.stdout/.stderr, NoPositiveRailCore-checked.stdout/.stderr. The latter two pairs were copied from scratch during preservation only. The earlier lowercase two-filter-rail-usage logs belong to the prior source using a deprecated tactic and contain warnings; the capitalized checked logs correspond to the final hash above.

The final composition combining TwoFilterRailUsage with lean_setup's TwoFiltersRailCount was only planned. No new source for that composition was created. The proposed extension to all nonzero pairs and arbitrary filter operand orders was also not assembled. Existing CanonicalTwoFilter.impossible, AllTwoFiltersOrders, TwoFiltersRailCount, the completed auxiliary floor14, and the new rail-usage/outside-neighbor components retain their documented explicit premises.

There is no proof of the full L-meta-1884 statement and no counterexample. No named final-submission file was edited by this agent.
