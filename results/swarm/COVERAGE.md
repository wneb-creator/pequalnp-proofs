# L-meta-5012 coverage checkpoint

This is research status, not a submission or a proof of the full gap. The shared proof branch contains a checked partial file only.

For independent junk gates, raw factors are classified by their color supports:
- P: opposite pure colors (disjoint automatically).
- S: one pure factor and one mixed factor (may overlap).
- O: both factors pure in the same color (critical-edge use forces overlap).
- M: both factors mixed.

| Case | Status at this checkpoint |
| --- | --- |
| Any independent pair containing M | Complete restricted theorem published by helper5 at6d59af62; reviewed by peers and independently replayed by root. |
| P/P, all factor sizes | Complete wrapper reported by helper7; exact published outer wrapper still pending. |
| Disjoint S/S | Complete theorem published by helper6 at4a967a4a; independent peer review and root replay passed. |
| P/S with both pure-g factors large | Root center geometry, output guard and budget compiled; actual circuit compiler pending. |
| P/S with pure-g singleton | Root counting route assigned to helper6/helper7; not yet a case theorem. |
| Both overlaps large, same-color unique outside centers | Complete theorem published by helper3 at262724eb; canonical outer classification being assembled. |
| Both overlaps large, opposite-color centers | Complete distinct-filter theorem published by helper4 at0840db0; composition with the same-center case pending. |
| One overlapping product, or singleton intersections | Several conditional and diamond cases checked; general coverage incomplete. |
| Nested pair, later junk active on both color classes | Complete conditional theorem published helper1 at505960f0; stronger unconditional version reported locally. |
| Other nested pairs | General work split among helpers1/5/8 by earlier-junk color behavior. |

Independent reviewers explicitly distinguish the complete conditional cases from the exact posted statement. Resource bounds and no-unassigned-OR cases are additional checked support; they do not complete the remaining general cases.

Sub-agents: 9 external bus helpers and 2 local agents.
