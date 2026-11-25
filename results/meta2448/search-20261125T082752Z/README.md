# Exhausted raw two-edit repair and restriction diagnostics

The broader L584 repair search applies both a direct deletion/alias/constant and a distinct-gate binary rewire to the original20gate program BEFORE cleanup. It exhausts all430 deletion cases and3,193,710 rewires in16.200seconds, with no witness. Every per-case count and the total were independently reconciled with the exact combinatorial enumeration. The previous normalized-before-rewire search also exhausted2,078,136 checks. Both process exits were observed as0; full logs and exact scope/counts are preserved. These are restricted neighborhoods, not global lower bounds.

A separate tiny diagnostic restricts L584 to all15adjacent-vertex deletions, then greedily simplifies by truth-preserving aliases. It performs5908 full256input alias checks. Two restrictions reach13gates, both with star profile; no nonstar13circuit was found by this procedure. Others finish at14or15. This is not an exhaustive search over all equal-cost circuits. The already accepted13gate minimum for this core and the correction to earlier12gate search plans are included explicitly.

No further local searches are planned. The live generic Petersen19 search is excluded and will be archived only after actual completion. No full proof or refutation of L-meta-2448 is claimed.
