# L-meta-2962 counterexample investigation

No counterexample found yet. The Python finite search checks arbitrary dead AO2 networks on C4-free bipartite graphs and can be completed to a lift-fixed exact circuit by appending a canonical DNF output. It computes all truth-table values, singleton read-once supports, pair read-once supports, implicant status, core status, maximal cores, and both the target inequality and stronger |D|+tau(D)<=|U|+mc. The read-once recurrence is exact for fan-in-two circuits without constants: an OR unions supports; an AND can create a read-once pair only by joining disjoint singleton supports.

A tight example was found and kernel-checked in scratch Equality.lean (initial six lemma version exited 0; complete hypotheses version compiled successfully for its initial structural components). Graph edges {01,02,13}. Gates: e=3 AND 1; s=1 OR 2; t=0 OR e; core=t AND s; live=0 AND s; output=live OR e. The core and t are dead; other gates may be shared with the live output. It is AO2, computes the graph exactly, and is a lift fixed point. Maximal cores={3}; D has three edges; U={0,1,2,3}; minimum cover has size 2; deleting D leaves cover size0. Therefore the target is equality 3+2=4+1+0. Dead cores invalidate any hoped strict surplus.

General equality family: edges star a-B plus edge d-b with b in B. Compute e=d AND b; S=OR B; T=a OR e; core=T AND S. Core function=aS OR e, with reread at d-b. Cone cost |B|+2, accepted edges |B|+1, cover2, one core: equality. Sharing e between several such cores saves only one gate per additional core, offset by the mc term. Sharing S between distinct centers with |B|>=2 makes a forbidden 4-cycle.

Random search completed: 1,481,447 circuits over 50 sampled C4-free bipartite graphs with n=4..8, 240 seconds; no negative margin, smallest0. The stronger inequality also survived. Complete output in /tmp/oec/pequalnp-pilot-71/core-counterexample/search.log.

Guided search started on cycles10/12/14, Heawood14, and trees10/12/14, seeded from equality P4 gadgets. Full truth tables and exact read-once supports; gate mutation/insertion/deletion and shared-gadget additions; 15-minute budget, root renewing lease.
