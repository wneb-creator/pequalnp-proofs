# Root replay interval

The root kernel checked nodes0 through255 inclusive of the frozen packed checker at helper8 commit36375ce3bb56c227c81ecae98f6641800006b8c2. RootRange.checked quantifies over Fin5230 with the explicit hypothesis i.val<256. Eight32-node modules each use eight separate four-node kernel decisions. The aggregate and its dependency-axiom audit pass.

To rebuild, use the pinned project Lean/Mathlib installation and cache. Build results/swarm/SlimCount.lean from this branch as module SlimCount. Copy the19 helper8 checker modules listed in source-pins.json from the frozen commit, replacing its initial import of PEqualNP.Outside.L_meta_6581 by import SlimCount and all other PEqualNP.Outside.L_meta_6581 references by PEqualNP.Outside.L_meta_2373_aux.Count. Every resulting source hash must match source-pins.json. Build those modules in the listed order, then RangeAssembly, the eight RootNodes modules, RootRange, and RootAxioms with their directories on LEAN_PATH. RangeAssembly is copied from helper8 commit46151c240 and is included here.

The checked node modules used a9500MB Lean cap. Full stdout/stderr are included; compiled objects are deliberately omitted. Receipt timings are per-process wall time and wait4 peakRSS. The subsequent256..287 job was deliberately canceled after ownership moved to helper8; it is excluded from this packet and from every coverage claim.

This is a partial certificate interval, not the complete5230-node closure or the posted L-meta-2373 statement. No full-gap proof or counterexample is claimed.
