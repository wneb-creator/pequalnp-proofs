# Completed augmented-pair physical repairs008/009

Both runs use reviewed SearchPhysicalRepairPairs in sibling physical-macro-pairs/, with the complete254-test augmented Alternative6 basis, target28, width256,40rounds,120second cap, singleton rejection and minimum2diagnostic nontrivialdirty ANDs. The beam remains heuristic, and these restrictions do not express any proven necessity for arbitrary circuits.

Run008 seed14772949 inspected6,322,176neighbors in120.007955seconds and improved60→58augmented negative errors, corresponding48→46original maximal-negative errors. Run009 seed14772951 continued from that state, inspected5,013,504neighbors in120.033274seconds, and improved58→54augmented errors,46→43raw errors. Both saved circuits accept all24positive tests, reject every singleton input, and remain INVALID. Full logs and exact mistaken assignment lists are retained.

The separate included diagnostic independently scalar-replays both artifacts on all88original cases and checks physical topology, active-gate cones, augmented signatures, dirty counts and singleton rejection. No target28witness, UNSAT result or lower bound follows from these bounded runs.
