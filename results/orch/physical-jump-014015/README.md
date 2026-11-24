# Completed focused repairs014/015

Both runs use reviewed fixed28-gate physical repair, the254-case Alternative6 augmented basis, singleton rejection and minimum2diagnostic nontrivialdirty ANDs. Run014 used Jump, width128, seed14772963,120seconds; it inspected5,826,560neighbors in120.004898seconds and saved41/34/33raw-error improvements, reducing the augmented count54→43. All candidates accept every positive edge and remain INVALID. The final33error candidate has all28gates active and three nontrivialdirty ANDs; one AND reads descendants of both other dirty gates.

The included exact symbolic-DNF diagnostic independently expands that final candidate and checks its result against all254cases. Its34minimal terms are the24target edge pairs plus10bad pairs:3-7,4-7,2-9,3-13,5-13,2-14,2-17,3-17,2-18,4-18. This is a description of an incorrect circuit, not a target witness.

Run015 used exhaustive one-gate Resynthesize, width16, seed14772964,120seconds from that33error state; it inspected6,572,032neighbors in120.026490seconds. Complete stdout/stderr and all recorded improvements, if any, are retained. Source is in sibling physical-composite-repair/. These bounded heuristic trials establish no lower bound or general UNSAT claim.
