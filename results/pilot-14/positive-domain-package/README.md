# Three positive-cofactor oracle ablation

UNVERIFIED AS A LEAN PROOF. This experiment temporarily assumes a lower bound10 for each cofactor obtained by setting variable4,6,or7to1. The associated8-input bound was only established by separate native searches at the time of this experiment; no formal oracle is claimed here.

`python3 make_positive_domains.py` adds3 domains to the existing12. For each marker, exactly94 of the existing414 diagnostic pairs have that bit1 on both assignments. Their indices are repeated cyclically to252positions. The8remaining raw-input signatures are recomputed directly; the fixed marker maps to the all-ones constant. All selectors therefore use existing414rows, and ordinary Boolean operations and target labels are preserved. Prefix circuit accounting and canonical search remain the same as live_theta12.cpp.

Compile `g++ -O2 -std=c++17 live_positive15.cpp -o live_positive15`. Run `./live_positive15 40 3000000 15 0` with complete stdout/stderr redirected to files. The run completed natively with EXCLUDED998,821calls/106,553expanded in11.8052seconds, compared with the previously completed12-domain baseline1,159,421calls. This13.85%node reduction is modest; no substantial further proof investment was justified by this t0experiment alone. Other NOT budgets were not tested.

Complete build output is gzip-compressed because unsigned decimal literals trigger verbose compiler warnings; no compiler output was discarded. Limits are checked every65,536calls and may overshoot their nominal values. No Lean theorem or posted-gap conclusion follows from this package by itself.
