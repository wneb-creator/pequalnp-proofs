# Signed17 formula-leaf rectangle applicability

This is exact integer research evidence, not a new Lean theorem or a completed signed17 exclusion. The input is the joint root-reachable bank export (edge and nonedge, including imported original-edge dependencies): 4,360 distinct banks, 1,966 formula0 and 2,394 formula1, over1,275 exact1024-bit truth functions. Its original SHA256 is pinned in all-signed-summary.json.

All62 available matrices were tested (13 original plus49 audited dynamic/symmetry records). For every raw signal v, the signed candidate cap is max(rectangleCost(v), rectangleCost(not v)). All4,360 banks fail to obtain a strict margin under every matrix. Positive-only costs would produce many apparent margins but are inapplicable to free-signed computation. Formula1 parent sums are diagnostics only: the extra sharing event requires checking every corresponding copied basis, so even a parent margin alone would not certify that case.

The exact original run contains158,242 cached profiles including390 implementation sanity samples. The portable independent replay reports the actual trace-profile count separately. It uses1,860 direct small-subset comparisons against a simple Python integer implementation, then reproduces every one of the4,360 full62-matrix margin vectors byte-for-data. Floating division is used only to rank the closest unsuccessful margin in the summary; all costs, strict-margin decisions and preserved vectors are integer.

The main implementation enumerates subsets of the smaller support, tracks signed opposite-side sums by Gray-code updates, and chooses all positive opposite-side sums. This permits negative coefficients and empty rectangles. All matrix dimensions are at most21, and the audited coefficient range is well within signed64-bit sums. The source and compiler output are preserved; no native code is proposed as a Lean proof.

## Reproduction

Copy this directory to writable scratch, then compile rectangle_dynamic.cpp with:

g++ -O3 -std=c++17 -shared -fPIC rectangle_dynamic.cpp -o rectangle_dynamic.so

After successful compilation, run python3 replay.py. Only bundled leaf-banks.json, matrices.json, and expected all-signed-bank-margins.json are required. No network or original scratch paths are needed. replay-summary.json and replay-full.txt preserve a successful fresh-directory replay. The historical measure_all_signed.py retains its original environment paths; replay.py is the self-contained reproduction entry point.

Scope: the existing weighted rectangle shortcut cannot discharge these actual signed terminal banks. This does not rule out other signed matrices, other lower-bound methods, or the separate finite signed formula-closure checker. The latter needs its own concrete data and kernel replay; library_route is measuring that cost separately.
