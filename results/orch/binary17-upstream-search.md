Petersen signed binary lower-bound source search

2026-11-25T14:27:58.303215+00:00

No generic 17-non-NOT-gate lower bound was found in the searched local upstream proofs or the relevant first-gate reduction ancestry. This is a scoped negative finding, not an exhaustive claim about all newly accepted files. The fresh desk feed is from 2026-11-25T14:23:10.467Z. GitHub main at review was ec6eec7fc86864d4be7fb500648865ce2f6b0695; it has 221 commits / 223 changed files after local base45b7dac0, and those new files were not all downloaded.

Exact reusable sources:

- L_meta_5236.lean:4456 Extended.realize compiles any FanInTwo circuit evaluating on ten inputs plus x0 OR x2 into a free-negation Live derivation, counting only binary/non-NOT gates. No ReadsBack, output-range, size, or NOT-count assumptions are used by this helper.
- L_meta_5236.lean:4478 Extended.first_needed uses two rows (96 and608 in its reordered input table) to prove the raw x0 wire remains live even with the extra OR(x0,x2) root.
- L_meta_5236.lean:4495 nineFloor gives the deleted-Petersen signed lower bound15.
- L_meta_5236.lean:4504 atLeastSixteen projects raw x0 tofalse, arranges the live front as first :: erase.toList, and charges its one constant to derive16binary operations for the suffix. This gives17including the already computed firstOR, but only for this first-OR branch. Its theorem at4543 then excludes suffixes with at least3NOTs and total size≤18.
- L_meta_6581.lean:4545 is already the direct generic16non-NOT lower bound for the full Petersen function: countP(fun g => !g.op.eval [false])≥16. Under FanInTwo its predicate is exactly non-NOT. Its source contains a nearly identical atLeastSixteen4505 and first_needed4479, but with only the ten raw roots. Our Binary16 partial independently rederives this existing bound.
- R_meta_1888_3.lean:5 separates firstOR(0,2) suffixes into monotone,1..2NOT,3..4NOT,and≥5NOT cases. L_meta_5236 discharges3..4 and L_meta_5238 discharges≥5. L_meta_5234 (1..2NOT) and L_meta_5232 (monotone) remain open in the fresh feed.

Both local L_meta_5236 and L_meta_6581 hashes match the fresh checked feed exactly. The first_needed finite witness and atLeastSixteen projection template are suitable to generalize to arbitrary first signed binary gates. They do not establish the parent gap alone.
