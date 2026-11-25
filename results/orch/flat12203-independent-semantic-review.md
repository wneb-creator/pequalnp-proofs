# Independent flat PR12203 semantic audit

Verdict: PASS for preservation of the source transformation. This is not a completed Lean/checker result or a final acceptable PR file.

I inspected `estimate_flat12203.py` and `generate_flat12203.py` against the actual original `forestRecord`, `forestHints`, `readSortedHints`, `promoteHints`, `readNode`, `fastState`, and `contextOf` definitions. I also reran the complete roundtrip audit successfully: 18 forests,67 packing entries,4,021 decoded node records, and15,599 ordered hints. No Lean build was started.

The raw-wire count is the population count of the lower nine mask bits, exactly matching selected inputs. Dense record prefix/live dictionaries and row offsets match the source. Unary Rice lengths use log2(head XOR(head+1)), including the all-ones32-bit case. Priority hint selection preserves the first/second/remaining order, duplicate selector behavior, and out-of-range selectors; the two-item subtraction uses truncated natural subtraction. Flat encoding preserves opcode/live words, the five-bit hint count, all column and paid fields, and per-node offset widths. Its branch is already implemented in the unchanged Lean decoder with marker0.

All consumers of packing records use the same forestRecord/forestHints path, including the optimized fastState and contextOf helpers. Every retained bound rule still undergoes buildRule validation, and linked states still undergo the existing soundness checks. Source comparison independently confirmed that only the reported packing tuples and data declarations change; all theorem bodies and every other declaration are byte-identical.

Original SHA-256: `5bc7f362c1cf08ca49a34dea07ed4ff386f2b393efb6261efa57a20c37f10348`.
Flat original-name source SHA-256: `9cb7708908b59feedbdfabe22663b6ecd9cd4483608cf1ba5a64b987df2527a9`.

The flat original-name file is548,472 bytes, above512KiB, and retains four custom structures. It therefore needs separate size/type conversion and review before it meets automatic plain-file requirements. This audit does not cover a later minified or type-converted candidate merely because it derives from this file. Full Lean replay/checker acceptance remains required after those transformations.

Reviewer: /root/status_review.
