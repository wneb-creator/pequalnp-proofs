Binary17 checkpoint review

UTC: 2026-11-25T14:25:00.308389+00:00
Verdict: PASS for reviewed mathematics, source-copy integrity, and file-format scan. Full-file compilation and checker remain PENDING; this review does not claim either passed.

Reviewed file: results/orch/lemmas/Binary17.lean
SHA256: 824549cea61a489c8821209214cf8d631ef13ac9741611f3c21caf9135c72bcd
Size: 293768 bytes; 4762 lines; below 512 KiB.
Base source: lean/PEqualNP/Outside/L_meta_6581.lean
Base SHA256: 23e7c375d8a73916110cf50ac5a91e715795ad57e5c665a35362ad935351e144

Scope and independence

The reviewer did not author the new suffix_floor, binary_floor_seventeen, or circuit/count wrappers. The reviewer originally generated the Geometry data and snippet; another agent independently compiled that snippet. This review independently checks its use by the new composition proof and validates that the copied base was preserved. Full-file compilation is still pending at this timestamp.

Copied-base integrity

The entire copied prefix through atLeastSixteen is byte-for-byte identical at the text level after replacing namespace PEqualNP.Outside.L_meta_6581 by PEqualNP.Outside.L_meta_2592.Binary17, ignoring trailing blank lines. No original hypothesis, certificate, or proof was altered. The old final exported theorem was removed; the new helpers are inserted before the renamed namespace closes. No stale old namespace occurs. Complete no-index diff is retained at /tmp/oec/pequalnp-pilot-103/review-binary17.diff.

New mathematics

1. suffix_floor allows the ten original inputs and one supplied signed binary gate on distinct vertices. The witness pair changes the target but keeps the supplied binary value and every other pin fixed, so live_row_difference forces the chosen original pin to remain in the live bank.
2. The vertex-false projection preserves the nine-variable target certificate, maps every permitted root to an available pin, constant, or complemented pin, and makes the forced original pin constant. projected_bound therefore charges at least one constant in addition to nineFloor's fifteen gates, giving sixteen gates for the suffix. The exact finite projection and witness data were validated in Python, and the Geometry snippet was separately Lean-compiled by another agent.
3. binary_floor_seventeen unfolds the first forward signed binary gate from Extended.Live. Its operands belong to the initial pin bank; distinct signal operands imply distinct vertices. The suffix roots satisfy suffix_floor's enlarged bank condition. Thus its sixteen-gate floor plus the peeled gate gives seventeen. The zero-gate case is excluded because the target is not an initial pin.
4. Extended.realize bounds signed binary steps by the number of non-NOT gates of a FanInTwo circuit computing the exact Extended.f10 target. The wrapper identifies notCount with countP Extended.isNot and uses the exact NOT/non-NOT partition of gates. Hence 17 + notCount C <= C.size is valid, and size <=19 implies notCount <=2. It does not assume NOT gates are essential.

No gap-closing claim

This is a partial lower bound. It leaves one-NOT and two-NOT circuits within the nineteen-gate budget; it does not state or prove the posted L-meta-2592 theorem. It must remain a preservation checkpoint rather than a final proof PR until that target is proved and checked.

Format scan

Only import is PEqualNP.Defs, at the start. No sorry, axiom, native_decide, _root_, double quotes, initialize, or unsafe tokens were found. There are no attributes. All 117 set_option lines use an allowed limit and the scoped numeric ... in form. File is plain UTF-8, regular, non-executable, and not a symlink. No credential material was observed in the reviewed content.
