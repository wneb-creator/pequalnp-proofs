# Independent review: Projection63

UTC: 2026-11-25T17:42:38.965212+00:00

Verdict: semantic PASS at SHA-256 `0eb8d3da8cf8e662fd9533a93b94e738a7be6c8f4557238a8d1e705dc92123e4` (29 lines, 1,224 bytes). One harmless trailing space on line 14 was reported to the author for removal before final assembly.

The proof retains StrictLive, full exact graph computation, Bzero=0, and exact ineligible mask 63. Independent finite checks give P=mask16000=[7, 9, 10, 11, 12, 13], an independent six-vertex set, wide(P)=[1, 3, 4, 5], contained in mask63, and labels(P,wide(P))=[9, 10, 11, 13] of size four. Bzero=0 and ineligibility ensure every wide neighborhood occurs, so marks=wide. The general projected_count bound then has left side 8+4+4+8=24 and right side at most6+6+Bplus, proving Bplus>=12. No unknown case coverage or arbitrary-circuit claim is assumed.

Both archived full success streams are empty; author validation records check/export exit 0. No new compilation was run. The auxiliary import must be inlined for final submission.

Final formatting update: source SHA-256 `720a6d420ac8b725f59dab63ad08fe8c976a851029f8cd4e0c4796262f6f284f` is byte-identical to the reviewed and compiled source after removal of exactly one trailing ASCII space on line 14. This exact transformation was independently verified. Final source has 1,223 bytes; semantic PASS remains unchanged.
