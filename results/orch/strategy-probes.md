# ProbesTen checked adaptation

`results/orch/lemmas/ProbesTen.lean` is a scratch harness, not the PR file. It compiled with Lean 4.36.0, exit 0, against the already compiled partial module `PEqualNP.Outside.L_meta_2592`. Logs: `/tmp/oec/pequalnp-pilot-121/probes/build-002.stdout` and `.stderr` (both empty).

The harness first copies the CoverCheck8 definitions through Builds, then adds the Probes ledger adaptation inside `PEqualNP.Outside.L_meta_2592_aux`. Final merge must remove the scratch Outside import and duplicate CoverCheck prelude.

The regular rows are zero, the six core singleton inputs in order [6,7,3,4,5,1], and the independent core pair [6,7]. The baseline row8 is [4,6,7], an independent set that activates every terminal in [0,2,8,9]. Row9 is the edge [1,6], forcing the ledger add bit. Thus the actual vertex masks are [0,64,128,8,16,32,2,192,208,66], and terminal contributions [0,1,4,256,512]. Five explicitly checked graph automorphisms cover all five maximum independent sets.

The proof establishes initial_safe and aim_samples by kernel computation, then all generic Safe ledger transition lemmas, exact_occ, binary_caps, ledger_for_circuit, output_cover, and no_ledger. The last lemma takes the exact CoverCheck8 no_cover_build proposition as its last hypothesis, with budget 11. With bound nonNotCount <=15, three joins and a required add gate leave at most11 for pure computations plus filters, contradicted by that finite lemma.

This yields a stronger 16 non-NOT lower bound once TerminalTen and CoverCheckEight are merged. It alone excludes four NOT gates in a19-gate candidate; the remaining one-to-three NOT cases still require work.
