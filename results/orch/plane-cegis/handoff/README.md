# Candidate integration handoff

Reviewed generator integrate_candidate2056.py SHAa03b9aec532961ddef699931c85f3989b3a37609830968f6baf6831439c8d79f accepts one standard decoded JSON circuit (gates, optionaloutput/size/n). It requires strict integer backward two-input AND/OR gates, verifies all52 positive and704 independently regenerated maximal-false rows, and refuses proof mode above63 gates. It pins the original PackedChunks template hash and exact desk statement text. Only after those checks does it render the literal Circuit, preserve all32 separate512-bit kernel negative certificates, and append the exact posted top-level theorem using exact_statement_of_checks. No external model or SAT result is trusted by the final Lean file.

For an actual validated<=63 candidate, from the repository root:

    python results/orch/plane-cegis/handoff/integrate_candidate2056.py --input /tmp/oec/pequalnp-pilot-121/CANDIDATE.json --output /workspace/pequalnp-proofs/lean/PEqualNP/Outside/L_meta_2056.lean --statement /tmp/oec/pequalnp-pilot-121/statement-2056.txt

The script writes a report only in scratch, so no extra file is created beside the named Lean file. Before invoking it, retain the decoded input JSON and native/source/model audit artifacts. Afterward, independently inspect the literal gates and exact final statement. Renew the held lease before each long build/checker through the parent owner.

Build the named module with the pinned executable from workdir /workspace/pequalnp-proofs/lean, saving complete stdout/stderr:

    LEAN_NUM_THREADS=3 /tmp/oec/pequalnp-pilot-121/toolchain/lean-4.36.0-linux/bin/lake build PEqualNP.Outside.L_meta_2056

Then from the repository root run the existing checker, again saving complete output:

    node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_2056.lean /tmp/oec/pequalnp-pilot-121/statement-2056.txt check

A successful generation is only a candidate. The named lake build, exact-statement checker and final independent diff review are still required before reporting a proof. Keep32chunk certificates; do not collapse them into one8192-bit decision. The successful original verifier benchmark was37.998seconds/3.04GiB with3Lean threads.

CONTROL TEST ONLY: the script was run on the actual decoded64-gate/13AND native control with --control64 into scratch/PackedHandoffControl2056.lean. That mode requires exactly64 gates, refuses the named path and appends no posted<=63 theorem. The rendered module has728lines and SHA31c5d93ce67c7b3acebe8e2293271277c4778cbc209c378511e698341d699e0c. All32negative certificates and52positive certificate compiled exit0 on2026-11-25 at19:04:51UTC,62.325seconds,3,167,736KiB at1thread. It is preserved under results/orch/lemmas. This tests literal replacement on a different canonical circuit from the original template; it is not a63-gate witness. The first launch started no Lean process because lake was absent from this shell PATH; the explicit pinned executable was then capability-checked and used successfully. The named Lean file was never changed during this control test.
