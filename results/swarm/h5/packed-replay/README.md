# Checked helper interval 3072–3839

All 768 nodes in this interval passed the Lean kernel under frozen checker commit `36375ce3bb56c227c81ecae98f6641800006b8c2`. The exported theorem is `PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5.checkedRange`: for every `i : Fin 5230`, if `3072 ≤ i.val` and `i.val < 3840`, then `Packed.checkNode i = true`. There are no unchecked interval hypotheses. The proof explicitly excludes wraparound in `Fin.ofNat`.

The twelve 64-node proofs use `decide +kernel` on four-node leaves and combine with the included `H5BlockSupport`. The aggregate and its audit passed. Both aggregate roots depend only on `propext`, `Classical.choice`, and `Quot.sound`; the audit found no foreign kernel exports, wrong module owners, or other axioms across 214 kernel declarations in fourteen proof modules.

`range-manifest.json` uses relative source paths. Every module has its exact checked source and complete stdout/stderr/result receipt. Empty logs are preserved. The manifest also records the hashes of locally observed oleans; binary artifacts are deliberately omitted. The separate source and completion reviews retain their historical scratch paths. `checker-dependencies.json` pins every local transitive checker source, plus L_meta_6581, to paths and hashes in the frozen Git commit.

To replay, use Lean 4.36.0 and the repository's cached Mathlib environment. Obtain the checker sources from their pinned Git paths, compile their imports in dependency order, and put their output directory in LEAN_PATH along with the repository and package build directories. Compile H5BlockSupport, then the twelve interval sources, then H5PackedRangeAll. The original audit source has a historical absolute JSON-output path; create its parent directory or change that output-only path when rerunning the audit elsewhere. The distributed source is exactly the audited original. Use one worker in an 8 GiB environment; the observed twelve-block compute sum was 1515.209263 seconds and peak RSS 4486248 KiB. Aggregate and audit builds took 2.921925 and 3.475793 seconds respectively.

`python3 verify.py --verify-only` checks this packet's hashes, interval coverage, successful receipt fields, and recorded audit rejection arrays without running Lean. It does not substitute for replaying the kernel.

This is a partial certificate receipt. It proves neither the whole 5230-node closure, the intended 18-non-NOT bound, nor the full posted gap. The separately assigned 3840–4607 interval is outside this packet. No PR or official full-gap acceptance is claimed.
