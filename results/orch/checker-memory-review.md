Read-only review of the active L-meta-670 verifier. No Lean process or build was launched for this review, and the proof, checker, and caches were not changed.

At 2026-11-25T05:32:32.641082+00:00, verifier PID 12669 had 13,433,928 KiB (12.812 GiB) resident memory. The mapping breakdown was:

| Mapping category | Resident KiB | Resident GiB |
| --- | ---: | ---: |
| Mathlib-backed mappings | 5,035,356 | 4.802 |
| Lean/runtime-backed mappings | 1,475,296 | 1.407 |
| Project-backed mappings | 20,520 | 0.020 |
| Anonymous mappings | 6,901,836 | 6.582 |
| Other files | 920 | 0.001 |

Anonymous pages across all mapping categories totaled 6,905,096 KiB (6.585 GiB). At 2026-11-25T05:35:19.605458+00:00, with process elapsed time 07:20, resident memory had fallen to 12,054,760 KiB (11.496 GiB) while anonymous memory was 6,955,400 KiB (6.633 GiB). Swap was zero. This confirms that total RSS is not a fixed minimum: file-backed residency can change independently of the anonymous working set. These are snapshots, not measured peaks or a pre-replay baseline.

[CheckLemma.lean](../../lean/CheckLemma.lean), lines 351–417, creates a statement environment importing the entire pinned Mathlib plus PEqualNP.Defs, imports the proof module separately, and imports a definitions-base environment. The full Mathlib import is unconditional and does not depend on narrowing this proof's imports. Only about 20 MiB of the sampled resident mappings belonged to project files, so the proof's serialized file size is not the principal resident-file component.

The pinned Lean 4.36.0 source Lean/Replay.lean retains an environment and sets of remaining/pending names. It visits safe, nonpartial declarations in the supplied constant map and recursively orders their dependencies. Ordinary definitions and theorems are checked through separate addDeclCore calls; constructors and recursors are checked against generated declarations. It does not filter declarations by reachability from the final theorem. Declarations that are merely unused still get checked unless they are actually removed from the source. This code does not expose a persistent verifier-level cache of normalized certificate results. The snapshots do not distinguish imported environment metadata, live kernel reduction data, and allocator-retained pages within anonymous memory; attributing all anonymous memory to one of those would be unsupported.

Theorem bodies are already opaque for ordinary reduction. Making the computation definitions opaque would obstruct the certificate computations and would not exempt their declarations from kernel validation. Noncomputable definitions retain their kernel bodies and have already been applied to the primary; their demonstrated benefit is reduced compiler payload/build work, not omission of kernel checking.

The fastest credible fallback remains the independently prepared product/Subtype/Sigma version of PR 12203, whose monotone certificates use fewer states and additional checked pruning. This is a recommendation from its structure and prior measurements, not a verified full-build or verifier verdict for that fallback. It needs its own complete build and checker run.

Independent review of saved upstream logs found late verifier RSS samples of 12,933,492–13,282,664 KiB for PR 12184 (elapsed 3:36–4:38), versus 10,260,932–10,265,904 KiB for PR 12203 (elapsed 6:55–7:57). Both runs timed out before a final verifier verdict. These samples support investigating the smaller fallback, but are neither peak measurements nor a startup-memory baseline. No earlier resource samples were available in the saved logs.

The measured batching tradeoff on the same 96 primary certificate states was:

| Maximum states per batch | Process seconds | Kernel seconds | Peak KiB | Result |
| ---: | ---: | ---: | ---: | --- |
| 16 | 46.587 | 35.8 | 4,185,120 | PASS |
| 32 | 42.160 | 30.5 | 4,804,900 | PASS |
| 48 | 39.918 | 29.9 | 5,402,716 | PASS |
| 96 | 70.831 | incomplete | 6,657,016 | FAULT at the 6500 MiB Lean cap |

A cap of 32 saves about 584 MiB of observed peak versus 48, at about 5.6% more process time in this test. A cap of 48 was fastest measured. The fallback uses different certificates and sample width, so these numbers cannot guarantee its peak or hosted runtime. The supplied hosted targets of 20 minutes and roughly 6.5 GiB remain goals requiring measurement; neither the sampled RSS nor this microbenchmark establishes compliance. See [the batching summary](batch-width-summary.txt).

The primary source remained SHA256 42bee598c028c21d1eeebcb40ff8435ce53b4bf5256c806ce0304c5721d581b6 throughout this review. Its completed build took 1366.55 seconds and reported peak child RSS 6,183,016 KiB; the standard checker was still running when this report was written.
