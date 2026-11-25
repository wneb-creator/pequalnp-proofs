# Dynamic rectangle generation research

These scripts propose exact integer signed rectangle weights for tight monotone formula banks. Floating LP solutions are never used as pruning certificates: each accepted matrix is converted to integer weights, all rectangle costs are recomputed by finite integer subset enumeration, and an independent agent audits sample labels, coefficients, costs and duplicate multiplicities before publication.

The source matrices are mathematical data; the eventual Lean checker must still verify the finite cost obligations and the complete search certificate. No whole-case or original-gap proof is claimed by this directory.

The published loader snapshots are append-only versions. Their independent audits are under results/orch/rectangle-cut-audits and the dynamic-loader review reports. The second diagnostic snapshot contains216 banks, all covered by the original13 plus publishedv4. A third276-bank snapshot has five further independently audited symmetry variants for its21 residuals; these variants remain unpublished.

The strong mono19 first-OR-edge computational search completed with found=0 using ONLY loaderV1–V3, IDs1001–1026. V4 arrived after completion and is optional data for future cases. The completion is not a Lean proof; exact predecessor traces and search soundness still require kernel replay.

The V2 generation log contains54 proposed matrices; most were superseded by symmetry and remain unaudited/unpublished. Only records in the published loader snapshots are approved for computational search.

The benchmarks directory contains a compiled computation-only vector-sum alternative on the same20 profiles as the existing packed checker. It gave no significant performance improvement and is not part of the search or proof dependencies; no generic soundness theorem for that alternative is claimed.
