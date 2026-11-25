# L-meta-1904 research archive

No complete proof or refutation of L-meta-1904 was obtained. The three existing reductions were already at the live cap. This archive preserves the checked partial results, accepted reference sources with provenance, finite experiments, and complete successful validation logs.

Checked with the required `PEqualNP.Defs` import:

- `RankedMinimum.lean`: select an equivalent minimum-size Monotone2 circuit, then minimize any natural rank.
- `UnsafeBypass.lean`: a finite example showing that either naive operand bypass can change the computed graph function. This refutes the proposed local proof strategy, not the posted statement.
- `DiamondRewrite.lean`: a local OR/OR/AND to OR/AND/OR rewrite, with explicit unread-middle-wire conditions, preserves size and evaluation.
- `DiamondRank.lean`: for primary inputs with b distinct from c, this rewrite preserves Monotone2 and decreases the total singleton-active-AND rank exactly one.
- `DiamondRankMinimal.lean`: every Monotone2 circuit has an equivalent minimum-size circuit avoiding this exposed primary-input diamond. No theorem proves that every dirty circuit exposes one.

The copied accepted L/R sources under clean-and-proof are research references, not locally recompiled results. The SAT and stochastic searches under clean-and-search and clean-and-counter are computational evidence only; numerical UNSAT is not a Lean certificate, and UNKNOWN is not a lower bound. These searches found no counterexample. Folder documentation records the exact scopes and limitations.

`1904-BACKUP-MANIFEST.json` records exact hashes and byte lengths for all frozen text artifacts in the four folders, plus this README. `1904-BACKUP-FILES.txt` is the explicit named-file list, including the manifest and list themselves. No binary build outputs, credentials, lease responses, or unrelated repository files are included.
