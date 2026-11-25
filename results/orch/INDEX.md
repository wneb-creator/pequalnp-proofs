# Saved proof artifacts

Inventory as of 2026-11-25T15:34:10.932065+00:00. No full posted theorem has been proved. A checked partial may still depend on an unproved hypothesis; see validation.txt and the strategy notes for its scope.

The only named target file is [L_meta_2592.lean](../../lean/PEqualNP/Outside/L_meta_2592.lean). Its named lake build passed, but it contains helpers rather than the full target theorem.

## Useful starting points

- Petersen: [ReadOnePetersen2590](lemmas/ReadOnePetersen2590.lean) proves20 gates with explicit AO2 and joint read1 hypotheses. [CircuitBracket](lemmas/CircuitBracket.lean) supplies the one-NOT decomposition and critical witnesses.
- Projective planes: [PlaneStarExact2583](lemmas/PlaneStarExact2583.lean) supplies the exact-size read1 star construction. [NormalForm2583](lemmas/NormalForm2583.lean) and [CleanReaders2583](lemmas/CleanReaders2583.lean) record proved normalization components.
- Finite lower-bound work: [EliminationSound](lemmas/EliminationSound.lean), [EliminationBound](lemmas/EliminationBound.lean), and [ProbesTen](lemmas/ProbesTen.lean) have remaining finite-certificate hypotheses. They are not unconditional circuit lower bounds.

## Source inventory

| File | Recorded status | Lines | SHA256 prefix |
| --- | --- | ---: | --- |
| [BracketWitnesses.lean](lemmas/BracketWitnesses.lean) | Compiled partial | 97 | d63099b3262a |
| [CircuitBracket.lean](lemmas/CircuitBracket.lean) | Compiled partial | 429 | 514846d58cc0 |
| [CleanReaders2583.lean](lemmas/CleanReaders2583.lean) | Compiled partial | 640 | 112fff4818e4 |
| [CoverCheckEight.lean](lemmas/CoverCheckEight.lean) | Unverified or uncompiled snapshot | 701 | 40a6d8bc4f2c |
| [Elimination.lean](lemmas/Elimination.lean) | Unverified or uncompiled snapshot | 46 | e0695d3a5657 |
| [EliminationBound.lean](lemmas/EliminationBound.lean) | Compiled partial | 198 | bd8385aa5a11 |
| [EliminationCertified.lean](lemmas/EliminationCertified.lean) | Unverified or uncompiled snapshot | 216 | db41de916c08 |
| [EliminationChunked.lean](lemmas/EliminationChunked.lean) | Unverified or uncompiled snapshot | 485 | 02b0c83ccf5e |
| [EliminationRow.lean](lemmas/EliminationRow.lean) | Compiled partial | 59 | cf31ebfe7004 |
| [EliminationSound.lean](lemmas/EliminationSound.lean) | Compiled partial | 110 | 6b34a3d59df3 |
| [FanoCriticalRows.lean](lemmas/FanoCriticalRows.lean) | Compiled partial | 131 | b8beaa68ec15 |
| [FanoGeometryTest.lean](lemmas/FanoGeometryTest.lean) | Compiled partial | 15 | 6afbd73daec1 |
| [FanoReadOneBound.lean](lemmas/FanoReadOneBound.lean) | Compiled partial | 2014 | 61570a7a4558 |
| [IncidenceCriticalRows.lean](lemmas/IncidenceCriticalRows.lean) | Compiled partial | 97 | 8cc4f28ad582 |
| [LastNotCut.lean](lemmas/LastNotCut.lean) | Unverified or uncompiled snapshot | 87 | 2b990afc03e4 |
| [NormalForm2583.lean](lemmas/NormalForm2583.lean) | Compiled partial | 714 | 22b6e9980b0a |
| [NormalSingleton2583.lean](lemmas/NormalSingleton2583.lean) | Unverified or uncompiled snapshot | 1064 | 3f24d396004e |
| [Normalize2590.lean](lemmas/Normalize2590.lean) | Unverified or uncompiled snapshot | 260 | 9b9cf265e4b8 |
| [OneNotCut.lean](lemmas/OneNotCut.lean) | Compiled partial | 120 | 07a75abc4466 |
| [OrLift2583.lean](lemmas/OrLift2583.lean) | Compiled partial | 477 | 5d8f2c04974f |
| [OrLiftFixed2583.lean](lemmas/OrLiftFixed2583.lean) | Compiled partial | 585 | c6f9a8796832 |
| [PackedCircuit2583.lean](lemmas/PackedCircuit2583.lean) | Unverified or uncompiled snapshot | 217 | 2bdc88274464 |
| [PetersenBinaryFloor.lean](lemmas/PetersenBinaryFloor.lean) | Byte-identical copy of compiled named helper file | 3218 | 6c8e23234111 |
| [PetersenBracket.lean](lemmas/PetersenBracket.lean) | Compiled partial | 156 | 07f1033a93fb |
| [PetersenFormula2590.lean](lemmas/PetersenFormula2590.lean) | Unverified or uncompiled snapshot | 909 | b0431d957c39 |
| [PetersenReaders2590.lean](lemmas/PetersenReaders2590.lean) | Unverified or uncompiled snapshot | 85 | fb994b39b1ca |
| [PlaneStarExact2583.lean](lemmas/PlaneStarExact2583.lean) | Compiled partial | 664 | dd6e73b3f2a7 |
| [ProbesTen.lean](lemmas/ProbesTen.lean) | Compiled partial | 712 | 72c53a03fb42 |
| [ProfileFixtures.lean](lemmas/ProfileFixtures.lean) | Compiled partial | 47 | 115c27151a23 |
| [ProfilePruning.lean](lemmas/ProfilePruning.lean) | Compiled partial | 144 | f0c75432b495 |
| [ProfileRange.lean](lemmas/ProfileRange.lean) | Compiled partial | 97 | 328812614b99 |
| [ReadOnePetersen2590.lean](lemmas/ReadOnePetersen2590.lean) | Compiled partial | 1447 | 3da4d332bd36 |
| [RedundantNot.lean](lemmas/RedundantNot.lean) | Unverified or uncompiled snapshot | 562 | b7deed3aa944 |
| [SingerThreeReadOneBound.lean](lemmas/SingerThreeReadOneBound.lean) | Compiled partial | 2019 | 7913fd344ac0 |
| [Singleton2583.lean](lemmas/Singleton2583.lean) | Unverified or uncompiled snapshot | 673 | a8835671d1dd |
| [Singleton2590.lean](lemmas/Singleton2590.lean) | Unverified or uncompiled snapshot | 674 | ae1a21411954 |
| [StarConstruction2583.lean](lemmas/StarConstruction2583.lean) | Compiled partial | 1179 | 235ecb539b87 |
| [StrongNormal2583.lean](lemmas/StrongNormal2583.lean) | Unverified or uncompiled snapshot | 1073 | b485e408c2d7 |
| [StrongNormal2590.lean](lemmas/StrongNormal2590.lean) | Unverified or uncompiled snapshot | 1075 | 72254debc321 |
| [TerminalTen.lean](lemmas/TerminalTen.lean) | Unverified or uncompiled snapshot | 207 | d2f56f511d5b |

## Reproduction and logs

Run Lean4.36.0 with the pinned lean/lake-manifest.json and Mathlib cache; never run lake update. From lean/, a standalone partial was checked with lake env lean ../results/orch/lemmas/NAME.lean. ProbesTen intentionally uses the compiled named partial and needs integration changes before it can be a standalone submission. Full logs and exact hashes are listed in [validation.txt](validation.txt).

No full-statement tools/check-lean.mjs acceptance is claimed. No cleanup pass or proof PR has occurred. The source variants with shared declaration names are alternative snapshots, not files intended to be combined by importing them all.

Complete search archives contain controls and failed candidates, not counterexamples. See [CHECKPOINT-003.md](CHECKPOINT-003.md), [search2590](search2590/), and [sat2590](sat2590/). Desk diagnostics redact lease-control credentials.
