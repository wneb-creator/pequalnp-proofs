# Symmetry preservation handoff

Stopped immediately on the parent's instruction after the lease-expiration response. No repository files were edited by this agent, and nothing was staged, committed or pushed. No owned compiler remains active. The interrupted generator18 child (PID46174) was explicitly terminated after stopping its runner.

The authoritative preservation index is `Symmetry982FinalPreservation.json`. Each compiled module has its complete combined stdout/stderr in `NAME.compile.log` and its status/timing in `NAME.compile.json`. Prior all-group paired-layout evidence is indexed in `CompactSymmetryManifest.json` and `Symmetry982Manifest.json`.

## Recommended APIs

Namespace: `PEqualNP.Outside.L_meta_982_aux.Finite.Symmetry`.

- `Grouped.fast bits width coordinates word`: derives coordinate contributions, radix-groups them by displacement and merges equal-displacement masks. `Grouped.fast_eq` proves equality to `Full.fast` for every Nat word when the coordinate-list length equals width. Bits above width are preserved. The correctness theorem needs no sorting-width assumption; insufficient bits only reduce grouping efficiency.
- `Grouped.Check k bits forbidden coordinates`: checks length2k, coordinate surjectivity via radix-sort equality with range2k, half preservation and forbidden-pool transport. `Grouped.check_good` produces `Full.Good k forbidden coordinates`.
- `Grouped.checked_actions`: applies the generator checks and cheap recipe/reference bounds to the existing `Checkpoint.group`/`actions` decoder. Its group identity width is2k. It needs no inverse-coordinate data.
- `Grouped.word bits k groupCount permutations g`: returns the input word immediately when g%groupCount=0; otherwise uses Grouped.fast on the chosen full coordinate list.
- `Grouped.word_run` and `Grouped.orient_run`: arbitrary-word RNatRun preservation from Full.Good. `Grouped.orient bits k groupCount permutations payload ws` preserves the existing payload convention: payload0 means identity, otherwise action `(payload-1)%64`.
- `Grouped.word_hom` in `GroupedSymmetryHom.lean`: conjunction of f0=0, XOR-with-Live.mask preservation, AND preservation and OR preservation. This is intended for proof_strategy's paired replay relation; RNatRun transport remains `Grouped.word_run`.
- `Coordinates.full k rowBits indexBits rows vertexPermutation`: builds each half's occurrence-rank map by radix-sorting `(row,index)` and `(vertexAction(row),index)`, zipping source/destination occurrences, and sorting by destination index. Concatenates independent low/high-half maps. Current data supports rowBits7 and indexBits13.
- `Coordinates.rows width inputs`: sequential row extraction by folding input columns right-to-left, with recursive injector `(word%2 + 2*row) :: inject(word/2) rows`. It avoids repeated large powers. This definition itself has no independent semantic bridge theorem; root owns that bridge. Numeric Grouped.Check still verifies every constructed generator before transport.

The new occurrence-rank maps differ from the saved full-coordinate arrays on duplicate-row positions. An independent Python comparison found that source row codes agree at every destination for all14 C7 actions and all48 core26 actions, so they have the same effect on encoded truth-table words. Do not claim literal equality of the coordinate lists.

## Verified concrete scope

- `GroupedSymmetry26Full4` and `GroupedSymmetry26Full18`: both complete core26 generator checks passed on the saved full2472-coordinate maps, each in14.98s.
- `CoordinateSymmetry26Gen4`: complete core26 generator4 check derived entirely from the seven input words and vertex permutation, passed in30.44s. It uses Coordinates.rows/full, then Grouped.Check; no literal coordinate list is in its theorem statement.
- `CoordinateSymmetry26Gen18`: interrupted on the stop instruction. Its log may be partial; it has no PASS and must be rerun only if work is authorized to resume.
- `GroupedSymmetryHom`: passed in4.34s. `CoordinateSymmetry`: passed in4.03s. `GroupedSymmetry`: passed in5.08s.
- Earlier `RadixSymmetry26Pool` passed the complete generator4 pool check in61.39s; the older array-based checker timed out at90s. These are diagnostic comparisons, not the recommended implementation.

`LinearSymmetryData26.lean` contains literal coordinate lists solely as benchmark inputs. Do not copy those lists into the final size-constrained proof. The derived-coordinate check uses only its k and forbidden/input words.

## Dependency chain and source reduction

Scratch cache imports currently form:

`CoordinateSymmetry` / `GroupedSymmetryHom` → `GroupedSymmetry` → `RadixSymmetry` → `LinearSymmetry` → `MaskSymmetry` → `FullSymmetry` → `CompactSymmetryReplay` → `CompactSymmetry` + `CompactSymmetryDecoder` → `ConcreteSymmetrySupport` → `Fast982`.

These imports are for scratch caching. Final source must be flattened into the permitted Mathlib/Defs-only file. Import-free copies are `GroupedSymmetryAppend.lean.txt`, `GroupedSymmetryHomAppend.lean.txt`, and `CoordinateSymmetryAppend.lean.txt`; earlier modules also have append copies.

There is removable historical code in that chain. The necessary generic foundation is permWord/bit lemmas and run_map, getD_map_lt, range_getD, array_all, generic Checkpoint group/actions preservation, Full.Good plus full-coordinate algebra, Linear.getD_mem/zip_mem, Masked.tail_bit, and radix membership lemmas. The current Grouped.check_good delegates through Radix.check_good and Masked.fast_eq; replacing it with the already-checked direct argument used by Radix.check_good would allow removal of most historical Masked/Linear checker code. That source cleanup was NOT attempted after the stop instruction.

Independent audits exist for Full, Masked, Linear, Radix, Grouped and compact replay. Coordinates and word_hom were compiled but had not received a separate independent source audit at the stop.
