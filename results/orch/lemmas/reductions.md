# Reduction and checked-component map for L-meta-2592

- Three live reductions are already in main: `R_meta_2592_271`, `_318`, `_408`. A fourth reduction exceeds the stated cap.
- `_271`: binary floor `15 + notCount C ≤ C.size`, followed by exclusion for 1 through 4 NOT gates.
- `_318`: split at the last NOT, arbitrary FanInTwo prefix plus monotone suffix, with combined binary budget 18.
- `_408`: normalize invalid reads and unused NOT operands, trim to last output; then exclude legal normalized circuits. Normalization may remove all NOTs, but then strictly decreases size.
- `L_meta_4725` is a checked, self-contained 3224-line proof of the binary floor from `_271`. It imports only Mathlib.Tactic, Mathlib.Combinatorics.SimpleGraph.Basic, PEqualNP.Defs. It handles ≥5 NOTs immediately. To reuse under the allowed-import constraint its helpers must be included inline and namespaces renamed.
- `R_meta_4727_1` splits the remaining 1..4 NOTs by existence of a NOT. Its no-NOT child `L_meta_8021` is vacuous and contributes no remaining difficulty. Do not mistake it for a useful Petersen lower bound.
- `L_meta_5236` (4560 lines, 285226 bytes) excludes 3..4 NOTs for an 18-gate remainder with supplied `x0 || x2`. Its actual proof ignores ReadsBack and output-range hypotheses, and proves at least 16 non-NOT gates for such a remainder. Signed truth-table certificate counts binary gates with complementation free; all code self-contained under PEqualNP.Defs.
- `L_meta_5238` excludes ≥5 NOTs for the same supplied-input circuit, by the 15-binary-gate floor.
- Remaining `R_meta_4727_17` and `_53` compile circuits to signed finite function/wire representations; their corresponding signed lower bounds are still unproved in this checkout.

These checked results support a real partial proof (large NOT counts / selected first-gate cases), but do not by themselves establish L-meta-2592.

## Prepared partial strengthening

`/tmp/oec/pequalnp-pilot-95/reductions/Sixteen.lean` reuses the signed certificate from L_meta_5236. Its new `Extended.realizeOrdinary` executes the original circuit on the ten input pins, instead of the eleven-wire bank containing a supplied OR. All extracted live roots remain a subset of the larger bank, so the original `atLeastSixteen` lemma applies. The resulting bound is `16 + notCount C ≤ C.size`, excluding four or more NOT gates at budget nineteen. This strengthens the earlier fifteen-binary-gate bound. Compilation is pending the root Defs build.

Exact normalization bridge R_meta_2592_408.normalize already appears as checked L_meta_7389 (305 lines). Repackaged helper-only scratch file is Normalization.lean.

Compilation completed 2026-11-25T13:59:53.440308+00:00: `Sixteen.lean` exit0, noerrors, stderr empty; stdout contains ordinary linter warnings. Independent status_review audit passed. Root handles preservation/push and target-module build.

## Terminal negations

`TerminalNot.lean` compiled and independently reviewed: an output gate that is the sole NOT cannot compute any function satisfying f(bottom)=false and f(top)=true, irrespective of gate budget.

`TerminalTwo.lean` compiled: if P,Q contain only AND/OR and `Bool.not (Q.eval (P.wires x ++ [!P.eval x])) = f x` with those endpoints, then P itself computes f. The proof compares the monotone suffix on bottom/x/top inputs, conditioning only on the prefix output bit. A concrete circuit decomposition using exactly two NOT gates is being tested in `TerminalStructural.lean`. Together with a monotone Petersen lower bound of18, this would exclude every≤19 circuit ending in NOT and containing at most twoNOTs.
