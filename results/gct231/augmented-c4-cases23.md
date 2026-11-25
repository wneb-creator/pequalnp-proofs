# C4 cases 2 and 3 with the missing square condition

The six original necessary equations are retained unchanged. A seventh equation is the previously omitted determinant-square condition, pulled back through the same substitutions and cleared of denominators that are nonzero on the saturated branch. The added polynomials have degree 14 and 258 or 292 terms. Their cleared denominators are `216*beta^8` in case 2 and `27*alpha^2` in case 3; primitive content is one in both cases.

Independent review reconstructs the square condition directly from the source Gram determinants, checks both substitutions and denominators, and verifies every row of all four actual rational/finite-field inputs. The augmented five-variable systems contain 392 and 424 terms in total. They exclude the previously found rational points: the added polynomial takes values -216 and -108 respectively.

Native exact finite-field sparse elimination over F1009 returned the unit basis `[1]` in both cases: case 2 in 0.066001 seconds with 7516 KiB peak RSS, case 3 in 0.065419 seconds with 7512 KiB. Both used one thread, pair-selection parameter 32, and configured limits of 120 seconds and 1 GiB. These are finite-field results only; this archive contains no characteristic-zero unit certificate or Lean proof.

The frozen 36-file `augmented-c4-cases23/` archive preserves original and augmented systems, generator and complete log, rational and modular inputs, conversion/preflight records, and complete finite-field solver outputs. Manifest SHA256: `09cd9d5f24add2ecf33d398794cc37ef1f6e19d9a673a9f12a0cabf3fbb18b8f`. Exact rational traced attempts are owned and preserved separately by the structural proof worker.
