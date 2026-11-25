# Structural NOT route

Existing upstream reductions of L-meta-2592:

- `R_meta_2592_271`: binary gate floor 15 and a separate bound for 1–4 NOT gates.
- `R_meta_2592_408`: normalize invalid reads and output, then a finite lower bound.
- `R_meta_2592_318`: split at the last NOT, then bound the resulting prefix/suffix separator.

The known `FewNot` helpers concern multi-output set families and do not directly prove this single-output Petersen lower bound. The monotone sibling L-meta-2590 itself has three reductions and no theorem file in current upstream.

Drafted `lemmas/LastNotCut.lean`, proving the first hypothesis of `R_meta_2592_318`. It separates the list at the last NOT, gives the prefix the NOT gate's first input as output (or an invalid wire when the list is empty), and takes the suffix as a monotone circuit. Exact gate accounting and evaluation factorization are preserved. Compilation awaits root's Lean toolchain setup.

The public gap audit subsequently identified this exact component as already checked in `L_meta_8295`. The draft is retained only as notes and should not be built or submitted as new work.

Structural obstacles and existing work:

- `L_meta_7227` already compiles arbitrary circuits into signed binary gates with a marked-wire budget bounded by the number of NOT gates.
- `L_meta_4725` gives 15 plus the number of NOT gates as a lower bound on the Petersen circuit size. Thus a putative 19-gate witness has 1–4 NOT gates.
- `L_meta_8039.binaryFloor` gives 14 non-NOT gates for Petersen with vertex 9 deleted. This does not directly raise the full binary floor to 16: a two-gate elimination chooses the killing input value, whereas the 14 lower bound applies only to fixing a Petersen variable to false.
- Fixing vertex 9 to true gives three positive literals (4, 6, 7) OR the edge function of the six-cycle 0–1–2–3–8–5–0. It has an 11-binary-gate circuit: three factored stars for the six-cycle cost 8, then OR the three literals. To contradict a 15-binary-gate full circuit, restriction would need to save at least 2 binary gates at false or 5 at true.
- Replacing the sole NOT by a constant is not generally valid even for scalar monotone outputs. With z = NOT x, the expression xz OR xa OR zab is a(x OR b), but replacing z by either constant changes it. This example does not disprove elimination in a size-minimal circuit.

New search route: the nine-vertex deletion has 12 edges and a 16-gate monotone construction. A 15-gate construction with one NOT would give a 19-gate full Petersen witness by appending four gates for x9 AND (x4 OR x6 OR x7), then OR with the deletion function. Parent approved a stochastic search for this nine-input target, complementary to the SAT agent.

Search status: the baseline stochastic run reached 10 wrong rows out of 512 with an unused NOT before root stopped it for resource control. The live-NOT variant reached 14 wrong rows; its best NOT is semantically redundant. All diagnostics remain in `/tmp/oec/pequalnp-pilot-121/not-elimination/`. No witness was found.

Useful essentiality refinement: in a circuit with exactly one NOT, replacing that gate by false gives a monotone function below the original output, while replacing it by true gives a monotone function above it. If the original output is an edge function, an essential false-replacement has a witness among minimal true edge inputs; an essential true-replacement has a witness among maximal independent-set inputs. The SAT agent is using these small projected tables to exclude redundant-NOT candidates.

New Lean component `lemmas/OneNotCut.lean` adapts checked `L_meta_8295` and strengthens the hypothesis to exactly one NOT. It returns a monotone prefix and suffix, exact gate accounting, the distinguished NOT position, the original evaluation factorization, and evaluation after replacing the NOT by either constant. The independent reviewer approved its final source hash before the first compile. This component is intended for the actual-circuit link to the Petersen bracket witnesses, not as a standalone proof of L-meta-2592.
