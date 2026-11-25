# Audit of accepted L-meta-3760 for L-meta-3451

The accepted file does not provide an arbitrary-junk normalization theorem. No proof code was copied or imported.

Relevant API in `lean/PEqualNP/Outside/L_meta_3760.lean`:

- `thm_1501`, line 1034: every least circuit for a nonempty graph can be put into TopForm with exactly the same size and exactly the same number of junk ANDs. The proof descends on the number of nested AND pairs, not the number of junk ANDs.
- `M1528.P1.S98.main_real`, line 2539: in TopForm, each below-F gate other than the output has a unique below-F OR reader; the below-F OR gates form a top aggregation tree.
- `M1528.P1.main`, line 3243: a counting inequality valid for arbitrary junk count. Its lower bound includes the number of junk gates and OR gates outside Lambda, but its right side contains the uncovered-edge defect |Ustar|. The cover-size companion bounds only the edges outside Ustar.
- `thm_1528`, line 4271: strengthens that inequality with formU/formZ, penalties, mixing, and cone charges. It explicitly assumes `junk G C = {g}`.
- `thm_1503`, line 4840: a centreless top must directly read the unique junk gate, and the opposite side lies in that gate's wmax. This is a substantive use of uniqueness.
- `Close.master_ineq`, line 6596: compares the strengthened count with a separately constructed star-cover upper bound. It consumes the one-junk strengthened inequality rather than producing a general bound.
- `Close.g_semantics`, line 6932: the junk gate is a product of two pure OR sums P and Q, with a combinatorial characterization of wmax.
- `Close.ustar_edge_structure`, line 7163: every uncovered edge routes through the same unique junk gate and has an endpoint in its wmax; the proof splits centreless and mixing cases.
- `Close.replace_gate_by_wire`, line 7598: deletes the unique junk gate when an earlier wire covers every Ustar edge and obeys an explicit soundness condition.
- `Close.final_proof`, line 10000 approximately: excludes exactly one junk gate, with no claim for two or more.

There are two model mismatches. `TopForm.junk` detects truth on ANY independent assignment, not merely singletons and nonincident crosspairs. A gate may be junk here while already satisfying L-meta-3451's rejection clauses. Also, `IsAO2` requires exactly two inputs and forbids constants, whereas the posted target uses Monotone2 with at most two inputs. A bridge would be needed before applying its leastness results.

One intermediate theorem admits a clear generalization: after putting a circuit in TopForm, the earliest strong-junk AND has no AND ancestor. Every earlier nonjunk AND is below F and excluded from its cone by TopForm; an earlier junk is excluded by the choice of the gate. Therefore its operands are pure OR sums and the P/Q product and wmax parts of `g_semantics` still hold without uniqueness. This isolates the first strong junk but does not control later junk gates. Later junk can filter its output, share OR contexts, or combine with it at a centreless top. The unique-junk Ustar routing and budget cannot simply be reapplied.

An induction on junk count has no descent step: thm_1501 preserves that count, and excluding count one does not rule out a minimum counterexample with count two. Replacing other junk outputs by independent formal inputs also fails to preserve the graph-function semantics, C4-freeness, and leastness hypotheses.

Conclusion: no clear path to the full posted theorem from this file within the current proof. Copying its roughly 10000 lines would only import a restricted one-junk result and substantial model-conversion work. The actionable open lemma remains a cost-preserving multi-junk exposure or a residual-edge budget that controls Ustar without the uniqueness hypothesis.
