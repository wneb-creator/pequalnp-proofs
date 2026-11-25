Binary16 independent review

Reviewed 2026-11-25T14:07:27.945144+00:00 by status_review.
Snapshot: results/orch/lemmas/Binary16.lean, 288897 bytes, SHA-256 a767ba8feaee179e939fd7217bb0d224d7e62fe24b93357d10d551c8ada9711b.

Verdict: suitable as a substantive partial after its author's Lean compilation passes. It is not a proof of the posted gap and is not yet a submission file.

Semantic checks

- Full.edge lists exactly the 15 edges in the desk's L-meta-2592 statement, in the same order.
- Independently recomputed all 1,024 values of Full.graph in Python and checked all ten input truth tables.
- Setting vertex 9 to false gives exactly the 512-row Deleted.graph copied from the checked L-meta-670 proof. The deleted graph has the outer 5-cycle, four surviving spokes, and inner edges 5-7, 6-8, 8-5. All nine deleted input tables independently checked.
- The copied signed lower bound forbids at most 14 binary operations when negations are free, yielding Deleted.signed_lower = 15. The new restriction sends input 9 to the constant false wire; projected_bound and constant_mass add one to obtain at least 16 non-NOT gates.
- FanInTwo is retained. The table interpretation uses the circuit's actual default-false reads and allows empty/singleton gate inputs; no validity assumption is silently added. NOT normalization treats negations as free, so the binary count conclusion is stronger than merely a total-gate lower bound.
- binary_not_lower then gives 16 + notCount C <= C.size. Consequently three_not_bound gives notCount C <= 3 for size <= 19. Cases with one, two, or three NOTs remain unresolved; this partial alone does not prove the gap.

Format and trust checks

- Official outside-guard checkImports/checkPlain passed with only PEqualNP.Defs allowed.
- 288,897 bytes at initial review, below 512 KiB; no forbidden axioms, sorry, native_decide, bv_decide, quotes, or forbidden attributes were detected by the real text guard.
- Helpers are in PEqualNP.Outside.L_meta_2592.Deleted or .Full, with matching namespace endings. The real own-namespace guard reports only the expected missing final fully-qualified theorem PEqualNP.Outside.L_meta_2592.
- No alternate data types or instances were introduced; definitions use library types. Kernel finite-case computation uses decide +kernel.
- Lean compilation is owned by restriction_review and was not redundantly rerun here. A full checker verdict is still required for any eventual final proof.

Endpoint was independently read earlier: AND/OR monotonicity and final-NOT exclusion are mathematically sound, including empty NOT inputs. Its current helper-only file intentionally lacks the final posted theorem; its author's compile result remains authoritative for that partial.

Endpoint final snapshot independently reread after compilation: 182 lines, 7,745 bytes, SHA-256 97b272a4105befedb2cb8f8df639b6a75c18f63491d5a87f0d377269f349637b. The author reports exit 0; endpoint-build-4.out and endpoint-build-4.err are both empty. Verdict: PASS for preserving the checked helper partial. It remains a helper-only file, so the official plain-file screen reports no theorem and the namespace screen reports no final posted theorem; those expected omissions must be addressed in any final submission.
Final elaboration-fix review 2026-11-25T14:26:01.156103+00:00

Snapshot: 289281 bytes, 5021 lines, SHA-256 6d460fb7b9aca1a87b1bd55a2d68ea9cec143436e1822e4bb0460f0cf354e4e5.

PASS for preservation. The complete 243,603-byte DeletedSigned.lean base is included verbatim. The final extension explicitly fixes signed extraction to u=true, raises only permitted recursion/heartbeat limits for finite checks, transports Reach into the copied Deleted namespace by constructor induction, and unfolds isNot in the count partition bridge. These are elaboration and namespace fixes; the semantic conclusion remains exactly 16 + PEqualNP.NotBracket.notCount C <= C.size, and the size-19 corollary remains at most three NOT gates. No full-gap theorem is claimed. Final source contains no _root_, string quotes, sorry, native_decide, axioms, unsafe declarations, or attributes. Author reports both the DeletedSigned base and the FullExtension checked with exit 0; the self-contained combined-file build remains required. Concatenating this helper with the named partial is sound provided imports remain at the top and no names collide; the kernel build will check this integration.

