# Independent review: L-meta-2592

Reviewed repository CONTRIBUTING.md/README.md, desk assignment, SAT encoder, and partial source.

## SAT search

- AND, OR, and NOT CNF clauses were checked independently on all gate truth-table rows and match their intended operations.
- One-hot selectors choose exactly one operation and predecessor per operand. The sequential counter enforces at most four NOT gates (the initial search version).
- Every candidate is simulated on all 1024 inputs before FOUND is reported.
- Independently enumerated the Petersen automorphism group: 120 permutations, with one orbit each on 10 vertices, 15 unordered edges, and 30 unordered nonedges. This validates the five first-gate orbit representatives for normalized nondegenerate circuits.
- Independently counted 76 false inputs, distributed by Hamming weight as 1, 10, 30, 30, 5. Together with 15 true edge inputs, these are the 91 initial constrained rows.
- Search UNSAT is NOT a Lean proof or a lower bound for all circuits of size at most 19. Exactly 19 gates, every gate used, distinct binary operands, no constants/invalid reads, and the NOT bound require mathematical normalization/completeness arguments before an exhaustive interpretation. The search author explicitly agrees and uses the program only to find witnesses.

## Partial Lean source

- NotCountFloor.lean reuses the checked L_meta_6581 certificate verbatim except for namespace renaming and replacement of its final theorem by three count lemmas. The complete normalized diff is saved in scratch as review-partial.diff.
- The new partial claim excludes circuits of size at most 19 with at least four NOT gates: binary floor 16 plus NOT count at least 4 exceeds 19. Its graph expression agrees with the assigned Petersen function.
- Final helper namespace has been corrected to PEqualNP.Outside.L_meta_2592_aux and adjacent namespace blocks merged.
- Static scan found no sorry, new axiom, native_decide, forbidden commands, _root_, string literals, attributes, or custom types/instances. Array literals using #[...] are data, not # commands. Only permitted resource-limit options occur.
- Only PEqualNP.Defs is imported, as allowed by the gap.
- This is a PARTIAL component. It does not prove the posted theorem, which also includes one, two, or three NOT gates, and it currently has no theorem named PEqualNP.Outside.L_meta_2592. Do not submit it as a completed proof PR or describe the original statement as checked.
- Build and checker validation are still pending; no kernel-level verdict is claimed by this static review.

Review timestamp: 2026-11-25T14:22:00.724314+00:00

## Pre-push review of compiled retention partial

APPROVED for archival partial push, not a completed-proof PR.

- RetentionStandalone.lean: 205 lines; SHA256 31ea9f275eb47583062f56d2c4c06c2379c24db4af1564c28e69a5bf7a39be96. Reported Lean exit status 0; complete stdout/stderr log exists and is empty.
- Independently decoded the ten input truth tables and verified the target equals the assigned Petersen expression on all 1024 rows.
- Independently checked all 360 row-pair witnesses (ordered distinct inputs, four signed gate kinds). Each keeps the computed gate and all other inputs fixed while changing the target.
- Reviewed the induction transferring target row difference back to an available wire, then the two retention lemmas. They correctly force both first-gate operands to remain available.
- Retention.snippet.lean exactly equals the standalone source suffix.
- The named L_meta_2592.lean remains unchanged from prior review, SHA256 86b2117c86d8ece99a481b2674974652fb7b61396a9072f6d83bb51529ca4a98.
- Pending tree contains only new named Lean file and results/ artifacts; no tracked source/config edits. No forbidden Lean words, strings, or credential-shaped data found in reviewed additions.
- FirstProjection.lean is uncompiled research at this review point. RetentionStandalone imports a narrower project definition module than the desk lists, acceptable only as an archival research component; the final named proof file still imports PEqualNP.Defs only. The final PR must contain only the named proof file with the exact posted theorem.

Review timestamp: 2026-11-25T14:29:34.571656+00:00

## RetentionFresh pre-push review

PASS for archival partial push. The delta adds only the finite raw_bin_fresh_samples certificate and raw_bin_fresh theorem (16 lines). Independently checked all 360 ordered-distinct-input/signed-operation combinations produce a truth table different from every raw input. Reviewed the List.all elimination proof. Source exactly matches compiled scratch and recorded SHA256 fd1119437485f59593db267baac1117135207a1cc98793b90b234ece4c183942; 221 lines; complete archived build log empty, validation reports exit 0. No forbidden tokens. This remains a partial component, not the posted theorem.

Review timestamp: 2026-11-25T14:33:16.328790+00:00
