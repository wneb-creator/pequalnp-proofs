# Finite certificate strategy — L-meta-2592

## Existing usable source

- `lean/PEqualNP/Library/LRAT/Checker.lean`: 578 lines, 26,553 bytes. Pure kernel RUP/LRAT verifier, soundness at `check_sound`/`checkW_sound`; segmentation available.
- `lean/PEqualNP/Library/LRAT/LinkN.lean`: 1277 lines, 55,210 bytes. General AND/OR/NOT normalized circuit to CNF model. Handles empty gates, repeated reads, invalid reads, source sorting, padding, duplicate negation elimination.
- `lean/PEqualNP/Library/LRAT/LinkN2.lean`: 597 lines, 26,646 bytes. Lexicographic adjacent-independent-gate ordering. Main lemma `lower_of_unsat2` turns UNSAT into a gate lower bound.
- LinkN uses only first ~45 lines of Helpers/Shannon (wire prefix/length/getD facts), not the large Shannon synthesis theorem.
- `notes/data/lrat-link/gennot.py` mirrors exact CNF and source normalization. Search agent informed.
- Root import `PEqualNP.Defs` contains only monotone LRAT encoding definitions; **none** of the verifier/bridge modules is an allowed import. A final single-file proof must copy/namescope needed source (about 110 KiB before certificate), or obtain newly allowed imports from site; we do not contact desk except root.

## Limitations

The copied verifier has a custom `Trie` inductive and bridge has custom `Model`, `Valid`, `NF` structures. These can be adapted to standard Mathlib types but need work to retain automatic-merge plain-file requirements; raw copying may trigger manual review. Existing generated certificate test `notes/data/lrat-link/trial-not/P4Not.lean` uses huge decimal packed numerals, unrestricted options and forbidden imports; it is an internal example, not admissible final proof format. A packed certificate must instead use small-numeral words and declaration-local permitted limits.

## Promising finite row sets

Bridge permits any rows below 1024, so an UNSAT certificate on a subset suffices. Candidate subsets: Petersen 15 positive edge masks plus 15 maximal false independent sets (30 rows), all weight-at-most-two masks (56 rows), or their union. SAT candidates from a reduced row set can be tested on 1024 rows and refined (CEGAR). All truth-table rows remain fallback.

## Current gap reductions

Three existing reductions use all slots: `R_meta_2592_271` (15+notCount floor and 1..4 NOT), `R_meta_2592_318` (last-NOT factorization and separator), `R_meta_2592_408` (normalization and normalized lower bound). A fourth reduction should not be submitted.

## Nearby checked facts communicated to combinatorial agent

Full Petersen binary floor in `L_meta_4725`; many P9 induced-subgraph restrictions in `L_meta_7493`, `L_meta_8551`, `L_meta_7820`, `L_meta_8039`. These may support gate-elimination, but are not permitted imports either.

## Checked partial

2026-11-25T14:09:47.556181+00:00 — `results/orch/lemmas/Certificate.lean` compiled with exit 0 under Lean 4.36.0. 2235 lines, 95,849 bytes. This is only LRAT soundness and the conditional circuit-to-CNF lower-bound bridge; there is no Petersen UNSAT certificate. Logs: `/tmp/oec/pequalnp-pilot-111/certificate-build.stdout` (warnings only) and `.stderr` (empty).

Boundary-only exact-2-NOT SAT model fails 874 of the 1024 truth-table rows. Stronger row-set exact-2 and exact-3 searches are running for 600 seconds each, without proof traces.

## Count-preserving normal form

2026-11-25T14:15:42.868894+00:00 — `CertificateCount.lean` and `CertificateBound.lean` compiled with exit 0. The final extension proves exact NOT-count change when bypassing a gate, invariance under source/gate swaps, and `exists_nf2_notBound`: a valid model with at most k NOTs has a lexicographically ordered normal form with at most k NOTs. These are conditional support lemmas, not the gap proof.

The stronger exact-3-NOT SAT run was stopped at coordinator request to relieve CPU pressure; no SAT/UNSAT verdict. The exact-2 run remains until its 600-second limit. No more builds or solvers will launch during the resource pause.

Final status of this SAT round: strengthened exact-2 NOT run hit its 600-second wall-clock limit with no SAT/UNSAT verdict; exact-3 stopped at 521.59 seconds without a verdict. All own solver and build processes are finished.

## Physical-circuit count transport and counted CNF bridge

2026-11-25T14:25:24.770811+00:00 — `CertificateTransport.lean` compiled self-contained with exit 0 (2608 lines, 111631 bytes). It proves `modelNotCount s (ofCirc n s C) ≤ NotBracket.notCount C`, sound at-most-k negative cardinality clauses, `link2_notBound`, and `lower_of_unsat2_notBound`. Normalization can delete NOT gates, so the encoding deliberately includes zero through k NOTs. It never requires exactly k or a positive count.

The count clauses are `reverse(sublistsLen (k+1) (range s))`, each combination mapped to negative operation-NOT selector literals. This bridge covers only the existing physical AND/OR/NOT LinkN2 encoding. The search agent's newer signed-binary/producer-polarity SAT encoding is different and needs its own bridge before any UNSAT result can be used. There is still no Petersen UNSAT certificate or final theorem.

## Clause order sanity proof

`CardinalityOrder.lean` compiled with exit 0 and empty stdout/stderr using the cached `CountTransport.olean`. It kernel-checks that `fNotAtMost 10 19 1` and `fNotAtMost 10 19 2` equal lexicographically increasing index loops with explicit negative literal `2110*j + 9`, exactly the clause order and literal encoding produced by Python itertools.combinations on gate-NOT variables `1055*j + 4`. The small development modules `CountTransport.lean` and `CardinalityOrder.lean` import local partials and require building those local oleans with their directory on LEAN_PATH; the portable support artifact remains the self-contained `CertificateTransport.lean`.
