# Petersen SAT investigation, pilot 110

This directory preserves search evidence, not a proof of L-meta-2592.

- CaDiCaL 3.1.0 was built from github.com/arminbiere/cadical in scratch.
- The repository generator `notes/data/lrat-link/gennot.py` generated the base CNFs.
- Thirty boundary rows with at most four NOT gates were SAT in 17.39 seconds. The decoded circuit fits all thirty rows but fails 250 of the full 1024 rows. The complete SAT witness and independently checked clause satisfaction are preserved.
- Both 82-row variants reached their 300-second limits without a SAT or UNSAT verdict.
- A 1200-second full-table search and a 600-second strengthened partial-table heuristic were running when this snapshot was written. Their final logs will be added later.

## Soundness limits

The base encoding has soundness proofs in `Library/LRAT/LinkN.lean` and `LinkN2.lean`; these modules are not allowed imports for the assigned step. Inlining and adapting them would be necessary.

Additional search restrictions require Lean normalization proofs. They include at most four NOT gates, a NOT surviving or a leading padding gate, source incomparability, and a first-gate graph-automorphism representative. The strengthened partial-table heuristic also uses global Petersen reader/count bounds. Combining these bounds with minimality only on sampled rows is not complete: an UNSAT result from that heuristic would not establish the target. Every SAT candidate is checked on all 1024 assignments before it can count as a counterexample.

`SatCofactor.lean` in the lemmas directory is independently Lean-checked and establishes the finite cofactor essentiality property. That lemma is separate from the unverified SAT normalization bridge.

Compressed files retain complete contents. SHA256 hashes in manifest.json refer to the original uncompressed files.

## Update after the 600-second heuristic

The strengthened 82-row heuristic reached its 600-second wall limit without a verdict (340.83 CPU seconds). Its complete log is now included. A new 82-row variant omits source incomparability, while retaining global reader/count bounds; this avoids using row-only minimality together with facts requiring full truth-table correctness. Its Lean completeness bridge is still pending.

The default `bv_decide` tactic is not admissible here because its native certificate check adds a computation axiom. This was verified against the official Lean documentation on 2026-11-25: https://lean-lang.org/doc/reference/latest/Basic-Types/Bitvectors/ . The finite helper proofs instead use kernel computation.

## Full-table run completed

The first 1024-row run reached its 1200-second limit with no SAT or UNSAT verdict: exit0,1200.01 wall seconds,792.42 CPU seconds,382.61MB peak resident memory. Its complete log is included. A second full-table run now adds the checked16 non-NOT floor (hence at most3 NOT gates), plus the first-gate reader bounds. It is bounded to1200 seconds.

The checked source files are frozen under checked-sources/. They include the finite cofactor witnesses, output bounds, exclusion of constants/signed inputs, the non-NOT/NOT count partition, and the pair-orbit symmetry table. Their hashes and successful compiler status are recorded in checked-components.json.

## Lease interruption

At 2026-11-25T14:48:52.660458+00:00, root reported HTTP410 on renewal and directed a pause. SAT PID41316 was stopped with SIGSTOP. The full-table at-most-three-NOT log is saved as a paused snapshot; it has no verdict. The cleaner82-row run had already finished with no verdict after600.01 wall seconds and406.22 CPU seconds. A focused deletion construction encoding was prepared but never launched:15 suffix gates, exactly oneNOT, supplied inputs x0 throughx8 and x4 OR x6, all512 valid rows. It is a construction search only. Awaiting root instructions and a new lease before any solver resume.
