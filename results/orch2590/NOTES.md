# L-meta-2590 orchestration notes

Ownleasea1cdb295-f879-4902-baa7-ce60a1f1590b received15:10:16UTC, expires15:30:16UTC. Exactstatement scratchstatement-2590.txt. MonotonePetersen19 lowerbound. Reductionsopenbut3livecapalreadyfull.
PreviousL2592andL2583leasesunexpected410; allworkpreserved, canreusecheckedhelpersforthisnewgoal.

## Monotone minimization 2026-11-25T15:14:45.152093+00:00

`MonoFirstChecked.lean` clean checked. New namespace L_meta_2590_aux.MonoFirst contains MonoL, elim preservation, drop_core_mono, clean_mono, LeastMono, least_mono, least_mono_first. It minimizes circuit length only among clean monotone circuits; therefore no unsupported transfer from an all-basis minimizer. Nonconstant target not equal to a primary input guarantees first gate exists. The first gate is AND/OR on two distinct primary inputs; repeated input would be an alias removed by drop_core_mono, contradicting monotone minimality. Existing infrastructure is the earlier FirstBinary checked source under L_meta_2592_aux.CircuitProof; new declarations begin after its closing namespace. Full snapshot e40091e655fb4e1ed2362282a601b97bb45338695477775de323a44b8c2e99b1. No remaining proof errors or warnings.

[2026-11-25 15:15:21 UTC, proof_strategy] MonotoneResidualChecked.lean compiled exit0. New restrict_core_mono, restrict_two_drop_mono preserve Monotone2 and bound actual circuit size. residual_rename_mono turns an arbitrary Petersen vertex-zero cofactor into standard nine-input deletion with no size increase. Hash 98029eebd0d1a2da625f275ad4d9944dc3aed3dcef6c33620c6f71dae79a9abb. Assembly with MonoFirstChecked for unconditional monotone two-drop and conditional floor18 in progress.

## Finite AO Petersen route (2026-11-25 15:17 UTC)

Launched three600-second19-gate AO2 searches after root15:12:27 renewal: firstAND(0,1), firstOR(0,1), firstOR(0,2). In a least circuit, firstAND(nonedge) is false on every prime pair and can be deleted; the old fifth symmetry case wasNOT and is absent here. Encoder uses30 exact monotone boundary rows, ordered active inputs, leadingOR(0,0) padding, all active gates used, row incomparability, both boundary clamp bounds, lex order, and pair symmetry. No solver verdict yet.20-gate pinned positive control passes and was independently checked on1024assignments, all15READ1pairs, allCNFclauses. Complete artifacts in `results/orch2590/sat`. Checked boundary and ordered-pair orbit certificates in `lemmas/sat_strategy`; v2 boundary adds pairwise accepted unions for the15 negative masks, supporting root CNF route.

[2026-11-25 15:17:44 UTC, proof_strategy] MonotoneTwoDropChecked.lean compiled exit0, hash abb0579b1fc8d9ecdf57a870870f037e19448fde12ee2bc443e7649c5445b973. Final petersen_two_drop_mono unconditionally gives some zero-vertex cofactor computed by Monotone2 D with D.size+2≤C.size. petersen_floor_of_nine_floor transfers any standard nine-vertex monotone lower bound k to full Petersen k+2. Full L8035 integration prepared separately but not yet compiled.

CHECKED read1subclass at 2026-11-25T15:20:34.598627+00:00: results/orch2590/lemmas/counterexample/PetersenReadOne.lean (Defs-only inline genericL4897.General and finitePetersen specialization). IsAO2+exactPetersen+IsReadK1 implies20≤size. Fullcompile exit0, warningsonly. This is apartial because arbitrarymonotone→read1 unproved.
