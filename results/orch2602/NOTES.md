# L-meta-2602 shared findings

Assigned2026-11-25T05:50:38Z after prior lease invalidation. Exact statement and allowed imports are saved alongside.

2026-11-25T05:56:05.871982+00:00 compact_benchmark: checked67 TopForm-related final statements and broader edge/size census. Strongest valid general bounds remain L2237(read1) and L1491(top/junk/Ustar accounting); L3444/L3446/L2969 are refutations. Inventory in graph-library-search.md and locations JSON. GraphSearch geometry helper checking separately.

2026-11-25T05:56:13.373194+00:00 normalization

Normalization lane findings (paused after parent reported HTTP410):
- Posted hypotheses are two Boolean formal-derivative traces at singleton0 and singleton13, both zero at the output; no input/output loophole identified.
- Existing R_meta_2602_2 reduces to a56-gate deleted-edge-face bound plus a global derivative-path theorem. R_meta_2602_415 uses a guard lemma and stronger face obstruction.
- Checked sources L_meta_2613 and L_meta_2615 provide strong pair-active AND counting under the extra global condition that every AND gate implies the target function. Top-form normalization alone does not establish that condition.
- Public partial PR12286 by wneb-creator/pilot60, revision d76942fe040a2a750d4a5bf2f152ec5ae277bf9f, URL https://github.com/open-goat/pequalnp-proofs/pull/12286, already supplies the entire planned local derivative package. Source is /tmp/oec/pequalnp-pilot-61/PR12286_L_meta_2602.lean (226703bytes; no final theorem).
- Useful declarations in that partial: Derivative.derivative_unique (83), derivative_zero_forces_repeated_and (103), repeated_and_of_pair (202), derivative_true_iff_walk (258), Clamp.minimum_all_active (4629), Clamp.minimum_all_essential (4933), Normalized.minimum_obstruction (4960).
- Planned next genuinely additive wrapper: combine minimum_all_essential with existing counterexample_shape to obtain a minimal marked-zero circuit with AllActive, AllEssential, positive AND nesting, a dirty AND, and explicit exclusion of both marked derivative paths. Also express MarkedZero equivalently as absence of those paths using the existing canonical derivative witnesses.
- No2602 build has been launched by this lane. No new proof source exists yet; all findings are read-only and no checked status is claimed for PR12286 during this task.

2026-11-25T05:56:15.157761+00:00 structural findings (paused on root lease HTTP410):
- Existing checked bounds do not presently close2602. L2237 bounds |E|+vertex cover by size+1 under ReadK1; L2235 covers only the read-once edge subset. L3706 adds read-twice edges to the RHS and does not give the desired strictness.
- R_meta_1482_3 already proves a zero derivative forces nested ANDs if no AND is nested; its unresolved hypotheses are global64 lower bound, no junk AND in minimal circuits, and no nested AND in junk-free minimal circuits.
- PR12286 contains derivative/path equivalence, repeated-AND witnesses, first dirty nonedge witness, gate erasure, and derivative-preserving clamp normalization. Its Clamp.minimum_all_essential (near line4933) ensures every gate is essential on some true edge input and is stronger than the final minimum_obstruction wrapper.
- PR12286 tightCircuit/tightness65 (lines3046–3260) has65 gates and both marked derivatives zero. The construction rewrites H OR (a AND b) as (H OR a) AND (H OR b), rereading edges in H for one extra gate. Thus any proposed lower bound above65 is false.
- Candidate structural route: deletion of the marked endpoints leaves45 edges/24vertices and a putative56-gate face lower bound; double reread should force at least9 distinct gate functions lost on that face. R_meta_2602_2 separates these into face lower-bound and weighted-path hypotheses, neither automatically supplied by the inventory.
- No new Lean proof or build in this lane before root stop. Child was preparing independent52-edge/C4-free/cover13 geometry, but was told not to launch its check.

2026-11-25T05:56Z compact_benchmark: Geometry probe had already started before the new HTTP410 stop instruction, and completed exit1 in7.831s. Finite incidence,52-edge andNoFourCycle proofs had no errors; cover injection fails only at line42 from ambiguous Fin.val specialization. No full compilation claim. Expected repair: explicitly type fun z : Fin26 => z.val in congrArg; not applied because root ordered stop. Source SHA5808475ff06af99593356cf4e9abc685c39d0e9ba554964c04e35b5cb2593938; complete build log+JSON preserved here.

2026-11-25T05:56:40.511640+00:00 structural correction after child report: GraphSearch.lean had started just before the pause and exited1 in7.831s; the sole reported error is a Fin13/Fin26 inference mismatch in the cover injection. The complete geometry file is not yet checked. Source, log, metadata, and detailed67-file census are preserved in orch2602; no process remains. No repair was made after the stop instruction.
