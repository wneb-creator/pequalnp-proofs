Canonical refutation reproduction recipe

Status: the generic compiler and mask checker are checked, all13520 fixed sample-input bits are checked, and the51-OR baseline is checked. No program with fewer than51 ORs has been found. The conditional exact posted-negation wrapper is checked, and geometry completeness/agreement is checked. A concrete refutation still requires a genuine program with fewer than51 ORs and its certificate.

The fixed sample order is the52 Flags in line order with offsets0,1,3,9, followed by468 AllRows entries at flat index13*g+i. The target output mask is2^52-1; truth is2^520-1. All candidate certificates must use the exact fixed26 input masks from the checked CanonicalSampleData source.

1. Obtain a global26-input JSON witness with k<51, its two backward-reference lists for every OR, its final conjunction list, and the corresponding mask export. The witness generator must first embed any local witness and add the remaining incidence edges. Keep the original JSON, compacted JSON and complete solver/replay output.

2. Run the preparation script, which checks input count, strict OR budget, backward references, exact fixed input masks, every supplied OR mask, and the final acceptance/rejection mask before writing Lean. It emits both a helper refutation and the required main theorem PEqualNP.Outside.L_meta_1896 with the literal posted statement negated.

   python3 /tmp/oec/pequalnp-pilot-62/prepare-canonical-candidate.py "$PNP_WITNESS_JSON" "$PNP_MASKS_JSON" /tmp/oec/pequalnp-pilot-62/lean-modules/Candidate.lean

   The51-OR baseline is deliberately rejected. A generated file is still unproved until Lean accepts it.

3. From the repository lean/ workdir, source the existing lean-env.sh and use the existing guarded runner with LEAN_PATH pointing at the scratch module directory. Compile in this order, emitting each .olean beside its source and preserving a distinct complete log:

   - CanonicalCompilerSamples: the prepared update adds compile_mask_at.
   - CanonicalRefutationWrapper: contains certified_positive, certified_negative_row, and refutes_posted. Its parameters require k<51, a true mask check, generic-row completeness, and row agreement; none is an axiom.
   - Candidate: imports GeometryCompleteness and GeometryRowsAgreement, proves its closed mask check using decide +kernel, and supplies GeometryComplete.admissible_complete and AllRows.row_eq to the wrapper.

   The relevant command form is:

   LEAN_PATH='/tmp/oec/pequalnp-pilot-62/lean-modules' python3 /tmp/oec/pequalnp-pilot-62/run-lean-guarded.py /tmp/oec/pequalnp-pilot-62/lean-modules/Candidate.lean /tmp/oec/pequalnp-pilot-62/candidate-kernel.log /tmp/oec/pequalnp-pilot-62/lean-modules/Candidate.olean

   Renew the lease before the sequence. Only one memory-heavy Lean process may run at a time.

4. Flatten only Candidate's local dependency closure into the single named proof file:

   python3 /tmp/oec/pequalnp-pilot-62/flatten-canonical-modules.py Candidate /workspace/pequalnp-proofs/lean/PEqualNP/Outside/L_meta_1896.lean --manifest /workspace/pequalnp-proofs/results/orch/candidate-flat-manifest.json

   This emits only import PEqualNP.Defs, preserves every local declaration once in dependency order, and writes a source/hash manifest. It rejects forbidden root-namespace text, strings, proof escapes, non-simp attributes and unexpected options. The flattened file still needs its own build and independent review. Do not include TwentyOne or packing-search modules.

5. In lean/, run the named-file build with a complete log:

   lake build PEqualNP.Outside.L_meta_1896 > /tmp/oec/pequalnp-pilot-62/candidate-named-build.log 2>&1

   Then, from the repository root, run the actual checker explicitly in refute mode:

   node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_1896.lean /tmp/oec/pequalnp-pilot-62/statement.txt refute > /tmp/oec/pequalnp-pilot-62/candidate-checker.log 2>&1

   Preserve complete stdout/stderr and the actual verdict. The checker currently has a known missing-full-Mathlib-cache FAULT; a kernel build does not change that verdict. Do not label a FAULT as a checker pass.

6. Have another agent inspect the exact flattened diff, literal statement negation, gate budget and certificate scope. Follow the job's push-early rule and preserve every compiled milestone. The final proof PR must contain only the named Lean file; result logs and portable helpers remain on the work branch. Parent owns lease, push, PR and release actions.
