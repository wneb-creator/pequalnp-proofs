# Compact finite layout certificates

These are independently generated certificates for the exact L-meta-9775 graph, using the generic layout and RUP framework from the public L-meta-9774 proof. They prove conditional circuit exclusions, not the posted positive existence statement.

The complete cap11 census has 117 ineligibility masks. All 115 mixed masks yielded UNSAT; only the two pure sides 127 and 16256 yielded SAT in this necessary-condition encoding. Those two sides have separate geometric exclusions. Automorphism reduction gives 36 mixed representatives; checked private projections and an additional projection for mask63 remove several representatives from the final assembly.

For Bplus=10, the exact residual count is popcount(I)-4. Weak clauses exclude1290 and8488 with k=0. Paired exact-neighborhood clauses exclude127 and16256 with k=3, and4757 with k=2. The paired rule requires Bzero≤1. An earlier diagnostic using4757/k0 was not the relevant budget case and is not used. SAT layout models are not circuit witnesses.

`compact-packed/` contains 28 stable packed certificate sources and their unpacked JSON cores. Twenty-seven selected files were checked successfully by Lean; complete logs and exact source hashes are in `compact-packed/checks/`. P63 is superseded by a geometric lemma and was not compiled. W16256 andW8488 were subsequently checked and exported for the initial complete modular proof, though symmetry will remove them from the compact final assembly. `SNAPSHOT_MANIFEST.json` freezes the source/core files. The theorem names are `Compact.excludeP<m>` for Bplus=11/Bzero=0 and `Compact.excludeW<m>` for Bplus=10/Bzero≤1, all in namespace `PEqualNP.Outside.L_meta_9775.UpstreamCore`.

Every certificate was extracted from positive-hint ASCII LRAT. The extractor independently checks each addition by unit propagation, retains the dependency closure of the empty clause, and emits ordinary kernel-checked `decide +kernel` computations. Deleted clauses may safely remain in the replay database. A separate agent independently reconstructed all28 scheme families from the graph, decoded every packed payload, and replayed all learned clauses; see `../review-rup/packed-independent-validation.json`.

`compact-artifacts.tar.gz` preserves complete CNFs, source mappings, LRAT traces, solver diagnostics, and deletion-minimization diagnostics (1525 files, SHA256 a1b8c1ed839040e0411b9786ffdd731765ea31d9279282ed67547cf8c20ff849). Its per-file manifest is adjacent. Generic gate-synthesis runs preceding this work returned UNKNOWN and establish no lower bound.

The packed individual certificates are valid independently of the final single-file size limit. Root is selecting smaller geometric/code-only exclusions and assembling the complete negation separately.

The final compact payload is now checked and frozen in `compact-final/FINAL_SELECTION.json`: 21 selected files, 194981 source bytes, all kernel-checked with exit0 and exported oleans. These use64-entry clause tables and96-row proof chunks. There are18 Bplus11 representatives plus the three Bplus10 representatives127,1290,4757. The extra P4293 payload was also checked but is replaced by a smaller geometric/code argument. All22 actual packed source files were independently decoded and their clauses replayed; see `../review-rup/compact-final-independent-validation.json`.

No stochastic or exact gate-synthesis witness of size24 was found. The result of this work is a checked set of conditional exclusions used by the parent agent's complete refutation.
