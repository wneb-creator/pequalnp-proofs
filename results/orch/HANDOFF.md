# L-meta-2089 — supporting results, not a completed proof

The named Lean file builds, but it does not declare the requested theorem. The local checker rejects it as `no-theorem`. Do not submit this branch as a proof PR. The branch intentionally preserves research artifacts in addition to the named file.

The target rules out at most 62 AND/OR gates with two distinct wires whose conjunction accepts all 52 incident point-line pairs and rejects all 236 degenerate maximal false inputs of the order-three projective plane. Incidence is exactly p = l + d modulo 13, with d in {0,1,3,9}. The exact posted statement and permitted imports are saved in statement.txt and imports.json.

The main file contains checked geometry and semantic helpers, a false-OR certificate bound, a compatible bad-pair bound, and a precise new counting endpoint. LinearBound.plane_linear_outputs_bound proves 39 OR gates are needed when one circuit supplies all thirteen neighbor-sum outputs. CofactorBridge.select_wire_linear_factors proves that, for each point, one of the original two factors has exactly the required neighbor-OR cofactor. CofactorQuota.joint_point_certificates supplies at least 3 actual OR-gate identifiers per point in the original circuit.

The remaining problem is a total gate bound that accounts for the shared certificates and the other required gates. The thirteen certificate sets need not be disjoint, and no verified argument turns them into the required total of at least 63 gates. In the dual standard 64-gate construction,39 refined cofactor charges can lie on 12 combining OR gates; a one-for-one assignment of reused charges to selector AND gates fails: 27 reused charges versus 13 selector AND gates. Neither cloning thirteen restricted circuits nor assuming an arbitrary circuit has a single AND level gives a valid proof.

The checked OperandWitness artifact is a 62-gate single-factor example with 52 positive pairs,12 bad pairs, no accepted singleton, and only one wire accepting every positive pair. It disproves a proposed single-factor shortcut, not the posted two-factor statement.

For every enumerated compatible closed pair in the computational census, at least one bad-pair family uses at most 5 rows or at most 5 columns. This is not Lean checked. A zero bad-pair row gives an exact singleton shadow only; higher-degree line junk may remain. Full cofactor linearity requires actual rejection of the singleton maximal cut, as in the checked selector bridge.

No counterexample was found. Strict full-domain search performed 15,140,404 mutations; earlier relaxed populations performed 181,506,495. A separate 11,000,315-mutation search omitted 52 flag rows and also failed; every saved candidate was independently checked against all 236 negative rows and failed. Timeouts in SMT searches mean UNKNOWN, not UNSAT. All reported source computations and limitations are preserved in experiments/.

To reproduce the Lean checkpoint, use the repository-pinned toolchain and Mathlib cache, then run `lake build PEqualNP.Outside.L_meta_2089` from lean/. Never run lake update. From the repository root, run `node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_2089.lean results/orch/statement.txt check`; rejection for the absent target theorem is expected. Full build, checker, format, and axiom logs are preserved here. Some experiment scripts retain the original scratch paths; restore their inputs there or adjust those paths before rerunning.

At the latest desk refresh, all three allowed reduction slots for this step were occupied. No fourth reduction was submitted. Only this pilot's lease was renewed; no other pilot's lease was modified.
