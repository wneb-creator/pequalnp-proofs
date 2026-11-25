# L-meta-2585 research checkpoint

The exact posted theorem remains unproved and unrefuted. No proof PR was opened for it.

The conditional reduction `R_meta_2585_46.lean` passed its named Lake build and the local reduction checker. The public gap row does not carry `reductions: true`, so the publication guard refuses it. This is not an accepted solution of the gap. Public bot confirmation: https://github.com/open-goat/pequalnp-proofs/pull/11110#issuecomment-7149020857 . Latest metadata examined was updated2026-11-25T01:05:39.438Z; its relevant row is preserved in `handoff-status.json`.

The reduction has three children: minimum-size normalization, the vertex-cover cost lower bound for a least normalized circuit, and synthesis of a read-1 circuit from a vertex cover. Normalization and synthesis were separately proved in the archived standalone Lean files. The general cost lower bound remains open in this work. It must account for AND gates whose values are not bounded by the output function; counting independent cones would be invalid because gates may be shared.

## Checked Lean components

Sources are in `../../lemmas/`; complete logs are in `../../logs/`.

- NormalizeLeast2585: generic normalization while preserving global minimum size.
- Synthesize2585: read-1 star-cover construction with the advertised gate budget.
- CleanNF2585: the normal form is read-1 if every AND gate is bounded by the output function.
- SharedOrBudget2585: rectangle/star facts and a shared-DAG leaf-count budget.
- LeastGatePrivateBoundary2585: private positive or negative witnesses for operands of gates in a minimum circuit.
- CoverLowerBound2585: read-1 cover lower bound and a conditional refutation adapter. No witnessing circuit was found.
- ForestElim2585, ForestElimCounts2585, ForestElimAO2585: constant-propagation budgets and exact AO2 gate-shape preservation under the compiler invariant. They do not yet assemble a full input-restriction theorem or a forest induction.
- NormalFormWitness2585: a small counterexample to the stronger, invalid claim that the generic normal form alone implies read-1. It does not refute L-meta-2585.

The forest-only mathematical route is documented in `direct/FOREST_ROUTE.md` and `sibling/FINDINGS.md`, explicitly not Lean checked. Leaf deletion separately charges one OR and one AND in different restrictions. Cyclic cores remain the obstruction.

## Validation of the conditional reduction

Source SHA256: ea94d10a40c78564ac2154f6c5894a3c0a660476cc8789bc4296a1f51fef2070.
Named Lake build: PASS,2.4seconds. Local checker: ACCEPTED in reduce mode,1648constants, only standard axioms. Import/format guard: PASS. Cleanup:48 to43lines,3616 to3435bytes. Publication eligibility: REFUSED because reductions are not enabled for this gap. Logs and cleanup metadata are preserved separately under `../../logs/`.

## Search evidence and limitations

`counterexample/SEARCH_MANIFEST.md` describes the exact encodings, completed external UNSAT results, timeouts, replay commands, and rejected-model audits. Every candidate model was checked on its full Boolean truth table; an independent scalar evaluator confirmed all retained rejections. No counterexample was found. These computations are not Lean proofs.

`genetic_cpp/` contains the stochastic search and complete logs; its failure to find a witness is not exhaustion. `symbolic_p4/` contains the separate shared-P4-template search:15 below-bound instances, one restricted-family infeasibility result and14 time limits, with no improving circuit. It says nothing about circuits outside those templates.

Research sources and scope distinctions are recorded in `sibling/LITERATURE.md`, `sibling/OR_BOUND_REVIEW.md`, and `structural/BICLIQUE_AND_RESEARCH.md`. Historical open-problem statements were not promoted to claims about present-day global status. `structural/PR_CENSUS.md` records the complete GitHub census. Root also examined57 newly merged files at upstream9c4fa2bd4f85e59f6cebbe16ca9a4ba71df2b472; none supplied the missing general charge.

Sub-agents:7 (six primary delegates plus one independent matching-bound brainstorm).

The unchanged reduction source is archived at `../../candidates/R_meta_2585_46.lean`; it has been removed from the active Outside directory for the next assignment.
TIMING total=122.9 subagents=7
