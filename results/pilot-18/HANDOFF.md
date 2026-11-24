# L-meta-1342 research handoff

Status at 2026-11-24 06:08:00 UTC: the posted theorem is unproved. No exact circuit with at most21 gates and no global refutation has been found. No PR has been opened. The pilot owns one lease; final release status will be recorded in TIMELINE.md.

The branch is pnp/pilot-18 on wneb-creator/pequalnp-proofs. The named Lean file is lean/PEqualNP/Outside/L_meta_1342.lean,2069lines, SHA256 0e0620c89307cf34be010940037cb187797eea76c85fc8c8a89b9bd1cfc56e5c. It builds successfully, but the required module-named theorem is absent. The actual posted checker ran at05:56UTC and exited1 after79.97seconds with REJECTED(no-theorem). Fulloutput is in posted-checker-wave9. Full build/axiom output and exact commands are in validation.txt and scaffold-* artifacts. No cleanup of a finished proof applies.

## Useful kernel-checked components

The file gives an exact22-gate baseline, a22-gate lower bound for clean monotone circuits, graph/cover facts, input-renaming/matching machinery, and a complete finite boundary test. The target_spec_of_boundary_check and target_witness_of_boundary_check lemmas turn an actual Monotone2 circuit passing the40boundary rows into the exact posted predicate, preserving a supplied size bound. A separate dirty22 control with full Lean logs is preserved in dirty22-checkpoint/S03/Dirty22Control.lean.txt. None proves the required bound21 or excludes arbitrary circuits.

## Closest construction

The independently scalar-checked21-gate best4 circuit computes F OR(x0 AND x2 AND x4). It has no false negatives and exactly four false-positive masks21,29,85,149. It is not a witness. Its immutable source SHA256 is b6da8ac6962d7836f2e5546423f5ed3846b7165fbe1ae47e58b8e470955101b0. The best4-pack-wave7 and allnegative-engine-wave7 archives preserve it and its checks. Full2048-input validation remains mandatory for any new candidate.

A seven-input construction route uses a=0,b=2,c=4,x=9,y=5,z=8,t=10 and target t(a OR b OR c) OR ax OR by OR cz OR xy OR xz OR yz. Any exact11-gate circuit for this function extends to a21-gate full witness by ten explicit gates. The related eight-input target includes vertex6 and edge(6,10); a12-gate solution extends by nine gates. Exact controls currently use12 and13 gates respectively, giving22 globally. See gadget7-wave9, gadget8-wave8, and sat-only-gadget-wave9 for reviewed encodings, validators, controls and portable reconstruction recipes.

## Lower-bound scope

The mathematical clean-prefix analysis excludes all331 k5/r0 support families and all68 k3/r2 families within its stated productive17-prefix/minimal-proper-full-cover hypotheses. The independently reviewed copy-cover argument now also excludes all258 remaining k3/r0 and800 k3/r1 families; together with the prior r2/r3 results this closes the analyzed k3 classes. The latest review is a598a661731287f9c3a3b586fc594484464ce60d2a92b6e197e070e1536feff6 in copy-cover-review-wave9. The newer proof/source review b3613cd880d5898ff18e5871e2d45dea9bb6fa621de9554bf2f97327ba6ac037 also accepts the112 k4/r0 exclusions and the recorded pure k4/r4 andk5/r5 exclusions, with the explicit proper-support cardinality-at-least-two guard. Its reviewer did not independently rerun the complete pure-case DFS. Mixed k4/r1..3 andk5/r1..4 cases remain open; all seven final mixed probes reached their time limits. These finite analyses are not Lean refutations, and no full assigned shard has been certified exhausted. The original unguarded forced-birth claim was false; its counterexample and corrected nonempty-edge guard are preserved in structural-wave7. Read NOTES.md and the individual lemmas reports before using a claim.

## Search evidence and resumption

Every completed production run retains full stdout/stderr and its outcome. UNKNOWN means no accepted result. Pinned toy/control UNSAT certificates prove only their fixtures. Unaccepted incomplete proof traces are omitted from Git with exact size/hash records; reproducible CNFs have hash-checked recipes. The new SAT-only runner never accepts UNSAT as exhaustion, and accepts SAT only after complete pinned model, truth-table, gate-count and provenance checks. Lean acceptance is still required.

All four final live/rootOR SAT-only searches ended UNKNOWN at their600-second limits, with noSAT indication; complete outcomes are in completed-wave10. No final search worker is running. Do not reuse an old lease or infer a proof from a search limit. Only the main orchestrator renews/releases its own lease and performs repository writes. A finished proof PR must contain exactly the single permitted Lean file, with research artifacts remaining in branch history.

Sub-agents: 6 inherited-model agents used for distinct proof, construction, search and independent-review strategies.
