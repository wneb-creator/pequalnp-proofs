Pilot 100 orchestration state

Goal: prove exactly posted L-meta-2592 (Petersen edge function; no fan-in-two circuit of at most19 gates containing a NOT), or find a checked refutation. Full statement and initial lease are in scratch desk-first.json. No full proof or counterexample exists yet. No PR opened.

Only root manages our lease d30cd9f5-2ff3-41d8-b031-e33b731294ac. Other held gaps belong to other pilots. Automatic renewal runs every5minutes; complete answers in scratch desk-log.txt. Never release another lease. Null desk responses:0.

Workspace /workspace/pequalnp-proofs, branch pnp/pilot-100, fork origin only. Base upstream45b7dac0. Latest pushed checkpoint058b63887b0c3a2e12a60e100907ed7e248b4ec2. Earlier checkpoints116eccb7, b6b49a44, d15bbaa3,352612be. All pushes are partial preservation, not accepted proofs.

Lean wrapper /tmp/oec/pequalnp-pilot-100/lean-env.sh. Pinned Lean4.36.0 installed in scratch; actual required Mathlib cache verified with --no-build; never lake update. Defs and checklemma built. Named partial5337lines/302201bytes now lake-builds successfully; full log scratch partial-build-03.txt. Its16+NOT lower bound is also known upstream (L_meta_6581). Official local checker cannot load the complete statement library under available disk: missing Batteries.olean first; fullMathlib unavailable. Compressed FUSE mount denied; attempts stopped. No checker changes or fake artifacts. See checker-limitations.md.

Current mathematical progress:
- Checked generic17 non-NOT lower bound via Floor17Data+Projection+Proof; source refinement removes helper instance. Source Floor17.lean will be concatenated after cleaning duplicate auxiliary definitions/imports. Instance-free Data revalidation running with restriction_review.
- Checked conditional18 binary lower bound for a non-OR first signed operation; Floor18.lean. Therefore signed17 beginsOR.
- ReadCount.lean now checks at least notCount(C) primary inputs have occurrence1 under Strict10, size<=19 and input/internal usage. Root source167lines; read-count-build-07.txt exit0, independent review by reduction_strategy. Latest extension not yet pushed.
- Structural agent has checked actual circuit reader decomposition, essentiality, NOT-later, binary-leaf/partner and related helpers. Some newest sources await preservation/review; do not claim whole theorem from these conditional facts.
- L2590 monotone<=19 exclusion remains OPEN; no full monotone20 bound may be assumed. A monotone<=18 circuit plus a deadNOT refutes our step.
- All three reduction slots for L2592 are occupied. No fourth reduction is permitted.

Search: counterexample_search owns one active signed18/actual19-cost SAT run; full models are verified on1024inputs. Also preparing monotone18 search on15minimal-true+15maximal-false rows (complete by monotonicity). Earlier unseeded and seeded searches ended UNKNOWN; nearest circuit has four false-positive independent triples. No result may be called a counterexample without exact verification and Lean.

All six subagents have been used: status_review, structural_proof, lemma_routes, counterexample_search, reduction_strategy, restriction_review. Helpers and full logs stay under results/orch; a final proof PR must have exactly the one named file in its netdiff. Every new checked component must be independently reviewed and pushed promptly to own branch.

Wall-time start2026-11-25T13:46:17Z. Do not finish before15:16:17Z unless complete proof/counterexample; total task ceiling about6hours. Lease hard limit roughly19:44UTC. Final must state Sub-agents and TIMING and end with gap/pr/checker lines. Acknowledge kit message msg-5c117df1f45d6a72cccf81e5.

## Lease invalidation and preservation
At14:39:57 desk returned HTTP410: no such live lease: it expired or was released. Ask /desk/next again. Discovered14:47; manual beat repeated same error. Full headers/body in validation/desk-error.txt and beat-15-diagnostic.txt. Partial named file (5337lines) lake build passed; full log partial-build-03.txt. New floor17 combined source is compositionally checked, pending unified named build. Floor18 and FloorSecond development modules compiled. These are lower-bound helpers only; posted19gate statement remains unproved.
