# L-meta-2448 orchestration notes

Root holds the sole lease for this job. Other leases under the same GitHub handle belong to other pilots and must not be touched.

## Goal

For a graph without triangles or four-cycles, prove that a minimum monotone circuit computing its edge function can have a star profile. The exact posted statement is in the task scratch directory, `gap.json` and `statement.txt`.

## Current findings

- L-meta-1035 is already withdrawn. Its opposite L-meta-1036 was accepted in PR 2095, using five inputs and twenty-one outputs.
- L-meta-2448 has three live reductions. No further reduction slot is available.
- Minimum-circuit existence is checked in L_meta_2666 and L_meta_7069. The named file currently contains an adapted helper proof of this part, without a claimed proof of the posted theorem.
- R_meta_2448_263 proves that a gate owning disjoint edges in a four-cycle-free graph fires on a nonedge pair or singleton among their endpoints. Circuit repair is the unresolved part.
- L_meta_8237 and L_meta_8415 study singleton witnesses and downstream blocking AND gates.

## Assignments

- Root: integration, lease renewal, builds, publication, alternate global argument.
- status_review: independent review and mathematical lower-bound route.
- structural_proof: local circuit exchange/repair argument.
- library_route: library search and adapted minimum-existence helper.
- finite_cases: exact small-case search and counterexample investigation.
- lean_setup: install the missing pinned toolchain and fetch the pinned Mathlib cache.

Strategy-specific notes go in separate Markdown files in this directory to avoid concurrent edits. Candidate Lean fragments go in the scratch strategy directories or the lemmas directory. Only root integrates the final named Lean file after coordinating ownership.

## First strategy review

Existing lower bounds and the one-junk proof do not close the target: they rely on a global assignment of residual edges and, in one critical case, on exclusion of a five-cycle. Earliest/latest bad-gate choices do not supply those hypotheses.

Continue four routes: whole common-singleton component extraction; graph-only guard classification with a separate small pentagon case; explicit context-preserving circuit repairs; exact and heuristic circuit synthesis on interacting-cycle graphs. The theorem remains unproved.

## Conditional one-junk result

`lemmas/OneJunk.lean` proves the cover-size bound for a least exact-two AO circuit in TopForm on a triangle/four-cycle-free graph, assuming exactly one junk AND gate and silence on singleton inputs. This removes the old global bipartition premise for that subcase. It imports checked L_meta_3760 as a prototype dependency, so it cannot be copied into the final gap file without extracting the used helper proofs. It does not address multiple interacting junk gates and does not prove the posted theorem.

## Second strategy review

The at-most-one-junk case now gives the desired star-profile existential conditionally, including zero junk and empty graphs. Multiple dirty gates remain unresolved. A concrete two-junk circuit blocks a fixed-prefix replacement within three added gates; this is not a full counterexample because the whole OR prefix can be rebuilt. Free-OR bounded-AND searches and finite total-gate synthesis support small instances but do not prove a global size bound. A fresh independent full-theorem route and allowed-import dependency extraction are underway.
