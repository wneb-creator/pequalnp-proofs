# L-meta-2732 orchestration notes

Lease acquired 2026-11-25T05:27:40Z. Only root renews and submits.

Target: a 26-gate monotone circuit for the Heawood edge function, with the first two gates canonical under function automorphisms. The standard star construction uses 27 gates.

## Strategies

- circuit_search: finite SAT synthesis.
- lower_bound: mathematical obstructions and necessary conditions.
- formalization: Lean construction, prefix normalization, and baseline verification.
- formalization/rename_wires: input permutation lemma.
- constructive: structured and stochastic circuit synthesis.
- sat_review: independent encoding review and stronger search restrictions.
- repo_review: submission rules, reductions, and independent validation.
- root: integration, lease, dependencies, validation, and delivery.

Each strategy records findings in its own file under lemmas/.

## First findings

- Three existing reductions exhaust the allowed slots. The initial complete census found no open PR targeting 2732.
- A 27-gate construction is straightforward; existence of a 26-gate circuit remains unresolved.
- L_meta_1983 proves a 27-gate lower bound for circuits with a single level of AND gates. Its pairCleanBound gives the same bound when all AND gates reject false inputs of weight at most two. A 26-gate witness must therefore have nested ANDs and an intermediate AND that accepts a false singleton or nonedge pair.
- L_meta_3537 proves 65 canonical prefix representatives. R_meta_2732_3 supplies 58 extremal rows and a packed gate encoding. These outside modules are not allowed imports for this step; needed helpers must be proved in the assigned file.
- The independent SAT review confirmed 21 minimal true rows and 37 maximal false rows, and checked the encoding.
- Initial setup downloaded focused dependencies; PEqualNP.Defs subsequently built successfully. Later full-cache preparation is recorded below.
- The local checker loads all Mathlib; full-cache disk capacity remains a concern.

## First strategy review

- The complete symmetry transport/minimization proof is checked and pushed. A raw witness now suffices for the assigned symmetry condition.
- The full local filter-cover geometry is checked. Gate-count accounting across shared intermediate computations remains unresolved; no 27-gate lower bound for arbitrary circuits has been proved.
- The 27-gate baseline is Lean checked; integration is building. No 26-gate witness has been found.
- Fixed-size stochastic search completed 600 seconds without a witness; neutral exact-function rewrites are in progress.
- General SAT is temporarily paused for bounded three-star/four-star subgraph searches. Both three-star searches timed out UNKNOWN; no UNSAT conclusion is justified.
- Next SAT candidates: near-witness phases, incremental counterexample-guided synthesis, and the reviewed at-most-one-dirty-AND subproblem. CPU quota is two cores, so runs must be scheduled rather than all launched together.
- Formalization next prepares the existing packed58-row decoder to verify a found witness cheaply.

The checked witness pipeline is complete: Packed.decode certifies58boundary rows; PackedWitness.raw builds the residual24-gate witness; canonical_prefix with transport_prefix supplies the exact symmetry condition. A26-gate program remains missing. AssemblyTest is a result artifact with a local test import; final proof must inline its dependencies.


## Strategy review, 2026-11-25 07:07 UTC

The unrestricted26-versus27 question remains unresolved. No proof PR has been opened. The assigned file is still a checked partial (518 lines), not the posted theorem. The exact20-gate lower bound is now checked for this edge list. Target-oriented non-domination of the first20 gates is therefore justified for a minimum circuit followed by padding.

The complete one-dirty-slot restriction is checked: after forcing an exceptional non-output AND slot false, any circuit of size at most26 satisfying the stated pair-cleanliness conditions must lose at least3 of the21 indexed edge pairs. A no-liveness bridge supplies the consumer. This uses ambient-graph counting, exact erasure and cleanliness transfer, and the three disjoint perfect matchings. It does not prove the full gap. The remaining theoretical obstacle is joint cover accounting for old clean contributions without charging an OR twice. An auxiliary six-support counterexample rules out a proposed pair-only cover bound; it is not a refutation of this gap.

Completed general, guided, incremental and at-most-one-pair-dirty runs all returned UNKNOWN. Active search1 is shadow-three (06:33:32 to07:18:32); search2 combines third-gate symmetry, shadow-three and prefix20 (06:58:27 to07:43:27). A three-lost-edge encoding for the one-dirty class is undergoing review for a later slot. Prefix domination is not automatically valid inside that restricted class. The bounded cofactor search tried1942 variants and retained27 gates; its result is heuristic.

The pinned full Mathlib cache has now been downloaded and decompressed through official cache plans. Genuine immutable artifacts occupy at most5GiB across two memfd keepers; bytes, mode and mtime are preserved. Independent review and a genuine Lean import smoke passed. No checker, library source or sentinel artifact was changed. Keep both keepers alive while using the cache. Full-cache no-build validation and an official checker rerun are underway; the earlier checker fault was missing cache, and no checker acceptance has been claimed.

## Strategy review 2026-11-25T07:41:16.349040+00:00

The unrestricted26-gate statement remains unresolved. The27-gate baseline and exact20-gate lower bound are checked; neither decides the posted statement. The one-exceptional-AND path/cover construction is capped at08:05UTC: completing it would be a useful restricted result, but no argument currently excludes multiple exceptional AND gates. Overlapping lost-edge sets cannot be added without proof.

A root review corrected the cofactor search budget. A24-gate circuit computing F0 and also A=x1∨x2∨x4 yields the target in26 gates by appending AND(x13,A), then OR with F0. The earlier23+3 route was sufficient but unnecessarily restrictive. The corrected route was independently reviewed and its25→27 smoke checked on all inputs. Its45-minute search began07:38:57UTC. A relaxed co-output W satisfying A≤W≤A∨F0 and bounded-distance repairs of near26 witnesses are the next constructive routes. Both output orders must be allowed for relaxed W.

The environment restart around07:28 killed two searches and the full-cache checker; the checker returned fault exit137, without a verdict. Sources, complete solver logs, and honest interrupted statuses are pushed. Official focused cache recovery then passed a19,053-path audit (no missing files/symlinks) and lake build --no-build +PEqualNP.Defs. Full-cache restoration is deferred until needed; a read-only compressed filesystem is being assessed as a persistent, lower-memory alternative. No checker or source modifications are permitted for storage recovery.

## Strategy review 2026-11-25T08:19:35.377369+00:00

No exact26-gate witness or unrestricted refutation has been found. The capped one-dirty route ended with a checked conditional ForkCover theorem; the exceptional edge-birth budget and multiple-dirty cases remain open. A separate experimental cubic gate-elimination recurrence evaluated141468 cofactors and returned only20, so that route is closed without another formal lemma. The strict single-file witness generator is ready and independently reviewed; its27-gate smoke is explicitly weaker.

Current long searches are F0+A24 (scheduled end08:23:57) and matching-cut14 (scheduled end08:38:03). The six-gate fixed-five-star cone is UNSAT; both120-second ten-gate probes are UNKNOWN. Next: general26 with finalOR plus reviewed fanout constraints, and joint-selector versions of all six ten-gate or seven noncollinear14-gate cut families to share SAT learning across variants. All conclusions remain scoped to their architectures.
