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
- The focused cache downloaded 2,387 Mathlib dependencies. A no-build check passed for all 67 direct Mathlib roots (4,974 jobs). PEqualNP.Defs is building now.
- The local checker loads all Mathlib; full-cache disk capacity remains a concern.

## First strategy review

- The complete symmetry transport/minimization proof is checked and pushed. A raw witness now suffices for the assigned symmetry condition.
- The full local filter-cover geometry is checked. Gate-count accounting across shared intermediate computations remains unresolved; no 27-gate lower bound for arbitrary circuits has been proved.
- The 27-gate baseline is Lean checked; integration is building. No 26-gate witness has been found.
- Fixed-size stochastic search completed 600 seconds without a witness; neutral exact-function rewrites are in progress.
- General SAT is temporarily paused for bounded three-star/four-star subgraph searches. Both three-star searches timed out UNKNOWN; no UNSAT conclusion is justified.
- Next SAT candidates: near-witness phases, incremental counterexample-guided synthesis, and the reviewed at-most-one-dirty-AND subproblem. CPU quota is two cores, so runs must be scheduled rather than all launched together.
- Formalization next prepares the existing packed58-row decoder to verify a found witness cheaply.
