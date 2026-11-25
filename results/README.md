# pequalnp-pilot-53 preserved work

Assigned gap: **L-meta-3457 remains unproved**. Its lease was released with reason `other` after preserving the results. No proof or reduction PR has been opened. The files below are compiled partial results, with their extra hypotheses or remaining alternatives explicit. They are not a proof of the unrestricted posted statement. The combined [SmallCase theorem](lemmas/SmallCase3457.lean) establishes the requested conclusion for every N <= 3.

Each file is standalone and may repeat declarations from earlier files. Compile them separately; do not import cumulative versions together. Full compiler stdout/stderr and per-file validation notes are in [validation](validation/). SparseCase and CycleSix retain copied custom data/proposition types and require manual format review; they are not automated-PR-ready files. Later combined derivatives that retain these declarations inherit the same format limitation.

| Compiled artifact | Lines | Scope |
|---|---:|---|
| [PrefixUnion3457.lean](lemmas/PrefixUnion3457.lean) | 342 | Union preservation and first dirty AND operands |
| [StarCover3457.lean](lemmas/StarCover3457.lean) | 567 | Clean star-cover construction and incidence specialization |
| [DropUnusedAnd3457.lean](lemmas/DropUnusedAnd3457.lean) | 405 | Iterated deletion of edge-useless ANDs |
| [ForestCase3457.lean](lemmas/ForestCase3457.lean) | 2378 | Full requested conclusion for acyclic incidence graphs |
| [OneAndCase3457.lean](lemmas/OneAndCase3457.lean) | 639 | Full requested conclusion with at most one AND |
| [IncidenceBudget3457.lean](lemmas/IncidenceBudget3457.lean) | 626 | Full conclusion conditional on an explicit cover budget |
| [PairReplacement3457.lean](lemmas/PairReplacement3457.lean) | 765 | Repair of an AND serving exactly one incident edge |
| [JointNormalization3457.lean](lemmas/JointNormalization3457.lean) | 943 | Every remaining dirty AND serves at least two incident edges |
| [LastAnd3457.lean](lemmas/LastAnd3457.lean) | 271 | OR-suffix gate: below output or removable |
| [SparseCase3457.lean](lemmas/SparseCase3457.lean) | 9139 | Full conclusion under explicit girth and hub-separation hypotheses |
| [CycleSix3457.lean](lemmas/CycleSix3457.lean) | 4544 | Full requested conclusion for canonical six-cycle incidence, with an eight-gate lower bound and clean construction |
| [SmallIncidenceClassification3457.lean](lemmas/SmallIncidenceClassification3457.lean) | 203 | C4-free incidence classification: acyclic for N <= 2; acyclic or a relabeled six-cycle for N = 3 |
| [CycleSixPerm3457.lean](lemmas/CycleSixPerm3457.lean) | 4678 | Full requested conclusion for every relabeled six-cycle incidence |
| [SmallCase3457.lean](lemmas/SmallCase3457.lean) | 7308 | Full requested conclusion for every C4-free incidence with N <= 3 |

The initial L-meta-3178 file built successfully (8103 lines, unchanged after the unadopted cleanup attempt). The authoritative feed subsequently withdrew that step because its parent was proved. Its local checker ended with CHECKER FAULT, verifier exit 137 under the container memory limit; no acceptance is claimed. The source and complete diagnostics remain on this branch.

The special L-meta-1035 request was already resolved by checked L-meta-1036, merged PR https://github.com/open-goat/pequalnp-proofs/pull/2095. No new 1035 submission was attempted.

[Search evidence](search3457/README.md) distinguishes SAT witnesses, UNSAT of the explicit generated models, UNKNOWN, and unsuccessful heuristics. These computational experiments are not Lean certificates. [Research notes](search3457/RESEARCH.md) and the [masking argument](orch/masking-obstruction.md) state their scope and verification limits.

Sub-agents: checker_review, counterexample_search, lean_route, lower_bound, reduction_design, global_route (6).

Job started 2026-11-25T00:31:48Z. Desk null responses: 0. Message ID: msg-4e2ffa03417d4c37dcb234be.

Final independent handoff audit: approved. Current-gap checker: not run because the unrestricted proof is incomplete. Complete desk responses and release outcome are preserved; null responses: 0.

TIMING total=115.6 subagents=6
