# pequalnp-pilot-144 preserved work

No complete proof or refutation has been obtained, and no proof PR has been opened.

The desk first returned L-meta-2583, then freshly assigned L-meta-2590 after the first lease returned HTTP 410. The second lease also returned HTTP 410 before its last reported expiry. All proof work stopped. Three recovery requests returned no lease because the checker queue was backlogged. The next request and the one permitted retry both returned an existing L-meta-4970 lease issued to the shared handle before these requests, with the five-gap holding-limit message. Under the explicit ownership rule, the job stopped without working on, sending a beat for, or releasing that other pilot's lease. No release request was made during this job.

Retrospective ownership caution: the initial L-meta-2583 response also had an older issue time and the five-gap note. It was originally interpreted as an assignment; the resulting checked components are preserved as partial work only. Do not treat that response as evidence that this job owned the earlier lease.

## Checked components for L-meta-2590

| Source | What it proves |
| --- | --- |
| `lemmas/NormalizedLive.lean` | A nonconstant, nonprojection monotone circuit has a no-larger binary AND/OR representative with distinct operands, an internal output, and all other gates read at least once. |
| `lemmas/PetersenSingleRead.lean` | A live binary Petersen circuit of at most 19 gates, with distinct operands and an internal output, has an input read exactly once. Includes the formula lower bound and circuit-unfolding infrastructure. |
| `lemmas/PetersenEssential.lean` | Every input is read by any circuit computing the Petersen edge function. |
| `lemmas/PetersenFormula.lean` | Every positive Petersen formula has at least 21 leaves. |
| `lemmas/UniqueReader.lean` | A single raw input occurrence isolates one reader gate and excludes that input from every other gate. |
| `lemmas/PetersenUpper.lean` | An explicit 20-gate monotone circuit computes the Petersen function on every input. |
| `lemmas/PetersenOrGuard.lean` | Semantic restrictions on an OR helper at the single input. |
| `lemmas/PetersenSymmetry.lean` | A Petersen symmetry exchanges the two exceptional OR-helper supports. |

Complete compilation logs and earlier source versions are under `search/structural2590/` and `search/counterexample2590/`. A zero-byte log accompanies a recorded successful exit; the validation record distinguishes completed and interrupted attempts.

`search/structural2590/Compression.lean` and `lemmas/PetersenRename.lean` are unfinished drafts. Neither is claimed checked. The exact public statement of the compression child L-meta-7889 is in `logs/statement-7889.txt`; no lease was held for that child and no child submission was attempted.

## Earlier L-meta-2583 components

`lemmas/Structural.lean` characterizes incidence prime implicants and read-k pair tests. `lemmas/IncidenceUpper.lean` constructs an exact-size read-1 incidence circuit. `lemmas/MatchingObstruction.lean` checks an obstruction to the proposed normal-form argument. `lemmas/FanoDesign.lean` checks Fano incidence axioms and a 27-gate circuit's shape and size; it does not establish that circuit's full semantics.

## Validation limits

The named partial files built successfully with pinned Lean 4.36.0. The audited Petersen components use only the permitted standard axioms. The repository checker stopped before checking the statement because the full Mathlib cache was unavailable. Storage preparation is documented separately; it is not proof validation.

The named partial files contain helper lemmas, not the final posted theorem. This branch also contains research artifacts, so it is not a single-file proof PR branch. Preserve this history when preparing any eventual clean PR diff.

## Search scope

No counterexample was found. Local UNSAT results concern bounded edits to a particular near-witness; they are not global circuit lower bounds. Earlier Fano local searches required distinct operands. The completed Petersen local searches allowed repeated operands. Broader solver runs were interrupted after lease loss and have no verdict. Full sources, inputs, logs, and status records are retained under `search/`.
