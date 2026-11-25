# L-meta-2583 direct structural route

Read1 means that every prime implicant has some proof tree reading each variable at most once. It does not constrain global input fanout. The target incidence minterms are point-line pairs. AO2 permits exactly two earlier operands at each AND/OR gate, so invalid-wire and constant-gate loopholes are unavailable.

The straightforward reduction to a star-cover circuit requires the unrestricted lower bound |E| + N - 1 for a projective plane. The read1 analogue is already checked, as is a read1 star-cover builder. The general C4-free normalization and cover-budget theorem remain open (existing_reductions identified L-meta-4895 and its hard child2872). Thus the missing argument cannot be replaced merely by proving plane regularity.

A clean AND is a product of two monotone functions A and B whose product implies the target F. Every singleton term of A paired with every singleton term of B must be an edge, because both factors are true on their union. Their singleton supports therefore form a rectangle. In a C4-free graph at least one support has cardinality at most one, so these directly accepted pairs form a star.

A pair accepted by the clean AND but not in either orientation of that singleton cross product must be accepted by one operand that rejects both singleton endpoints. This is the nonlinear operand dichotomy in 2583_direct.lean. It identifies the exact case that a read1 normalization must eliminate: an edge has already been combined inside an operand, and the top AND filters it or rereads one endpoint. The star lemma alone gives no size accounting for this case.

Current candidate results/orch/lemmas/2583_direct.lean contains:
- cleanAnd_support_rectangle: semantic singleton supports form a rectangle.
- cleanAnd_support_star: no-four-cycle relation forces one support cardinality at most one.
- incidence_rectangle_star: the posted unique-line hypothesis directly forbids a 2-by-2 point-line rectangle.
- cleanAnd_pair_requires_nonlinear_operand: outside the singleton cross product, one operand accepts the pair and rejects both endpoints.

The generic semantic statements explicitly assume monotonicity, implication to F, and the interpretation of F on pair inputs. They do not claim an arbitrary Circuit is already in top form or a non-increasing circuit transformation.

Prepared UTC: 2026-11-25T14:48:58.339905+00:00

UTC: 2026-11-25T14:49:48.891900+00:00
Source: results/orch/lemmas/2583_direct.lean
SHA256: 6284d8b08eacbdf8fe1534093c807d09bac6c15890e500313442f42d7b58ed43
Lines: 102
Lean exit: 0
Command: PATH=/tmp/oec/pequalnp-pilot-98/toolchain/bin:$PATH PEQUALNP_REAL_LAKE=/tmp/oec/pequalnp-pilot-98/toolchain/bin/lake PEQUALNP_HOME=/tmp/oec/pequalnp-pilot-98/build-home MATHLIB_CACHE_DIR=/tmp/oec/pequalnp-pilot-98/mathlib-cache LAKE_ARTIFACT_CACHE=false ../tools/bin/lake env lean -j 1 -M 2048 /workspace/pequalnp-proofs/results/orch/lemmas/2583_direct.lean
Stdout: empty
Stderr: empty
Scope: singleton rectangle/star semantics and nonlinear operand dichotomy only; no non-increasing Circuit conversion.


## Public search report read 2026-11-25

Read https://github.com/brilliant-hq/pequalnp-proofs/discussions/12644 (GitHub redirected to the same discussion under open-goat). The author reports exhaustive core-cover searches on small C4-free bipartite graphs without a counterexample. The separate PG(2,3) annealer missed one test at63 gates, but also failed at70 gates where witnesses exist. Its own assessment is “local search is not good enough here”. These are reported searches, not a checked lower bound; I did not reproduce them. Their relevance is to avoid mistaking unsuccessful synthesis for the missing star-cover budget argument.

## 2026-11-25T14:52:26.696114+00:00: near-miss artifact audit

Read the full linked public GitHub gist. It contains search programs and graph data but no saved near-miss circuit or failing input. Its annealers print full circuits only on a zero-error result. A one-error 63-gate baseline follows immediately by deleting a leaf OR from the 64-gate star circuit, thereby omitting one edge. Therefore the one-error report is insufficient to identify a nontrivial repair seed. Root, counterexample_search and exact_synthesis were informed. No external code was executed.
