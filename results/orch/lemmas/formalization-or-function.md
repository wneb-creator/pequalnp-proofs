Disjunction specialization

or_function_or_count specializes false_or_count to the all-false base and every singleton input. Any Strict Dag computing OR of n inputs has at least n-1 OR gates, even if it contains AND gates. minimum_or_function_only_or concludes that a Strict Dag computing OR of n inputs with at most n-1 total gates has only OR gates. The n=0 case is vacuous.

The generic false-base certificate theorem in formalization-or-count.lean is stronger for cofactors: it applies directly to the original Dag at a partial assignment and avoids introducing constants or aliases. This file adds only the literal OR-function corollaries. Full source compiled exit 0; complete logs and SHA256 receipt adjacent.
