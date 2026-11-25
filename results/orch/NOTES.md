# Pilot 111 shared research notes

Gap: L-meta-2592. Exact statement: /tmp/oec/pequalnp-pilot-111/statement.txt. Only root holds and renews the lease.

Goal: Petersen edge function needs at least 20 fan-in-two gates even if NOT is permitted; assigned subcase requires a NOT gate. 3 reductions already live. Only PEqualNP.Defs project import allowed.

Write independent notes files and communicate findings; do not edit another agent's files. Proof experiments in results/orch/lemmas with unique names. Final file belongs to root.

## Current findings

- Existing L_meta_6581 yields 16 AND/OR gates, so only1–3 NOT gates remain for a size19 candidate. CombinatorialStrong transplant compiling.
- New retention witness shows first binary gate cannot consume either raw input completely. This supports a17binary lower bound; when first gate is AND or a signed difference, two constant roots after restriction may yield18. Pure OR remains harder.
- SAT partial-row models have failed full truth-table validation. No counterexample found. Searches now include maximal independent assignments, output endpoints, and single-NOT cut constraints.
- Certificate bridge and NOT-count transformations compiled. No UNSAT certificate yet; support components do not prove the gap.
- All three reduction slots are occupied. No new reduction may be submitted.

## First replan

The new17binary argument and first-AND/difference18binary argument now compile, with the existing nine-variable floor supplied as an explicit premise. The selfcontained base certificate rebuild is still running. Finish this integration first. Focus searches on17binary gates with at most2 NOTs and a first OR; edge/nonedge symmetry cases are running. P9signed15 search is also active. Stop stochastic search and the complementary-restriction lower-bound route: a checked14binary upper bound disproves the latter. Continue count-bounded SAT proof bridge; no UNSAT certificate exists yet.

## Checked progress

Seventeen.lean now proves the unconditional17+notCount lower bound using the checked nineFloor certificate. Both compilation and independent review passed. This eliminates every size19 Petersen candidate with at least3NOTs. One and two NOT gates remain unresolved. A selfcontained combined copy PetersenPartial.lean is compiling next, with only the allowed Defs import.
