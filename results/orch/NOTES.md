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
