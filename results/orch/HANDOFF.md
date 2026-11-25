# Pilot 81 research handoff

Snapshot: 2026-11-25 14:23 UTC; archival checkpoint `073a3a7fb0d15108a6ddea68a420da9d5bb2f850`.

This is an archival research branch, not a completed proof submission. The assigned step is
L-meta-1479; its negated twin is L-meta-1480. The exact posted statement is in
`statement.txt`. It asks for a normalized monotone circuit of at most 27 gates for Fano incidence,
with one incident pair quiet in both specified Boolean product-rule traces.

The named file `lean/PEqualNP/Outside/L_meta_1479.lean` has 1301 lines and builds.
The local checker rejects it with `no-theorem`: the final target theorem is absent.
It contains a checked 28-gate quiet witness and a 27-gate ordinary baseline, plus
normalization and trace lemmas. Neither is a solution of the posted step.

Use `CASE_LEDGER.md` for the current canonical cases and `validation.txt` for actual
build/checker outcomes. Later checkpoint paragraphs supersede earlier pending states.
`TIMELINE.md` records progress; each frozen package has a hash manifest, complete
diagnostics, and an independent review. Files named `cache` may use temporary compiled
modules; files named `standalone` use permitted imports. An active or failed build is
never a successful standalone result merely because its components compiled.

## Labels and strongest components

The accepted lower-bound proof uses point labels 0 through 6 and line labels 7 through
13. Its line `7+t` corresponds to posted cyclic line `-t`. Do not silently identify the
two line orderings. The accepted source of L-meta-6659 supplied the DAG, support-flow,
reserved-unit, restriction, and cofactor framework; attribution is retained in the
component archives.

- Canonical p7 and p8 have complete no-double-quiet components.
- Canonical p9 with ineligible set `{0,1,2,3,4}` is ordinarily impossible.
- Canonical p9 with ineligible set `{0,1,2,5,11}` is ordinarily impossible in the
  complete cached composition. Both one- and two-missing-mask cases are covered,
  with no finite-certificate hypothesis left. Its full and pruned standalone checks
  are tracked separately; consult their final exit receipts when available.
- Canonical p10 with ineligible set `{0,1,2,5}` is ordinarily impossible.
- For p10 with ineligible set `{0,1,2,3}`, Bplus is at least 13. The missing-mask
  subcase `{2,4,5,6}` with Bplus at most 13 is excluded by the complete cached q2
  composition. Its finite certificate, family transfer, and analytic residual
  obstruction are separately checked. The Bplus=14 case remains open.
- Most other high cases have Bzero bounds, not no-quiet theorems. In particular,
  Bzero=0 alone does not establish a refutation.

The preferred posted-statement bridge is the trace-preserving trim/delete version,
not the larger bridge depending on ordinary minimality. Its structural no-quiet
premise remains explicit. Do not turn this conditional bridge into a claimed result.

## Useful recent lemmas

The empty-opposite and two-exit support lemmas, nonedge first-filter theorem, and
consumer-chain cut have explicit hypotheses recorded in their source statements.
The consumer-chain cut no longer needs an ordering premise on the second consumer.
The C6-plus-three-private-leaves obstruction concerns a separate 9-input graph with
at most 11 gates and all three point labels eligible. A global restriction/deletion
bridge to that graph has not been proved.

Several source-pruning attempts deliberately preserve their failed first versions.
Dependency pruning left orphan documentation comments before `end` or `section`;
these were parser errors, not proof failures. Corrected q2 source has 8014 lines and
450772 bytes. The original combined q2 run also exceeded its -M6000 memory allowance;
its complete exit-134 diagnostics are retained. Check the corrected full-build receipt.

## Pitfalls already found

- Singleton support `{i}` does not mean that a wire computes the literal input `i`.
  It can compute `i OR H` with H false on every singleton.
- Even agreement with `i` on every maximal negative assignment, together with H
  independent of i, does not imply H is a subfunction of Fano incidence. The explicit
  counterexample uses `i=0` and H the conjunction of points 2, 3, and 4.
- Therefore setting ineligible inputs to zero does not automatically delete their
  assigned stars, and support-mask counts do not justify a protected-star deletion.
- An additional protected K4 input does not raise the sharp supported lower bound
  from 8 to 9. Explicit ordinary K4 examples refute that shortcut.
- The p10 finite necessary-condition search has 49 residual survivors in 12 symmetry
  classes. They are abstract models, not circuit witnesses; no contradiction follows.
- Solver timeouts are UNKNOWN. Finite controls validate encodings, not the target.
  The new cross-support and positive-redundancy cuts are disabled on the 28-gate Fano
  control; its incomparability and shared-slot checks remain enabled.

## Delivery constraints

All archival results are preserved on `pnp/pilot-81` at the fork. A final proof PR must
have exactly one permitted Lean file in its net diff; this branch currently contains
research archives and an unfinished target file. Do not open a proof PR from this tip.
The local checker must accept the exact posted statement or its negated twin before
claiming a proof/refutation. The latest public refresh found all three reduction slots
occupied. Never request, renew, or release a different pilot's lease.
