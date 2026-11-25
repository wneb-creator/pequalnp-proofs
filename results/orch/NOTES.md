# L-meta-2592 orchestration notes

Assigned hard step: Petersen edge function cannot be computed with at most 19 fan-in-two gates when at least one gate is NOT. Allowed project module: PEqualNP.Defs. Reductions are open but 3 are already live. Only the primary manages the lease and git mutations.

Strategy findings will be appended below.

## Independent checker/format review (status_1035, 2026-11-25)

- Local verifier: `node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_2592.lean /tmp/oec/pequalnp-pilot-107/statement.txt check`; use `refute` for the exact negation. It checks the pinned build configuration, rebuilds verifier and target, rechecks project declarations, checks standard axioms, and compares the target statement.
- The separate static guard is necessary: `node .github/scripts/outside-guard.mjs imports <file> <imports.json> <file> check`, with JSON allowed modules `["PEqualNP.Defs"]`. Guard code explicitly excludes `bv_decide` as well as native reduction, strings, forbidden names even in comments, custom syntax, and options except the four scoped limits.
- Helpers belong in `namespace PEqualNP.Outside.L_meta_2592` (or `_aux`), ending with its full name. Only the top-level full-name theorem comes last. Avoid helper instances and global simp lemmas.
- Desk reports three live reductions, and upstream contains R_meta_2592_271, R_meta_2592_318, R_meta_2592_408. No fourth reduction should be submitted while the cap remains full.
- Single-file PR plan: checkpoint partials and results on the required branch as authorized, retaining their commit SHAs. Before final PR, remove only branch-added scratch/results in a cleanup commit. They remain preserved in remote commit history, while the net PR diff adds exactly the one target file. No history rewrite or second branch is needed.
- Statement sanity: the 15-edge formula is the Petersen graph; circuit size counts all gates including ignored/unused NOT gates, invalid wire indices read false, and NOT uses only its first input. FanInTwo restricts operations to AND/OR/NOT and input-list length <= 2. No malformed type or contradictory premise is apparent.

## Semantics (2026-11-25T14:04:02.800566+00:00)

- `Circuit.wires` is a sequential fold; missing/future references read false. `FanInTwo` limits operations to AND/OR/NOT and input-list length to two. NOT ignores its second input. Empty AND/NOT gates evaluate true; empty OR evaluates false. No semantic loophole found.
- Draft `results/orch/lemmas/semantics_normalize.lean`: cap every input/output reference by `n + C.size`. This preserves every intermediate state, gate count, fan-in, NOT occurrence, and final value. All references then lie in a finite range (`0..29` here). Complete proof text; pending Lean availability.

## 2026-11-25T14:05:24.107619+00:00 lower-bound route

The checked branch/twin-class argument gives only 15 non-NOT gates. General monotone conversion for arbitrary graph edge functions cannot be assumed. A useful functional lemma for the last NOT is: if `f(x)=G(x,not h(x))` and `G(x,_)` is monotone, then `h≤f` permits setting the negated input to true; `f≤h` permits setting it to false. This needs no monotonicity of h. Draft Lean is in `results/orch/lemmas/lower_bound_helpers.lean`, not yet compiled while toolchain setup is pending. For one-NOT circuits, an AND of an adjacent pair of Petersen inputs is removable by this criterion.

- 2026-11-25T14:06:00.632466+00:00 [counterexample_search]: installed libz3.so.4 (Z3 4.13.3) is callable through ctypes; no Python bindings or executable. Wrote exact 1024-row truth-table CGP search (19 topological AND/OR/NOT gates) and SMT CEGIS synthesis. First CGP best so far is 10 errors, with its only NOT unused; not a witness. Known checked 20-gate construction at L_meta_1755.lean.

Timestamp: 2026-11-25T14:07:17.621387+00:00

## Existing-results audit

- Public feed meta map confirms L-meta-1035 and L-meta-2592 are conjectures as of head generated 2026-11-25T13:58:57Z. No checked refutation of1035 found.
- R_meta_2592_271: binary-floor child L_meta_4725 is checked (15 + notCount C ≤ C.size); few-NOT child L_meta_4727 remains conjecture. Equivalent binary-only lower bound L_meta_6194 checked.
- R_meta_2592_408: normalization child L_meta_7389 is checked exactly.
- R_meta_2592_318: cut-at-last-NOT child L_meta_8295 is checked exactly.
- R_meta_4727_1 merely splits by has-NOT: child L_meta_8021 checked but contradictory hypotheses (noNOT with positiveNOT); hard child L_meta_8023 remains conjecture. Other cuts R_meta_4727_17 (semantic gate-value compilation+finite lower) and R_meta_4727_53 (signed binary compilation+signed lower) are present.
- Full Petersen-minus-vertex lower bound ≥16 is already checked in L_meta_670 (523341 bytes) and L_meta_4033 (521569 bytes). All14 first-gate-orbit bounds L_meta_1665..1678 also checked. These sources nearly hit the512KiB cap; helper reuse would need compression/deduplication.
- L_meta_7493 gives ≥14 binary/non-NOT gates for Petersen-minus-vertex. L_meta_8039 excludes exactly15 gates and2NOT for that graph.
- Explicit20-gate monotone Petersen construction: L_meta_1755 (29lines). Counterexample agent notified.
- Full final-statement censuses retained in /tmp/oec/pequalnp-pilot-107/existing-fin9-size16-statements.txt and existing-petersen-equality-statements.txt.
