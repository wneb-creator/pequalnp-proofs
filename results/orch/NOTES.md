# L-meta-2592 orchestration notes

Gap: Petersen graph edge function, fan-in two, size ≤19, at least one NOT. Imports: PEqualNP.Defs plus Mathlib only.

Exact statement and desk response: /tmp/oec/pequalnp-pilot-114/statement.txt and desk-001.json.

Each agent owns a separate section/file in results/orch/lemmas/. Root alone edits final Lean file, handles lease and git. No secrets in notes.

Current upstream base: 1920101f. Read current CONTRIBUTING.md: helpers inside named namespace, final fully qualified theorem last.

Live reductions already 3 (at stated cap); explore useful reductions but do not assume submission available.

## status_review audit 2026-11-25T14:15:37.302145+00:00

See lemmas/audit.md. No immediate semantic counterexample: invalid reads default false; all gates count; NOT second input ignored. Crucial: syntactic NOT may be dead, so pruning needs strict-size alternative. Graph truth table: 76 false, 948 true; alpha=4, tau=6, all ten inputs essential. Three merged reductions confirmed in git (#7606, #9069, #11694), already at desk cap. Full open PR census had no exact 2592/2590/651 mention; gh search returned empty despite merged history, so do not rely on search alone.

- reductions agent: all three live reductions are present on main (_408 legal normalization, _318 last-NOT decomposition, _271 binary floor + few NOTs). No fourth reduction slot. Developing last-NOT decomposition as checked partial component.

- lower_bound: existing reductions exactly match the three live slots. Developing essentiality/output range and effective-fan-in support partials; no full lower20 route yet.

Counterexample agent: ordinary gate semantics confirmed; CEGIS search running for 19 gates/exactly one NOT. See lemmas/search.md.

- 2026-11-25T14:18:14.495659+00:00 not_elimination: located checked binaryFloor L4725 (15+NOT≤size), stronger residual binaryFloor L5236, and9-input deletion boundL8367. Main few-NOT pieces remain open; see lemmas/not-elimination.md.
