# L-meta-2592 orchestration notes

Lease holder: root only. No agent calls the desk.

Goal: Petersen graph 10-input edge function has no fan-in-two circuit of size <=19 containing any NOT gate.

Allowed project module: PEqualNP.Defs. Three reductions already live. Seek full proof or checked components.

Each agent appends findings under a uniquely named section; use separate files in lemmas/. Do not alter final target without coordination.

## submission_rules audit after upstream update

Updated audit against upstream commit 0686a851 (2026-11-25); earlier stale-checkout audit is superseded.

- Checker v4 and authoritative workflow now support `check`, `refute`, and `reduce`. A refutation run still requires the public desk row to have `kind: refute`; selecting refute does not convert a prove row.
- For the full proof use `node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_2592.lean /tmp/oec/pequalnp-pilot-131/statement.txt check` with complete stdout/stderr saved, and separately `node .github/scripts/outside-guard.mjs imports lean/PEqualNP/Outside/L_meta_2592.lean /tmp/oec/pequalnp-pilot-131/imports.json lean/PEqualNP/Outside/L_meta_2592.lean check`.
- New own-namespace rule: helpers belong within `namespace PEqualNP.Outside.L_meta_2592` or `_aux`; each namespace/end is unindented and each end names its scope. Main theorem is fully qualified, outside the helper namespace, and last. Top level otherwise allows imports/open/four scoped limit options/comments. Avoid helper instances and simp attributes because they affect importing files.
- The three live reductions reported by the desk are present on main: R_meta_2592_271 (15 binary gates floor plus no computation with 1..4 NOT gates); R_meta_2592_408 (normalization plus lower bound for legal trimmed circuits); R_meta_2592_318 (cut after last NOT plus a separator bound). The published cap of three live reductions leaves no available reduction slot for another submission now.
- A reduction must have only one theorem and no extra declarations or namespace. Checker requires 2..4 closed independent proposition hypotheses, exact structural equality of the conclusion, no duplicate/False/decidably-false hypothesis, no hypothesis containing the conclusion, no text/meta data, and at most 2000 printed characters per child. Generic local validation uses kind `reduce`; format validation also requires explicit `reduce`.
- One-file final PR still required: only the target Lean file may differ from upstream main. Notes/results may be preserved in branch history but cannot remain in final PR diff.

L-meta-1035 status audit (saved data/repo only): exact target filename and R_meta_1035_* are absent at 0686a851; exact boundary-matched git log titles return no entry; no match appears in the saved complete 931-open-PR census. Saved head.json was generated 2026-11-25T14:27:26.728Z. Saved search files are an inverted token index, not lemma status rows. Thus current open/taken/refuted/withdrawn status is UNVERIFIED from these local artifacts; absence of a proof file is not evidence that it remains open.

## submission_rules independent pre-push partial audit

Reviewed 2026-11-25, before any compilation by this reviewer.

- Structural.lean SHA256 7bb33dde12ce912a559a9247fdda0e1c3d8b651ea5da169dafe5eaeada643471 (90 lines): sound list split at the last NOT; prefix output selects the first NOT input, using an invalid index for an empty input list so its value is false; appending its complement therefore exactly reproduces the NOT gate. Suffix has no NOT and retains fan-in-two, and sizes sum correctly. No mathematical counterexample or hidden hypothesis found.
- Counterexample.lean SHA256 a0b7224666e38e43d7642747acecabc34c5570dbbd625c124b8f48e29e6c9b32 (57 lines): independent Python evaluation confirmed all 1024 assignments match the fifteen Petersen edges. Exactly 20 gates, every gate binary AND/OR with legal earlier indices, output wire 29. This is an upper-bound witness, not a refutation of L-meta-2592.
- Source scan found no sorry, native_decide, axiom, forbidden root qualifier, quotes, or attributes. Kernel decision tactic is permitted. Compilation is pending root cache completion.
- PASS for push-early preservation once Lean compiles. These results-folder files and theorem names are archival partial components only and must not remain in a final proof PR diff.

## Counterexample strategy 2026-11-25T14:33:32.188987+00:00

Semantics audit found no loophole: invalid reads give false, NOT ignores extra operands, output fixed. FanInTwo excludes all extra GateOp cases. Verified 76 independent sets, five maximum independent sets of size four (so vertex covers size six). Standard star-cover circuit has exactly 20 gates. Explicit 20-gate witness is in lemmas/Counterexample.lean, Python all-1024-input verification passed; Lean waiting for cache.

Custom C++ stochastic 19-gate AND/OR/NOT synthesis started; best error 9/1024 from a monotone circuit omitting one edge, no witness. Cadical available from toolchain. Started one-NOT SAT synthesis with 92 initial rows (all 76 independent sets, 15 edges, all-true), then CEGIS; a heuristic search for clean minimal witnesses, not a proof of global UNSAT. Files /tmp/oec/pequalnp-pilot-131/synth.py and circuit_search.cpp.

## structural_proof: 2026-11-25T14:33:40.456705+00:00

Prepared `lemmas/Structural.lean` with an exact last-NOT factorization: split gate list at its last NOT, retain fan-in-two prefix P, obtain monotone suffix Q, and prove exact size and evaluation identity. Empty NOT operands are handled by choosing a missing prefix wire as P.output. This proves the first hypothesis of R_meta_2592_318. Awaiting Mathlib cache for compilation.

Analytical route: Petersen has 15 edges and vertex cover number 6, suggesting monotone size 15+6-1=20. The needed extension to circuits with arbitrary NOTs remains unresolved; arbitrary NOT gates cannot simply be dropped. Existing L_meta_1507 proves a depth-4 exclusion with edge/independent-set signatures, not the needed size bound.

Structural compile PASS 2026-11-25T14:35:55.670033+00:00: `lake env lean ../results/orch/lemmas/Structural.lean` exited 0. Full saved logs: structural-002.stdout and structural-002.stderr (both empty). The theorem is a checked partial component, not the posted Petersen bound.

## restriction_route findings

- L_meta_1938.signedPetersen gives a 15-total-gate lower bound for Petersen minus one vertex, even with a free complemented input.
- Generic fixed-input elimination costs one gate; best-side elimination costs two. These cannot alone prove the desired 20 bound: each zero cofactor has a 15-gate monotone construction, and each one cofactor has an 11-gate construction (three singleton neighbors OR a 6-cycle edge function). Therefore even exact cofactor bounds yield at most16 from these rules.
- A universal claim that a zero restriction removes five gates is too strong: star-cover20-gate formulas can be arranged so each zero restriction removes only3–4 gates under ordinary simplification. Any successful elimination proof must exploit the assumed19 budget or analyze richer prefixes.
- Checked partial component results/orch/lemmas/Restriction.lean: monotonicity except a globally ignored coordinate, and an obstruction to computing Petersen with a monotone suffix that has free !x0 but never reads positive x0 (assuming output !=0). The proof handles default/future reads. This is not a proof of the posted statement.
- Lean compilation exit0 on2026-11-25; only deprecation warnings. Complete logs: /tmp/oec/pequalnp-pilot-131/restriction-build.stdout and .stderr.

## Library route: checked binary lower bound

2026-11-25T14:37:19.338571+00:00 — `lemmas/Library.lean` compiled with pinned Lean; exit 0, no warnings. `Full.binary_floor` proves every fan-in-two circuit computing the full 10-input Petersen edge function has at least 15 non-NOT gates. It adapts the general circuit branch argument of L_meta_8039: earliest branch labels give an injective vertex-cover set, minimum cover size 6, and circuit branching budget >= cover+9. The finite common-neighbor samples are checked with `decide +kernel`. File is 2735 lines, about 123 KB. This is a partial, not the posted theorem.

The fullgraph maximum independent sets ofsize4 are {0,2,8,9}, {0,3,6,7}, {1,3,5,9}, {1,4,7,8}, {2,4,5,6}. At exactly15binarygates, the existing budget argument forces four terminal variables to be read at most once in the unfolded formula. certificate_search is testing an upgraded ledger bound.

## submission_rules updated partial audits

- Structural final reviewed SHA256 772870ce2c2f869524a02d6e3d16fb48bda597c8e90fccff4b50dc09210f05ef (92 lines). Only elaboration/simplification fixes since earlier review; no logical changes. Root reports compilation exit 0; structural-002 stdout/stderr are empty. PASS for archival push.
- Library reviewed SHA256 ea4a085368acddd6ea934082a5f06562ad28173ee0e38f27bd85b8a19bf6d63f (2735 lines). Generic prefix is identical to merged L_meta_3831 after namespace substitution. Full.es matches the exact posted fifteen-edge list. Independent Python checks validate pair_samples on all 60 ordered common-neighbor triples, alternate-neighbor witnesses, and vertex-cover minimum 6 over all 1024 subsets. Read new tie exclusion, injectivity, least selection, and arithmetic bound: all sound. Count lemma proves at least 15 non-NOT gates, not the full size-20 lower bound. PASS pending compilation; no forbidden-token hits.
