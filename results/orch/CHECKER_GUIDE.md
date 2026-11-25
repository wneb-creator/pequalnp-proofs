# Checker guide

Read from upstream commit `8e683929`, 2026-11-25. This is infrastructure guidance, not a proof or a checker result. Sources: CONTRIBUTING.md, tools/check-lean.mjs, lean/CheckLemma.lean, .github/scripts/outside-guard.mjs, and the authoritative workflow. Refresh rules if the upstream base changes.

## Modes and statement ownership

- `check`: L_ file; its named theorem proves the posted statement.
- `refute`: L_ file; its named theorem proves the negation of the posted statement. The desk row must itself have `kind: refute`. A locally accepted negation of a check-kind gap is not sufficient for public intake; use the posted refutation twin.
- `reduce`: R_<gap>_<k>.lean, k from 1 through 999 without leading zero; explicit kind is required. The desk row must have `reductions: true` and be posted as a check-kind gap. The desk's live-reduction limits still apply.

The current checker supports all three modes. Its comment that reductions ship dark does not disable the mode; the public desk field gates acceptance. Advisory runs do not handle R_ files, so a reduction needs the authoritative reduce run.

The statement file contains the original posted statement in every mode. Do not negate statement.txt for refute or add the reduction hypotheses to it.

## File structure

For a proof/refutation module M, helper declarations belong in `namespace M` ... `end M`, or M_aux or a namespace below either. Scope lines begin at column zero and ends name their scope. Close helpers before the final `theorem M : ... := by ...`, fully qualified and at top level. Nothing but that theorem's proof follows it.

Outside the helper namespace, the permitted lines are top imports, comments, open lines, the four limit options, and the final theorem. Even private helpers at top level fail. Avoid helper instances and simp attributes because they affect importing modules. The raw-text guard rejects forbidden names even in comments, including _root_, quotes, native_decide, bv_decide and compiler/metaprogramming forms. Options must be allowed limits, scoped with `in` to the following declaration.

A reduction has no helper declarations or namespace: just permitted imports and one fully qualified theorem, with 2-4 independent propositional hypotheses followed by the exact parent conclusion. Children must use only pinned-library/definition-root constants, have no free variables, be distinct, not False, not the parent or contain it, not decidably false, contain no text/meta types, and print to at most 2000 characters each. The checker compares the conclusion structurally, not merely by definitional equality. It checks printed children round-trip to the same expressions. Avoid decompositions that simply restate the original difficulty.

## Local validation commands

Run from `/workspace/pequalnp-proofs`; the variables below stand for values already validated against the current desk response. Keep logs under `/tmp/oec/pequalnp-pilot-74/`. Renew the live lease before long builds/checks. Do not run these without an owned live lease. Never run lake update.

First obtain the prebuilt cache in lean/ with `lake exe cache get`; never compile Mathlib from source. The checker specifically requires Mathlib.olean. Its lakefile.toml, lake-manifest.json and lean-toolchain must match committed HEAD; no lakefile.lean may coexist.

After creating an existing scratch output directory PNP_CHECK_DIR, use the current public gaps feed (object containing its gaps array), not the single-row GAP.json, to validate the desk assignment and emit exact statement/import files:

```bash
node .github/scripts/outside-guard.mjs gap "$PNP_GAPS_JSON" "$PNP_GAP" "$PNP_FILE" "$PNP_CHECK_DIR" "$PNP_KIND" > "$PNP_CHECK_DIR/gap.stdout" 2> "$PNP_CHECK_DIR/gap.stderr"
node .github/scripts/outside-guard.mjs imports "$PNP_FILE" "$PNP_CHECK_DIR/imports.json" "$PNP_FILE" "$PNP_KIND" > "$PNP_CHECK_DIR/format.stdout" 2> "$PNP_CHECK_DIR/format.stderr"
```

PNP_FILE is the repo-relative file path, and its repeated occurrence is required by the current CLI. This command checks allowed imports, raw text and helper namespaces together. Inspect both exit statuses before continuing.

Build the named module from lean/ and retain complete stdout/stderr. Then run the checker from the repository root:

```bash
node tools/check-lean.mjs "$PNP_FILE" "$PNP_CHECK_DIR/statement.txt" "$PNP_KIND" > "$PNP_CHECK_DIR/checker.stdout" 2> "$PNP_CHECK_DIR/checker.stderr"
```

Checker exit 0 plus final ACCEPTED is success; exit 1 is REJECTED; exit 3 is CHECKER FAULT and says nothing about the proof. Preserve the full MANIFEST and, for reductions, CHILDREN and CHILD lines. The checker locks builds, rechecks project constants and axioms, and independently elaborates the statement. It does not replace the separate PR/file-format guard. Do not edit judged files while it runs.

## Research checkpoint versus proof PR

A research checkpoint may keep results/orch and logs on the fork. It is not PR-ready. Before the proof PR, commit removal of all checkpoint-only files from the final tree; their earlier commits remain in branch history. Against the verified upstream base, the net PR diff must add exactly one allowed file and nothing else. Using a later deletion commit preserves the checkpoint without requiring force-push.

Run these with PNP_BASE set to the verified upstream base commit:

```bash
git --no-pager status --short --branch
git --no-pager diff --name-status "${PNP_BASE}...HEAD"
git --no-pager diff --raw --no-abbrev "${PNP_BASE}...HEAD"
git --no-pager diff --check "${PNP_BASE}...HEAD"
```

Expect exactly one A entry, the named file, mode 100644, size 1-524288 bytes. Recheck that the file is absent from the current upstream main and the gap remains open. Use an independent diff review before every push as requested by the owner. Stage only named files and inspect git status before committing.

After PR creation, the exact API-shape guard is:

```bash
node .github/scripts/outside-guard.mjs pr "$PNP_PR_JSON" "$PNP_FILES_JSON" "$PNP_TREE_JSON" brilliant-hq/pequalnp-proofs main "$PNP_CHECK_DIR"
```

These inputs are GitHub API pull-request JSON, the complete files array, and recursive tree JSON for its exact head SHA. Validate JSON shape and fully paginate file lists before passing them. Do not substitute gh pr view's differently shaped JSON. The guard checks changed_files=1, added status, base repo/branch, matching blob SHA, mode 100644, size and untruncated tree. A local ACCEPTED result is distinct from the authoritative PR verdict.
