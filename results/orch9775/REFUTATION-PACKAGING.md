# Routing a checked refutation of L-meta-9775

Conclusion: **do not submit the negation under L-meta-9775 or request checker
mode `refute` for that row. The exact opposite row is L-meta-9777, and its
supported checker mode is `check`.** L-meta-9776 is a different, already
checked value row.

This was a read-only routing investigation. No lease was requested, renewed,
released, or modified; no branch, commit, push, PR, comment, or workflow was
created. Only public reads, local guard replay, and local evidence files were
used.

## Public rows and current availability

The public desk snapshot at
<https://data.pequalnp.com/data/desk/gaps.json>, whose `updated_at` field was
`2026-11-25T17:38:58.134Z`, contains:

| Row | Posted statement | File | Posted kind |
|---|---|---|---|
| L-meta-9775 | Existence of a Monotone2 circuit of size at most24 for our exact19-edge graph | `lean/PEqualNP/Outside/L_meta_9775.lean` | Absent, therefore `check` |
| L-meta-9777 | The negation of that exact existence statement | `lean/PEqualNP/Outside/L_meta_9777.lean` | Absent, therefore `check` |

The full strings were compared programmatically:

    statement9777 == "¬ (" + statement9775 + ")"

This comparison passed. Both rows allow `PEqualNP.Defs`. L-meta-9777's theorem
must be named `PEqualNP.Outside.L_meta_9777`, with helpers under its own permitted
namespace. A proof currently written under9775 helper names must be packaged
and rechecked under9777 names before submission.

L-meta-9776 appears in the snapshot's checked list as
`lean/PEqualNP/Outside/V_meta_9776__k6.lean`, SHA256
`d4857caddb85401741ceb5103d63ebab172dceea59b1140e3b447c53d015d614`.
It is not the negative twin.

The live read-only step endpoints reported:

* <https://pequalnp.com/desk/step?gap=L-meta-9775>: `leased`, one holder.
* <https://pequalnp.com/desk/step?gap=L-meta-9776>: `not_open`.
* <https://pequalnp.com/desk/step?gap=L-meta-9777>: `pr_open`, PR18338.

The live endpoint was newer than the downloaded gap row's `pr_open: 0` field.
GitHub independently confirmed [PR18338](https://github.com/open-goat/pequalnp-proofs/pull/18338)
is OPEN and not a draft, adding exactly `L_meta_9777.lean` with7611 lines.
Its public author is `ithurtstom` (Thomas Brovelli (Meyer)), not a `wnebpilot`
login. The exact head is `79345c8812d893da9c305e0d1bec931bb198594a`.
Its observed head was `79345c8812d893da9c305e0d1bec931bb198594a`; the structured
GitHub response listed no status checks at that moment. This investigation
did not inspect or claim correctness of that submitted proof.

## Why current9775 cannot be judged in refutation mode

The current cached9775 lease has `terms.kind = prove`, and its gap row has no
`kind` field. More decisively, the authoritative intake reads the public gap
row and enforces its checker kind independently of any requested kind:

* `.github/scripts/outside-guard.mjs:159–162` assigns `check` when `g.kind` is
  absent or equals `check`. It assigns `refute` only to an explicitly posted
  `g.kind = refute` row. A mismatched requested kind is refused.
* `.github/workflows/authoritative.yml:29` says `refute` is only for a step the
  desk posts as a refutation. Lines151–158 fetch the public row, run this guard,
  and require the resulting kind to equal the workflow's requested kind.
* `.github/scripts/outside-guard.test.mjs:203–208` tests the absent-kind default
  and rejection of `refute` on a `check` row.

The actual downloaded public rows were replayed through the local guard:

| Row | Requested kind | Result |
|---|---|---|
|9775|`check`|Passes gap-routing guard|
|9775|`refute`|REFUSED: the run's kind is refute, and the desk posts gap L-meta-9775 as kind check|
|9777|`check`|Passes gap-routing guard|
|9777|`refute`|REFUSED: the run's kind is refute, and the desk posts gap L-meta-9777 as kind check|

These are routing checks only, not proof checks. `tools/check-lean.mjs` does
support a standalone `refute` mode, but invoking that local mode cannot override
the authoritative desk-row guard. PR title/body text or the existing9775 lease
also cannot override that guard.

## Supported next action after a complete checked proof

The public [join instructions](https://pequalnp.com/join.txt), lines64–69,
document `tools/pnp.sh next --proof-of <step>` for an already checked proof and
explain that counterexamples are sent by proving the negated twin. The script's
lines6–8 describe the finished-proof lease route, including racing another
holder; line266 implements `--proof-of` by adding `gap=<id>&have=proof`.

After the complete negative proof has been checked, the root-owned routing
action is therefore to request **L-meta-9777** through the finished-proof
route, optionally with `--another` while9775 remains held:

    tools/pnp.sh next --another --proof-of L-meta-9777

This command is documented here only and was not executed. The desk currently
reports a pending PR for9777, so the investigation does **not** establish that
a new lease would be granted. `have=proof` explicitly supports another holder;
the local reference does not promise acceptance while a PR is already pending.
Root must inspect the actual response and live state at that time.

If that row is handed out, submit one new `L_meta_9777.lean` file proving its
posted negative statement, in checker mode `check`, with the9777 lease in the
PR body. The existing9775 lease is not evidence of ownership of9777. If9777 is
already checked or withdrawn by then, the intake refuses a second proof file;
the public instructions say not to resend a settled step.

## Preserved evidence

* `refutation-public-evidence.json`: exact public9775/9777 rows, checked9776
  entry, live step responses, source snapshot hashes, and exact-negation test.
* `refutation-routing-guard.json`: four actual routing-guard replay results.
* `refutation-pr-18338.json`: structured GitHub PR metadata observed above.
* Scratch originals are under `/tmp/oec/pequalnp-pilot-103/refutation-*`.

No permission or confirmation from the user is needed for these read-only
findings. Any subsequent lease, git, or submission operations remain with root
under the user's existing authorization and the actual desk response.
