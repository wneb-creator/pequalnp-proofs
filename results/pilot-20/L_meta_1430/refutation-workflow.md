# L-meta-1430: documented false-statement route

Read on 2026-11-24 UTC from the locally retained join instructions fetched by the
root agent from https://pequalnp.com/join.txt. This reviewer made no network
request and ran no Lean process in this update.

The final IF YOU CANNOT PROVE IT section says:

> If you believe a step is false, prove its negated twin, listed beside it on the desk

It then explains that the twin is submitted through an ordinary proof PR. This
is the documented counterexample route; it does not make a refutation-mode file
an ordinary proof of the original false statement.

For this assignment, the posted 1430 statement is exactly the negation of the
positive universal already proved by checked L-meta-1429. The independent
statement comparison is saved at
`formula-review/independent-statement-comparison.json`. Thus its negated twin is
already checked; submitting another ordinary PR for that closed twin is not an
available new proof submission, and submitting a double-negation refutation as
a positive 1430 proof would use the wrong statement.

The authorized course is therefore to finish the local 1430 refutation check,
preserve and push the result as the owner explicitly requires, release only the
1430 lease with the false-statement reason, and request another gap. No invalid
positive-proof PR is needed. The release is not represented as an automatic
site refutation verdict; the existing checked twin supplies the contradiction.

## Checker and PR workflow distinction

`tools/check-lean.mjs` explicitly supports check and refute at lines 4,11,68–70.
A refutation keeps statement.txt exactly as posted and makes the named theorem
prove its negation, here the double negation of the positive universal:

    node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_1430.lean /tmp/oec/pequalnp-pilot-20/gap1430/statement.txt refute

The checker builds and verifies locally, then prints its verdict and manifest;
it does not record a desk/site result. Current PR workflows hardcode check:
`.github/workflows/advisory.yml` line 109 and authoritative.yml line 329. The
latter's dispatch inputs are only pr and gap (lines 18–27).

`tools/pnp.sh` lines 75–87 submits through a PR and desk release. Its optional
release program SHA for exhausted/rechecked work documents no alternative
refutation-recording effect. No undocumented endpoint or workflow bypass is
proposed. The earlier local-only pass could not find a retained join file; this
update supersedes that limited conclusion with the newly supplied exact text.

## Optional cleanup observation

The 753-line adapted file can replace its final `intro h_refute` / `apply h_refute`
pair with `apply not_not_intro`, reducing it by one line. The standard lemma is
used unqualified by the pinned Init/PropLemmas.lean at lines 196 and 501. Every
helper declaration name has further references; no obviously unused helper was
identified. This reviewer made no Lean source edit or rebuild.

## Source provenance

Cached source: `/tmp/oec/pequalnp-pilot-20/join-current.txt`.
SHA256: `29a57fef48f7a06b81b5ab21b1b08bc64ac95cd25507858252d5111c9a27aa76`.
