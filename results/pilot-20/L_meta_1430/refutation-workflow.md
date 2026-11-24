# L-meta-1430 refutation workflow inspection

Read from the working repository on2026-11-24. No repository files were edited.

The posted1430 statement is exactly the negation of the positive universal
proved by `PEqualNP.Outside.L_meta_1429` at line738. The independent comparison
is saved under `formula-review/independent-statement-comparison.json`.

For a local refutation, keep statement.txt byte-for-byte as posted and make the
new named theorem prove its negation, hence the double negation of the positive
universal. Copy the self-contained1429 helpers into the1430 namespace, retain
only the permitted Mathlib/Defs dependencies, and use the existing positive
proof under a contradiction introduction. Do not import1429 unless the desk
explicitly permits it.

The checker explicitly supports this mode:

    node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_1430.lean /tmp/oec/pequalnp-pilot-20/gap1430/statement.txt refute

Evidence: tools/check-lean.mjs lines4,11,68–70 document and parse check/refute.
The checker reads the recorded statement before compiling and verifies its
negation in refute mode. An ACCEPTED verdict in this mode is a local refutation
verdict, not automatic PR acceptance.

The currently checked-in PR workflows have no refute selector:

* `.github/workflows/advisory.yml` line109 invokes the checker with check.
* `.github/workflows/authoritative.yml` line329 also hardcodes check.
* Authoritative dispatch inputs at lines18–27 are only pr and gap.

Thus the same refutation file is expected to fail the ordinary positive-proof
PR pipeline unless maintainers arrange a refutation-mode check. No workflow
modifications or bypass are proposed. The user explicitly authorizes preserving
and pushing Lean-checked refutations, superseding CONTRIBUTING's prose request
to release false statements without changing the target.
