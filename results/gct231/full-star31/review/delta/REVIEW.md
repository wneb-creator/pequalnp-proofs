# FullStar31 split-proof and narrow-import delta review

Reviewer: global_normal_form, 2026-11-25 UTC. Verdict: PASS for source
correspondence and helper-file format. No Lean build was performed here.

Reviewed final candidate `FullStar31Lean.lean`: 983 lines, 105,951 bytes,
SHA256 `4e3efa0b397320b678920ea30e5c1228261ee1d043e99e6134e2d8be60a9e6a3`.
The manifest SHA256 is
`a91063c68ff7cae5491bc57ac2520519a2a2f96e5bd0d9b241fe86403edface8`.

The previously reviewed source at SHA256
`1d9ce39dfdf8a03b0c818087bd6d243bf209f89840193cf015b9f47cdb55965a`
established the exact JSON equation correspondence, coefficient order,
primitive contents, derivative factorials, and cancellation scales. The new
source preserves that mapping, as checked directly against its actual text:

- The complete generic prefix, including matrix definition, permanent
  expansion, and all derivative helpers, is byte-identical after imports.
- Each of the 31 added `certEq` statements equals its original conjunct,
  with the same complex parameters and sole permanent-identity hypothesis.
- Each helper proof equals its original conjunction branch modulo whitespace.
  No coefficient, derivative operator, cancellation scale, or premise changed.
- The final theorem's parameters, hypothesis, and entire 31-part conclusion
  are byte-identical to the original statement.
- The final proof applies exactly those 31 helpers in the original order,
  with all parameters and h unchanged; no omitted or repeated helper occurs.

The only added declarations are those 31 helpers. Eight specific Mathlib
imports replace the umbrella imports; no project definitions are used. All
options are scoped `maxHeartbeats` limits (one million for generic formulas,
four million for coefficient helpers and the final wrapper). Namespace and
format checks find no sorry, new axiom, native_decide, root marker, strings,
attributes, or executable commands.

This remains a necessary-equation bridge, not a proof that the full-star
system is inconsistent and not a proof of the posted gap. Compilation status
belongs to the library worker's separately monitored build; this review does
not convert earlier resource-limited builds into successes.

`check.py` independently compares the frozen texts and declaration set.
`check.log` preserves its complete output. No reviewed file was modified.
