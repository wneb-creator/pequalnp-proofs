# Checked conditional contradictions for two reduced axis systems

`AxisReducedCertificates.lean` proves two scalar contradictions over the complex numbers. Each theorem retains six explicitly displayed polynomial equations as hypotheses and concludes `False`. The proof uses an exact integer polynomial combination: 183 multiplier terms in the equal branch and 250 in the different branch. These are standalone algebraic lemmas; geometric chart coverage and the rational substitution chain are not asserted by the Lean theorems.

Source: **44,023 bytes, 35 lines**, SHA256 `8eeef2cb88b2869c59b72329d5b896b37f818f64b6e41c95d7ae4c10769c39cc`.

`AxisReducedAudit.lean` is exactly the source followed by two axiom-print commands. The complete driver compiled successfully in **45.37547578900194 seconds**, sampled peak RSS **3,269,860 KiB**, under the serial 90-second / 4,096-MiB sampled monitor. Both theorems report only `propext`, `Classical.choice`, and `Quot.sound`. Full stdout/stderr and run metadata are included.

An independent reviewer parsed the actual Lean hypotheses and polynomial expressions, verified every emitted multiplier against the exact rational certificates, and multiplied both identities independently. It also checked each normalized generator against the respective four-variable source export and sparse input. Two unused generator rows have zero multipliers and are omitted from each Lean hypothesis list.

The original exact QQ unit traces are preserved and were replayed without trusting the CAS basis claim. Smaller multiplier identities were obtained by solving rational linear systems on known supports modulo `u^2-2`, then restoring an explicit multiplier of that relation. Every final identity was checked in the ordinary rational polynomial ring. The large superseded multiplier and linear-system intermediates remain in scratch; their hashes and sizes are recorded, while all complete process stdout/stderr, final exact certificates, inputs, source exports, and scripts are included here.

`AXIS-DERIVATION.md` records the proposed link from the reviewed triangle chart through the x-axis center-kernel stratum, an invertible shift, two legitimate linear eliminations, and a two-case factorization. Every denominator condition is stated. This entire geometric bridge has **not** been formalized in Lean or independently reviewed as a complete coverage proof; the scripts provide algebraic provenance, not a full-gap verdict.

The source and proof artifacts are frozen. Independent final driver/archive review is recorded separately so the manifest remains stable.
