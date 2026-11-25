# Independent exact trace/certificate review

Reviewer: global_normal_form, 2026-11-25 UTC.

Verdict: PASS for the frozen exact QQ certificate pipeline and its checked
restricted-chart certificates. This is not a Lean build verdict and does not
establish the full L-gct-231 statement or its negation.

## Independent arithmetic checks

`verify_certificate.py` was written independently and imports none of the
author's replay implementation. It parses the actual QQ input, checks each
generator root, enforces earlier-parent acyclic dependencies, independently
adds every shifted rational polynomial parent, compares every resulting
polynomial, and checks the exact final nonzero constant and ancestor closure.

All four toy certificates passed, including the nonunit and rational controls.
All 125 rowzero certificate steps passed (11 roots and 114 consequences).
The sliced star-support certificate passed: 26 roots and 698 consequences,
with 2,893,038 exact rational monomial contributions. Its final step 1531 is a
nonzero constant. The 724-step slice is exactly the full certificate's complete
ancestor subset, with identical metadata and polynomial bodies.

`verify_chart.py` independently recomputed the permanent by subset dynamic
programming, without the author's permutation-expansion loop. It exactly
recovered all 31 star-support coefficient equations and checked that the QQ
input consists of their nonzero rational primitive rescalings. The matrix is
symmetric, has total entry sum zero, has free first-row off-diagonal coordinates
x,y,z, and has its other three off-diagonal entries zero. This is a restricted
support chart, not a general 18-variable chart.

Complete arithmetic diagnostics: `certificate-review-v2.log`,
`chart-review.log`, and `slice-review.log`. The initial reviewer parser failure
in `certificate-review.log` was its handling of implicit toy coefficients;
the corrected reviewer was rerun on every requested artifact.

## Code review

The trace hooks record exact rational row scalings and additions and publish
matrix input/output polynomials. Input rows must be scalar monomial multiples
of a previously established polynomial. The replay's normalized shape and
minimum-exponent matching correctly implement that condition. Every published
output is reconstructed exactly; thus partial-row arithmetic optimizations,
unrecorded operations, or mistaken constant-output assumptions cannot silently
establish an unsupported output identity in the checked artifacts.

The certificate DAG provides a proof independent of OpenF4's correctness as a
Groebner-basis algorithm. Duplicate polynomial registration and polynomial
rescaling do not introduce new assumptions. Zero or malformed rows cause the
verifier to reject rather than produce a proof.

The GMP QQ adapter uses exact rational arithmetic. Its input parsing was
checked against the explicit source polynomials by the independent certificate
verifier. Batching changes only the number of selected critical pairs and is
not trusted in the certificate argument.

The Lean emitter groups only previously proved consequences, emits explicit
complex rational coefficients, uses `linear_combination`, and concludes from
a nonzero complex constant with `norm_num`. Its hypotheses are precisely the
used generator equations; it does not emit the full geometric gap statement.
Regeneration reproduced `F4TraceRowzero.lean` byte for byte (71,633 bytes,
SHA256 83e92fab3fbcd7e2d8f6911457652926b97fa2102e209fec0b2e87ae61780483).
This explicit-complex version has not yet been Lean checked; earlier failed
build logs must remain failures until a new successful build is recorded.

The runner captures complete output, enforces time/address-space limits, and
records timeout or nonzero exit without a mathematical verdict. Its COMPLETED
status indicates process success only; certificate replay and Lean checking
are separate checks. No successful full-chart run is claimed.

No source changes were made to the reviewed pipeline, named Lean file, or CAS
engine. Reviewer scripts, regenerated output, complete logs, and manifests
remain in this directory.

## Frozen pipeline hashes

- make_trace_overlay.py: d1ecd59f4f4434517d0b7d7538953584fc09a298a411a765d0b6c38efea3bf7c
- openf4_qq_trace.cpp: 630d05cea7a3f97ec95d0caeee1a348d2d9bb92b7f27ac3e3c374276105ed8d1
- replay_f4_trace.py: e5d934b777ad6b3fb87beff1a314a5b4c546f1448cbe89db112f60dd8a5c470b
- emit_f4_trace_lean.py: ef91d537d6b3299c0cc427a15e25aaff39e26f022718dda6b595219b96bd3015
- run_f4_trace.py: 1050359d226c2c2861edf7300f8485bb7f521874e2b626385cd198d9b06a462d
- support trace: 68c17f1cfd5bdd9f41df7264be9ddc109814d5fa9a0fdbdedd19508ac7b528e4
- support sliced certificate: 706caed729beab68b5c1c6924cad31bbc1d0575c76efe5c234ad5079827051f2
- rowzero certificate: 47b95514850d72bd5d53c1e35a0b476d26fbfe192825abb232264cd030b58a7c
