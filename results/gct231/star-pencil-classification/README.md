# Checked scalar classification of a star-supported pencil

`StarPencilClassification.lean` compiled successfully. Its two theorems prove that seven displayed polynomial equations in complex parameters imply `r = 0`, and then `p = q = r = 0`, `a = b = -1`. Every equation remains an explicit hypothesis. This is a conditional scalar theorem; it does not assert geometric chart coverage or prove the whole gap.

Final source SHA256: `7bdbee0dc04cb54742c6a0e3a60c474cbd5a9bc50dc1df6529bca5899db32603`.

The first theorem is a direct exact polynomial identity with 991 multiplier terms. The rational identity was independently multiplied by a separate reviewer, then cleared by a common integer denominator for Lean. The second theorem uses the remaining elementary polynomial equations and the fact that a square vanishes only when its base vanishes. The original reviewed identity and its integer-cleared Lean expression are both preserved.

Final compile `star-lean-build03`: PASS, exit 0, empty complete log, 52.08170968500053 seconds, sampled peak process-group RSS 4,342,128 KiB. The serial runner used a 180-second wall deadline and a sampled 6,144-MiB RSS ceiling. The monitor samples every half second; it is not a kernel-enforced resident-memory limit. A separate axiom audit is pending and will be archived separately.

Earlier attempts are retained accurately: `build01` stopped at the 4,096-MiB RSS ceiling; `build02` checked the large identity but failed on an unavailable lemma name in the short square-zero corollary. The corrected corollary uses `pow_two` and `mul_eq_zero`. The first source snapshot is retained byte-for-byte as `StarPencilClassification.first-corollary.lean`; only the final source above is reported as compiled.

The mathematical source is the star-supported pencil with off-diagonal entries `x`, `y`, and `a*x+b*y`, leaf diagonal entries `p*x`, `q*y`, and `r*(a*x+b*y)`, and center diagonal fixed by total-entry sum zero. Independent Ryser expansion checked every original coefficient. Under explicit `a != 0`, `b != 0` assumptions, two exact quadratic/cubic identities imply the additional equations Ep and Eq. The exported eight-row system includes one quartic row whose multiplier is zero; the Lean theorem therefore needs only the other seven equations. This theorem does not silently discharge the nonzero assumptions or the geometric reduction.

The existing exact QQ engine produced the scalar classification basis in 0.017 seconds. Every one of its 97 output identities was replayed exactly; the CAS basis claim is not used by the Lean proof. The complete small trace, source equations, normalized input and companion, basis, replayed certificate, flattened identity, emitter, and all stdout/stderr logs are included. No engine binaries or vendor trees are included.

Independent arithmetic review is in `rational-review/`. Geometry and original Lean-expression review sources/logs are also preserved. The original Lean-expression review applies to the byte-identical large identity; the small corollary fix and final artifact review are recorded separately. No cleanup or recompression has replaced this compiled checkpoint.
