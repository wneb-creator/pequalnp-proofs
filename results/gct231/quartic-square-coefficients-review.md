# Quartic square coefficient identities: source review

The frozen `library/QuarticSquareCoefficients.lean`, SHA256 `24051b7d2e1729780f4d74b6532e792dcca4bbda93fb443a9f6629f6b4f24a35` (43 lines, 1804 bytes), passes independent statement and algebra review. If q=p² and natDegree q≤4 in a commutative ring without zero divisors, the power degree formula gives natDegree p≤2. Writing p=uX²+vX+w yields coefficients a=u², b=2uv, c=v²+2uw, d=2vw and e=w². Substitution gives both identities by ring algebra:

`8a²d−4abc+b³=0` and `(4ac−b²)²−64a³e=0`.

There is no assumption that the leading coefficient is nonzero or that either polynomial has its maximum possible degree. Zero and lower-degree squares are covered. There is also no division or characteristic-zero premise; the stated CommRing and NoZeroDivisors assumptions suffice. The use over C is therefore valid.

The author build `library/quartic-square-coefficients-build01.log` passed unchanged with exit 0 in approximately 3.05 seconds. Its sampled-RSS metadata records peak 2884320 KiB. This independent review did not run another compiler.

Review completed 2026-11-25T11:42:51.872610+00:00.
