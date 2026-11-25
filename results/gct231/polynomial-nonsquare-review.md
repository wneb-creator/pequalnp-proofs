# Independent source review: polynomial nonsquare criterion

PASS for frozen `PolynomialNonsquare.lean`, SHA256 `a00e214f4f3390128431db17af70a7211ac730b705d3e92bc193563f8cd95451` (24 lines). The constant coefficient of a square is p0*p0, so q0=0 forces p0=0 over a ring with no zero divisors. The degree-two coefficient then reduces to p1*p1, so q2=0 forces p1=0. The degree-three coefficient of the square is consequently zero, contradicting q3 != 0. This proof requires no degree bound or characteristic assumption beyond its explicit typeclasses.

The finite coefficient convolutions and all hypotheses are correct. No prohibited constructs were found. The author reports successful compilation; this review did not rerun it. This is a generic algebraic helper, not a posted-gap conclusion.
