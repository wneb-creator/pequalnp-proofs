# Exact symbolic classification of the reduced C4 case 3 system

This calculation concerns the six explicitly saved necessary equations in A, beta, U, V, sat. It is not a full-gap Lean proof. Independent review recomputed the complete algebraic chain using separate linear-root formulas and Sylvester determinants, checked every allowed denominator and removed factor, and replaced the final small Gröbner-basis checks with direct scalar reasoning.

Saturation gives nonzero A, beta, and detW. The quadratic scale equation also implies nonzero H=beta²+beta−1. Polynomial reduction modulo that scale equation therefore clears only justified denominators. Forward and reverse elimination of U,V, followed by quadratic norms and a univariate gcd, yield the necessary factor `(beta+2)^22*(2*beta-1)^24` up to a nonzero rational scalar. Resultants are used only in the necessary direction; their degree-drop and conjugate-root artifacts are retained until the later scalar checks.

For beta=-2, the scale equation gives A=2 or A=3/32. The first contradicts saturation; the second gives V=0 and U=-86/15, contradicting the quadratic equation. For beta=1/2, the scale equation gives A=3/4 or A=4. The first contradicts saturation. The second forces U=0, V=-12, sat=1/13. This is the already checked rational point whose omitted square condition is nonzero.

Thus the exact symbolic calculation, independently audited, classifies this reduced system to that one point. The high-degree elimination chain has not been converted into a Lean certificate. Two short scalar endpoint lemmas were separately compiled and audited, with narrow-import copies preserved in `case3-scalar-endpoints-narrow/`; they assume only their displayed scalar polynomial equations.

The frozen 20-file `case3-resultant-classification/` archive contains all source, complete logs/statuses, intermediate and final exact data, the original reduced system, and the independent review. Manifest SHA256: `549e060cec4d6f8f734be115342b5a928b44c27110adeabc5d1ed2c5304999aa`.
