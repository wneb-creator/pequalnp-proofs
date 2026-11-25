# Axis-kernel reductions: algebraic provenance and remaining bridge

The final two Lean lemmas are conditional polynomial contradictions only. This document explains how their polynomial systems were obtained. The substitution chain below was checked symbolically by the generating scripts but has not been formalized as a Lean chart-coverage theorem or independently reviewed as a complete geometric argument. It must not be represented as a proof of the full gap.

Start with the independently reviewed twelve-variable triangle system, source SHA256 `03a8aa61b2a83e2918457d922059fb481128cc02b3d1532c2cfcc11677ed0ce7`. Its center-star map is

`M = [[a,b,0],[c,0,d],[0,e,f]]`,

where `(a,b,c,d,e,f) = (o0,o1,o3,o5,o7,o8)`. The previously established isolated-vertex argument is needed to connect this algebraic setup to a candidate subspace.

## Choosing the center kernel to be the x axis

In this stratum `a=c=0`. The center diagonal vanishes on the same isolated x direction, so `d3=-d0-2`; the other isolated diagonal zeros are already built into the twelve-variable system. The pure quadratic coefficient then gives

`h = d0^2 + 2*d0 - 1 = 0`.

The mixed quadratic coefficients solve

`d1 = 2*(d0-1)*(b+1)`,

`d5 = -2*(d0+3)*(d+1)`.

This uses only the inverses justified by `d0*(d0+2)=1`; neither divisor can vanish. Substitution and exact remainder reduction modulo the monic polynomial `h` yield `axis-seven.json`. A unit basis was computed and its entire exact QQ trace replayed, but the direct resulting certificate was too large for the intended Lean artifact.

Shift `u=d0+1`, so `u^2=2`, and place `u` last in the variable order. Drop the three quartic equations; this weakens the necessary system and introduces no assumption. The resulting eleven-row system is `axis-cubic-shift.json` and also has a fully replayed unit trace.

## Two legitimate linear eliminations

The equations inherited from source rows 8 and 12 are linear in `d7` and `d8`. Setting `b=1` in the first yields `4*u-20=0`; setting `d=1` in the second yields `-4*u-20=0`. Each contradicts `u^2=2`. Thus both `b-1` and `d-1` are nonzero.

The exact solved values, using `1/u=u/2`, are

```text
d7 = (-9*b^2*u + 6*b^2 - 4*b*e - 10*b*u + 4*b + 4*e - u - 2)/(4*b - 4)
d8 = ( 9*d^2*u + 6*d^2 - 4*d*f + 10*d*u + 4*d + 4*f + u - 2)/(4*d - 4).
```

`axis_eliminate.py` substitutes these values, clears the displayed nonzero denominators, and reduces exact numerators modulo `u^2-2`. Every denominator and content scaling is recorded in `axis-five.json`. The reduced mixed cubic is exactly

`-(b-d)*(u*b*d + 5*b - 5*d - u) = 0`.

## Two four-variable systems

If `b=d`, substitute that equality. Otherwise the second factor vanishes and gives

`d = (u-5*b)/(u*b-5)`.

The latter denominator cannot vanish: together `u*b=5` and `5*b=u` would imply `u^2=25`, contradicting `u^2=2`. No normalization of a kernel vector and the fixed off-diagonal pivots is performed.

`axis_branches.py` performs both substitutions and exact reductions, giving `axis-four-equal.json` and `axis-four-different.json`, in variables `(e,f,b,u)`. Their exact QQ unit traces were replayed, and flat rational multiplier identities were independently re-expanded.

For compact certificates, multiplier supports were reduced modulo `u^2-2`. The existing reviewed QQ engine solved only the resulting rational linear systems. The extracted proposed solutions were checked by direct polynomial convolution, with an explicit multiplier of `u^2-2` restoring the ordinary polynomial-ring identity. The final identities have 183 and 250 multiplier terms. They are recorded in the two `axis-four-*-quotient-compressed-certificate.json` files and independently checked against the actual emitted Lean source.

The Lean theorems each retain six explicit polynomial equations and conclude `False`. Two unused source rows have zero multipliers and are omitted from the theorem hypotheses. These are sound standalone scalar conclusions; linking a candidate triangle chart through every step above remains a separate obligation.
