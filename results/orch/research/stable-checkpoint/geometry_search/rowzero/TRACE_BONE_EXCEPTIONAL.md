# Exceptional disjoint-support B-rank-one chart

This is an exact algebraic exclusion, not a Lean theorem and not the global
L-gct-231 conclusion. The same-index B-rank-one chart remains open.

The Hadamard variables here are B, D, and R=P−3D. A normalized rank-one
B-projection plane has B_A=(1,tau,−1−tau), B_B=0. If some coordinate has
both B_A and D_B nonzero, it belongs to the same-index chart. Otherwise
sum(B_A)=0 forces B_A to have exactly two nonzero coordinates, while D_B
is supported on its missing coordinate. Permuting and scaling gives

    B_A=(1,0,−1), D_A=(u,0,v), D_B=(0,1,0).

Write R_B=(p1,alpha,p5). Its three permanent coefficient equations imply

    F(alpha)=5alpha²+14alpha+10=0,
    p1*alpha*p5=0,
    p1²+p5²=4(alpha+1)².

Since F(0)=10 and F(−1)=1, alpha and alpha+1 are nonzero. Swapping
Hadamard axes 0 and 2, and negating A to restore B_A, allows p5=0.
An even sign flip of these two axes then allows p1=−2(alpha+1).
These are actual vertex permutations: respectively (1 3) and (0 2)(1 3).
The script independently checks their conjugations by the Hadamard matrix.

The first-variation equations with indices 1,5,10 in the original twelve
coefficient generators force

    R_A0=u*(-5−12alpha/5),
    R_A1=u*(4+16alpha/5),
    R_A2=v*(-alpha−14/5).

Their 3×3 determinant modulo F is 136alpha/25+48/5, whose inverse is
−17alpha/16−11/10. Thus this elimination loses no solution.

Three remaining necessary equations reduce to

    q=A*u²+B*v²+2=0,
    c3=u²−v²+gamma*u²*v=0,
    c2=kappa*u*v=0,

where

    A=15+48alpha/5,
    B=124/25+16alpha/5,
    gamma=16/5+44alpha/25,
    kappa=34/5+24alpha/5.

kappa is invertible modulo F. Therefore u*v=0. In either branch c3 forces
both u and v to vanish, contradicting q=2. The JSON also records an exact
seven-monomial multiplier certificate equal to 4, together with its F
multiplier. It is multiplied out against both the reduced residuals and
the original generators after the forced substitution.

Files:

- `trace_Bone_exceptional_certificate.py`: exact reproducible verifier.
- `trace-Bone-exceptional-certificate.json`: equations, inverses, certificate,
  original-input hash, and normalization coverage.
- `trace-Bone-exceptional-certificate-2.stdout/.stderr`: complete successful
  diagnostic output, with empty stderr.

The first run failed only because SymPy compared an expanded vector to a
factored vector syntactically. Its complete logs remain preserved. The
second run compares their expanded difference and passes every exact check.
