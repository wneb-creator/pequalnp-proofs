Exact two-stage elimination of the quadratic and cubic derivative rows
====================================================================

This is a conditional coordinate chart, not a proof of global coverage.
It uses the original parameters from `tracezero_rankdrop/matrix.json`.

Replace the three extension B coordinates by

    (B_W0,B_W1,B_W2) = (R0+tau,R1+tau,-R0-R1+tau).

The extension trace is `3*tau`. The two quadratic derivative rows become

    B * (R0,R1)^t = P * X - 3*(k,l)^t * D,

where `X=(P_W0,P_W1,P_W2)^t`, `D=D_W2`, and

    B = [[2*b0+b2, b0+2*b2],
         [2*b1+b3, b1+2*b3]],
    P = [[p0,p2,p4], [p1,p3,p5]].

Its exact determinant is `det(B)=3*Delta`, with

    Delta = b0*b3-b1*b2.

Therefore, on `Delta != 0`, the first two equations eliminate both R
coordinates using the 2x2 adjugate. No trace coordinate occurs in these
two equations.

Write the three cubic derivative rows, after the same column change, as

    C_P*X + C_B*(R0,R1)^t + c_D*D + c_tau*tau = 0.

Here `C_B` consists of original columns3-minus5 and4-minus5,
`c_tau` is the sum of original columns3,4,5, and `C_P,c_D` are the
original P and D columns. The exact denominator-cleared residual is

    M_P*X + M_D*D + M_tau*tau = 0,

    M_P   = 3*Delta*C_P + C_B*adj(B)*P,
    M_D   = 3*Delta*c_D - 3*C_B*adj(B)*(k,l)^t,
    M_tau = 3*Delta*c_tau.

Thus `Delta != 0` and `det(M_P) != 0` give an explicit elimination of
five of the seven extension coordinates in terms of D and tau.
Alternative three-column pivots in the 3x5 residual cover other parts
of the `Delta != 0` locus. The `Delta = 0` locus requires another
quadratic-row pivot or a separate argument. Even on this chart, setting
`tau=1/3` additionally requires the extension trace to be nonzero.

For an algebraically simpler matrix, also set base `R=P-3D` and extension
`P_W2=R_W2+3D_W2`. The resulting trace-zero 5x6 matrix is saved in
`trace-rankdrop-shifted-pivots.json`. Its six maximal minors were computed
exactly over QQ by sparse determinant dynamic programming and checked
at 20 independent finite-field points. They have 2500 to3022 terms,
all degree8. No small expanded 5x5 pivot or global coverage certificate
was found.
