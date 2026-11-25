# Partial double-transposition reduction

Scope: complex solution three-planes stable under `(01)(23)`. The entire case remains unresolved. The completed computation excludes the dimension split with a two-dimensional minus eigenspace. This is an exact symbolic observation, not Lean checked.

The plus tangent space has dimension five and the minus space has dimension four. Their permanent quadratics are nondegenerate, so a stable solution three-plane has only two possible dimension splits: plus two/minus one, or plus one/minus two.

Write a minus matrix as

    N = [a, 0, c, d;
         0,-a,-d,-c;
         c,-d, b, 0;
         d,-c, 0,-b].

Its only nonzero homogeneous permanent coefficients are

    H2 = -2(a²+4ac+4ad+b²+4bc-4bd+2c²+2d²),
    H4 = (ab+(c+id)²)(ab+(c-id)²).

The Gram determinant of H2 is 576. Setting `alpha=a+2c+2d`, `beta=b+2c-2d` puts `-H2/2` into `alpha²+beta²-6c²-6d²`. The explicit change

    alpha=X1+Y1, beta=i(X1-Y1),
    c=X2-Y2/6, d=i(X2+Y2/6)

turns it into `4(X1Y1+X2Y2)`. On each of the four maximal-isotropic charts, with either member of each pair chosen as the free coordinate and `Y=(kv,-ku)` for `X=(u,v)`, all coefficients of H4 have exact Groebner basis `[1]` over Q(i). Thus the minus space contains no solution two-plane. Chart coverage follows from the independent-transversal argument in `c2.md`.

The completed exact source and output are:

    /tmp/oec/pequalnp-pilot-75/gct231/fresh/c2double/reductions.py
    /tmp/oec/pequalnp-pilot-75/gct231/fresh/c2double/reductions.log

For the remaining plus two/minus one case, I tried first to exclude any solution two-plane inside the plus space. Let `h0,h1,h2,h3` be the four columns of the unnormalized four-by-four Hadamard matrix. Every plus tangent matrix has the form

    P=A(h0h1ᵀ+h1h0ᵀ)+B h1h1ᵀ+C h2h2ᵀ+D h3h3ᵀ+E(h2h3ᵀ+h3h2ᵀ).

Its quadratic is `16(B²+C²+D²+2E²-6A²)` and its cubic is

    64(A²B-2ACE-2ADE+BCD+BE²).

All permanent coefficients are recorded in `reductions.log`. An explicit hyperbolic decomposition over Q(i) gives four three-parameter charts for isotropic two-planes. The exact cubic/quartic ideal calculation timed out after 45 seconds on each of charts 0 and 1. The run was then stopped, as requested once these chart systems became expensive. No conclusion is drawn from those timeouts. Source and partial log are `c2double/plus_two.py` and `c2double/plus_two.log` in the same scratch directory.

No witness or obstruction for the remaining plus two/minus one case was obtained. In particular, this note does not claim that all double-transposition-stable solution three-planes are excluded.
