# C4-stable support diagnostic using only quadratic and cubic coefficients

There is no three-dimensional space stable under the cycle `(0123)`, contained in the symmetric tangent support `T02=T13=0`, on which both the quadratic and cubic coefficients of `per(J+hT)` vanish. No quartic equations are used. This is a symmetry diagnostic; it does not exclude arbitrary three-planes satisfying those two homogeneous equations.

Use the character matrices from `fresh/c4_characters.py`. On this support the fixed tangent character is one-dimensional, with quadratic form `24a^2`, so it contributes no nonzero isotropic vector. The minus character has parameters `(b,c)` and quadratic form `8b^2-4c^2`; any nonzero isotropic line therefore has the normalization `b=1`, `c^2=2`. Call its matrix `N(c)`.

The `+i` and `-i` characters have matrices `U(u,v)` and `V(r,t)`:

```text
N(c) = [[-c,1,0,-1], [1,c,-1,0], [0,-1,-c,1], [-1,0,1,c]],

U(u,v) = [[iv,-u,0,iu], [-u,-v,-iu,0],
          [0,-iu,-iv,u], [iu,0,u,v]],

V(r,t) = [[-it,-r,0,-ir], [-r,-t,ir,0],
          [0,ir,it,r], [-ir,0,r,t]].
```

The quadratic coefficient pairs these two character spaces nondegenerately. Its mixed coefficient, after division by `-8`, is

```text
2ru + (2-2i)rv + (2+2i)tu + tv.
```

Its `2 x 2` pairing matrix has determinant `-6`. Thus two dimensions from one of these characters forbid a nonzero component of the other. A plane consisting of two dimensions from one character plus the minus line is also impossible: the corresponding cubic coefficient below is a nonzero quadratic on that entire two-space. Consequently any candidate stable three-plane must have one dimension in each of the minus, `+i`, and `-i` characters.

For `T=xN+yU+zV`, the only possibly nonzero coefficients below degree four, apart from `(8-4c^2)x^2`, are the mixed quadratic above and the cubic terms `4i f xy^2` and `-4i g xz^2`, where

```text
f = 2cu^2 + (2-2i)cuv - (ic+2)v^2,
g = 2cr^2 + (2+2i)crt + (ic-2)t^2.
```

For a nonzero `(u,v)`, quadratic orthogonality uniquely determines the opposite character line:

```text
(r,t) = ((2+2i)u+v, -2u-(2-2i)v),
```

up to nonzero scaling. The displayed vector cannot vanish because the pairing is nondegenerate. Since `c^2=2`, the equation `f=0` rules out `v=0`; normalize `v=1`. Substitute this orthogonal vector in `g` to obtain `h(u,1,c)`. Exact elimination gives

```text
Res_u(f(u,1,c), h(u,1,c))
    = 256(c^2-3c+1)(c^2+3c+1)
    = -2304 modulo (c^2-2).
```

This is nonzero, so the two cubic equations cannot hold simultaneously. As a separate redundant check, all four projective coordinate charts for each of `c=+sqrt(2)` and `c=-sqrt(2)` produce Groebner basis `[1]` over `Q(i,sqrt(2))`.

The independent source uses Ryser's permanent formula to derive all displayed coefficients. Reproducer and full log:

- `/tmp/oec/pequalnp-pilot-75/gct231/fresh/cubic_geometry/c4_cubic_only.py`
- `/tmp/oec/pequalnp-pilot-75/gct231/fresh/cubic_geometry/c4_cubic_only.log`

Command, from `/workspace/pequalnp-proofs`:

```text
python /tmp/oec/pequalnp-pilot-75/gct231/fresh/cubic_geometry/c4_cubic_only.py > /tmp/oec/pequalnp-pilot-75/gct231/fresh/cubic_geometry/c4_cubic_only.log 2>&1
```

An initial reviewer-only structural-expression comparison failure, corrected to test the expanded difference, is preserved in `c4_cubic_only-attempt01.log`. The successful final run performs only exact small polynomial calculations. This result has not been formalized in Lean.
