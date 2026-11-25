# Exact obstructions to determinant and Jordan interpretations

This is a scoped structural calculation for the full nine-dimensional tangent space. It neither solves a three-plane chart nor proves nonexistence of the requested three-plane. The checks completed at 2026-11-25 10:37:58 UTC.

Write the tangent matrix as `T = H [[0,b^t],[b,A]] H`, with the normalized Hadamard matrix `H`, symmetric `A`, diagonal coordinates `d1,d2,d3`, off-diagonal coordinates `o1=A23,o2=A13,o3=A12`, and `b1,b2,b3`. Let `Q,C,D` be the coefficients of degrees two, three, and four in `per(J+hT)`. The independent script uses Ryser's subset formula and obtains

```text
Q = d1^2+d2^2+d3^2 + 2(o1^2+o2^2+o3^2) - 6(b1^2+b2^2+b3^2),

C = d1*d2*d3
    + sum_i d_i*(o_i^2+b_i^2-2*sum_{j != i} b_j*o_j)
    + 2*o1*o2*o3 + 6*b1*b2*b3
    + 2*(b1*b2*o3+b1*b3*o2+b2*b3*o1)
    - 2*(b1*o2*o3+b2*o1*o3+b3*o1*o2).
```

## The quadratic is outside the cubic's Hessian span

Every `d_i^2` coefficient of `C` vanishes identically. Thus the `(d_i,d_i)` entry of `Hess C(E)` is zero for every `E`, whereas the Gram matrix of `Q` has that entry equal to one. In particular there is no `E` with `Hess C(E)` equal to a nonzero multiple of the Gram matrix of `Q`.

The exact calculation gives dimension nine for the span of the nine coefficient matrices of `Hess C` and dimension ten after adjoining the Gram matrix of `Q`. The obstruction is invariant under arbitrary invertible linear coordinate changes. It rules out an identification with `(tr(X^2), tr(X^3))` on `Mat_3`, because the Hessian of `tr(X^3)` at the identity is `6 tr(UV)`. It therefore also rules out such an identification by a `Q`-orthogonal transformation.

## The cubic has an ordinary double point of Hessian rank eight

The coordinate point `e_d1` is singular for `C`. On the eight transverse coordinates its quadratic part is

```text
d2*d3 + o1^2+b1^2 - 2*b2*o2 - 2*b3*o3.
```

The Hessian has rank eight, kernel exactly the radial line, and transverse determinant `-64`. Thus this projective singular point is an isolated ordinary double point. This statement does not classify the entire singular locus.

For a generic `3 x 3` determinant, every nonzero singular matrix has rank one: its gradient is the cofactor matrix. Left and right invertible matrix multiplication carry every such point to `diag(1,0,0)` and multiply the determinant by a nonzero scalar. At that representative the quadratic part is `m22*m33-m23*m32`, of Hessian rank four. Consequently `C` is not linearly equivalent to the generic `3 x 3` determinant.

In fact `C` has no homogeneous `3 x 3` linear determinantal representation at all. Its nine-dimensional Hessian span shows that no nonzero constant direction annihilates `C`. If `C(x)=det(M(x))` for a linear map from the nine-dimensional coordinate space to `Mat_3`, a kernel direction of `M` would annihilate `C`. Hence `M` would be injective, thus invertible, contradicting the Hessian-rank obstruction above.

## The quadratic–cubic product is not Jordan

Let `B` be the nondegenerate bilinear form with `Q(x)=B(x,x)`. Define a commutative product by

```text
B(u * v, w) = D^3 C(u,v,w).
```

On the diagonal coordinate span, `e_i*e_i=0` and `e_1*e_2=e_3`, cyclically. Take `x=e_1+e_2` and `y=e_1`. Then

```text
(x*x)*(x*y) = 0,
x*((x*x)*y) = 2*e_3.
```

This explicitly violates the Jordan identity. The violation is preserved by linear coordinate changes and by independent nonzero rescalings of `Q` and `C`. It excludes an interpretation as a Jordan trace quadratic and cubic whose polarized cubic product recovers a scalar multiple of the Jordan product. No broader classification of cubic forms or arbitrary determinant constructions is claimed.

## Reproduction

Source, complete log, and exact homogeneous coefficients are in scratch:

- `/tmp/oec/pequalnp-pilot-75/gct231/fresh/cubic_geometry/invariants.py`
- `/tmp/oec/pequalnp-pilot-75/gct231/fresh/cubic_geometry/invariants.log`
- `/tmp/oec/pequalnp-pilot-75/gct231/fresh/cubic_geometry/homogeneous.json`

Run from `/workspace/pequalnp-proofs`:

```text
python /tmp/oec/pequalnp-pilot-75/gct231/fresh/cubic_geometry/invariants.py > /tmp/oec/pequalnp-pilot-75/gct231/fresh/cubic_geometry/invariants.log 2>&1
```

The command completed with exit zero. It uses exact rational polynomial arithmetic and small matrix computations; no Groebner basis or numerical search is used. These calculations have not been formalized in Lean.
