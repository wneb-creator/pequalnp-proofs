# Independent corrected-coordinate and zero-factor review

The corrected scaled formulas pass independent verification by Ryser's permanent formula applied to the actual symmetric matrix supported on the cycle edges. The source uses the inverse maps

```text
p=(e+f)/2, q=(e-f)/2, A=h-e,
u=(U+V)/2, v=(U-V)/2, r=R-U, s=T+V,
U=(a+b)/2, V=(b-a)/2, h=H/2,
R=X/2+(a+b)/4, T=Y/2-(b-a)/4.
```

Here the original matrix has diagonal entries `(A+u)/2`, `(-2(p+q)-A+v)/2`, `(A-u)/2`, `(-2(p+q)-A-v)/2` and cycle edges `01=(p+r)/2`, `23=(p-r)/2`, `12=(q+s)/2`, `03=(q-s)/2`. Its other two edges vanish. The resulting seven-coordinate linear map is invertible; the checked seven-entry Jacobian has determinant `1/1024`. The total entry sum is zero.

Writing the homogeneous permanent coefficients as `Q,C`, exact Ryser expansion verifies the corrected formulas

```text
4Q = 6e^2+2f^2+a^2+b^2-H^2-X^2-Y^2-X(a+b)+Y(b-a),
16C = 2fab-2HXY
    + e[-4X^2-4Y^2+4X(a+b)+4Y(a-b)-a^2-b^2+4f^2]
    - 4e^3.
```

The output matches the corrected JSON coefficient by coefficient. The earlier uncorrected formula is not used.

On `e=0`, the cubic equation becomes `fab=HXY`. If this product is identically zero on a linear space, the polynomial ring of that space is a domain, so one of `f,a,b` and one of `H,X,Y` must vanish identically. For each of these nine choices the remaining four-coordinate restriction of `4Q` is nondegenerate. Its Gram determinants are:

| Zero coordinate | H=0 | X=0 | Y=0 |
|---|---:|---:|---:|
| f=0 | 9/4 | 3/2 | 3/2 |
| a=0 | 3 | 5/2 | 5/2 |
| b=0 | 3 | 5/2 | 5/2 |

Each has rank four, hence maximal isotropic dimension two over the complex numbers. This completely excludes a three-plane lying in `e=0` in the zero-product branch. It also supplies the nondegeneracy needed to normalize extensions of two-planes in those branches. The separate nonzero-product branch is handled by the parent agent's scaled-permutation argument.

Source, full log, and all nine Gram matrices:

- `/tmp/oec/pequalnp-pilot-75/gct231/c4_factor_coordinates_review.py`
- `/tmp/oec/pequalnp-pilot-75/gct231/c4_factor_coordinates_review.log`
- `/tmp/oec/pequalnp-pilot-75/gct231/c4-factor-zero-branch-review.json`

The exact run completed with exit zero at 2026-11-25 11:04:51 UTC. No Groebner computation or Lean build is used.

## The representative two-plane branch e=f=H=0 cannot extend

Let `K` be a two-dimensional isotropic space in the four-coordinate space `W=(a,b,X,Y)`, and suppose a proposed three-plane extends it by a vector with `e=1`. Since `Q` splits orthogonally between `W` and `(e,f,H)`, the `W` component of the extension is orthogonal to `K`. Maximal isotropy gives `K` equal to its orthogonal complement within `W`. Subtracting that component therefore normalizes the extension vector to

```text
w=(e=1,f=F,H=J,a=b=X=Y=0).
```

The equations `Q(w)=C(w)=0` give `F^2=1` and `J^2=8`. The mixed cubic coefficient requires `K` to be isotropic for the second quadratic form

```text
R = 2Fab-2JXY-4X^2-4Y^2+4X(a+b)+4Y(a-b)-a^2-b^2.
```

Let `G` be the Gram matrix of `4Q` on `W`, and `B` the Gram matrix of `R`. For every one of the four choices of `F,J`, exact symbolic calculation gives

```text
det(B-lambda*G) = lambda^2(9lambda^2+12lambda+16)/4.
```

This polynomial is not a square over the complex numbers: the residual quadratic has nonzero constant term and discriminant `-432`, hence two distinct roots. But if two symmetric forms on a four-space share a two-dimensional isotropic subspace, a basis beginning with that subspace gives their matrix pencil the block form `[[0,D],[D^t,E]]`. Its determinant is `det(D)^2`. A change of basis multiplies the determinant by a nonzero square constant, preserving this necessary condition. This contradiction excludes the extension using only quadratic and cubic equations.

The representative check is saved separately as `/tmp/oec/pequalnp-pilot-75/gct231/c4_fH_zero_extension_review.py` and `.log`. It verifies the general block determinant identity as well as the explicit determinant and discriminant. Its conclusion is only this branch, not all cycle-supported three-planes. None of these results is claimed to be Lean formalized.
