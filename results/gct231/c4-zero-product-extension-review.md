# Independent exclusion of all nine zero-product extension branches

Verdict: all nine branches pass independent review, with explicit algebraic contradictions that require no Groebner computation. The source replay completed at 2026-11-25 11:09:00 UTC. This covers the zero-product branch of `K=L intersect {e=0}`; it does not exclude the remaining nonzero-product branch.

Use the corrected quadratic `q=4Q` and cubic `c=16C` independently verified in `c4-factor-coordinate-review.md`. Suppose `K` is two-dimensional, lies in `e=0`, and has `fab=HXY=0` identically. Since its polynomial ring is a domain, some coordinate among `f,a,b` and some among `H,X,Y` vanish identically. There are nine choices. The other four coordinates form a space `W` on which `q` is nondegenerate, as independently checked earlier.

If a three-plane extends `K` outside `e=0`, choose an extension vector with `e=1`. Its `W` component, in the orthogonal decomposition by `W`, lies in `K`, because `K` is a maximal isotropic two-space in `W`. Subtracting that component leaves a vector `w` in `W`'s orthogonal complement. Assign the two missing coordinates the free values `u,v`; the remaining coordinates of `w` are then uniquely determined by orthogonality. The review independently checks every recorded normalization and recomputes `q(w)` and `c(w)`.

Let `R` be the coefficient linear in `t` of `c(k+tw)` for `k` in `W`. A valid extension would make `K` isotropic for both `q|W` and `R`. If `G,B` are their Gram matrices, the monic determinant of `B-lambda*G` must be a square: a basis beginning with `K` gives both matrices a zero upper-left `2 x 2` block, and the determinant of the matrix pencil becomes the square of a `2 x 2` determinant. Normalization to a monic polynomial preserves this condition over the complex numbers.

Write that monic quartic as `lambda^4+d3*lambda^3+d2*lambda^2+d1*lambda+d0`. A necessary square condition is

```text
S = 8d1-4d3*d2+d3^3 = 0.
```

The review computes the characteristic polynomial of `G^{-1}B`, independently of the parent's determinant expansion, and matches all nine recorded polynomials and both square conditions exactly. Only `q(w)=c(w)=S=0` are needed below; the second square condition and the original permanent quartic are unused.

The nine cases reduce to four elementary calculations. Nonzero rational rescalings of equations are harmless.

1. **f=H=0.** Set `Q=q(w)`, `C=c(w)/4`, `S0=27S/64`. Direct expansion gives `S0-2Q-9C=-3`.

2. **f=X=0 or f=Y=0.** After replacing `u` by `-u` in the latter case, take

   ```text
   Q=4u^2-3v^2+12,
   C=(u-1)(8u+v^2+8).
   ```

   The third normalized equation, together with `Q`, yields

   ```text
   F=(u-1)(u+3)^2=0,
   R=57u^3-391u^2+723u+571=0.
   ```

   But `R(1)=960` and `R(-3)=-6656`, so the equations are incompatible.

3. **a=H=0 or b=H=0.** After replacing `v` by `-v` in the latter case, eliminating `u^2` gives

   ```text
   F=v^3+14v^2-6v-72,
   R=33v^3+104v^2+1632v+4096.
   ```

   The exact integer identity

   ```text
   (116068029v^2+76597820v+5448726416)F
   +(-3517213v^2-40477578v+125002182)R
   =119700635520
   ```

   rules out a common zero.

4. **a=X=0, a=Y=0, b=X=0, or b=Y=0.** Replace `v` by `-v` in the last case. The three equations become

   ```text
   u^2-uv-v^2+5=0,
   37u^2-82uv+38v^2+50=0,
   130u^2-40v^2-63=0.
   ```

   Their invertible linear system in the monomials forces `(u^2,uv,v^2)=(1464,2755,3309)/920`. This contradicts `(uv)^2=u^2v^2`, since the difference is `1657^2/920^2`.

All transformations, normalizations, evaluations, and the integer Bezout identity are checked by direct expansion in the independent source. Full provenance:

- `/tmp/oec/pequalnp-pilot-75/gct231/c4_zero_product_review.py`
- `/tmp/oec/pequalnp-pilot-75/gct231/c4_zero_product_review.log`
- `/tmp/oec/pequalnp-pilot-75/gct231/c4-zero-product-independent-certificates.json`

The parent sources reviewed are `fresh/c4_zero_product_pencil.py` and `fresh/c4-zero-product-square-test.json`; their SHA256 values are recorded in the log. The review exits zero and makes no Groebner call. These are exact mathematical/CAS checks, not Lean formalization.
