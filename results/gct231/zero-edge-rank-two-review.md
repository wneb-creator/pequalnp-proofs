# Independent exact review of the zero-edge rank-two certificate

Verdict: the exact rational certificate is valid. It proves the existence of a complex constant-permanent two-plane with `T01=x`, `T02=y`, `T03=0` and diagonal projection rank two. Thus the proposed auxiliary rank-at-most-one assertion is false. It does not give a three-dimensional witness for GCT-231 and has not been formalized in Lean.

The independent replay completed at 2026-11-25 11:21:04 UTC. It recomputes every published fraction using exact `Fraction` arithmetic and separately differentiated polynomial lists. All values match exactly; no rounded numerical value is used as a proof premise.

## Polynomial and coordinate lineage

The source `zero-edge-pencil.json`, SHA256 `68694af7231339f727f58f0ecee44361318f2e7161335daa60b1c7089e528f3b`, has twelve variables ordered as the `x,y` coefficients of `T00,T11,T22,T12,T13,T23`. The tangent equation determines `T33`, while `T01=x`, `T02=y`, `T03=0` are fixed. An earlier independent Ryser calculation in `zero_edge_saturation01_review.py/.log` reproduced all twelve coefficient polynomials in order: three quadratic, four cubic, and five quartic coefficients. The constant term is 24 and the linear coefficient vanishes identically.

The saved center and matrix entries in `zero-edge-high-precision.json` are decimal strings, interpreted as exact rational real and imaginary parts. Their numerical provenance is irrelevant to the proof once these rational values are fixed: the certificate is recomputed against the verified polynomial source. The review checks the lengths of all coordinate and matrix arrays and their unchanged hashes.

## Norm and Hessian bound

For a complex number use `|z|1=|Re z|+|Im z|`, and for a twelve-vector use the maximum of these coordinate norms. The scalar norm is submultiplicative, and the row sum of entry norms bounds the induced matrix norm.

Let `F` be the verified twelve-polynomial map, `z0` the rational center, `R` the rational matrix, and `r=10^-20`. Every point in the closed ball satisfies `|zj|1 <= |z0j|1+r`. Bounding every monomial in every second partial derivative by these coordinate bounds gives, for each component, the sum `Hk` over all ordered second partials. The resulting constant

```text
M = max_i sum_k |Rik|1 Hk
```

satisfies `||R DF(z)-R DF(z0)|| <= M ||z-z0||` throughout the ball. There is no omitted dimension factor: `Hk` already sums both derivative indices. The independent implementation differentiates the coefficient polynomials first and bounds the resulting derivative polynomials, whereas the original script counts monomial multiplicities. Both methods give exactly the same rational `M`.

## Contraction and existence

Exact arithmetic verifies

```text
epsilon = ||R F(z0)||                         approximately 2.25384207745903e-92,
eta     = ||I-R DF(z0)||                      approximately 1.142157563921164e-72,
M                                               approximately 6866467.954503159,
kappa   = eta+M*r                             approximately 6.866467954503159e-14,
kappa < 1/2,    epsilon+kappa*r < r,    eta < 1.
```

The displayed approximations are only summaries. The strict comparisons and equality with the published values use exact fractions.

On this closed, complete, convex ball, `Phi(z)=z-RF(z)` is a contraction with constant at most `kappa`. Its center displacement is at most `epsilon`, so the self-map inequality places its image inside the ball. Banach's theorem gives a fixed point `z*`. The bound `eta<1` makes `R DF(z0)` invertible by the Neumann-series criterion. Both matrices are square, so `R` is invertible. Consequently the fixed-point equation `R F(z*)=0` implies `F(z*)=0`.

## Diagonal rank

The diagonal minor in rows 0 and 1 is `m(z)=z0*z3-z1*z2`, where the subscripts here index the twelve coordinates. At the center its real part is approximately `-3.763170441785765`. Throughout the ball,

```text
|m(z)-m(z0)|1
 <= r*(|z0_0|1+|z0_3|1+|z0_1|1+|z0_2|1)+2r^2
 approximately 5.080146200717321e-20.
```

The certificate checks that this bound is strictly less than the absolute real part at the center. Therefore the minor is nonzero at `z*`, giving diagonal projection rank two. The fixed pivot entries also directly ensure that the resulting linear family has dimension two. Since all verified permanent coefficient polynomials vanish, its permanent equals 24 identically for every complex `x,y`.

## Preserved evidence

Scratch files under `/tmp/oec/pequalnp-pilot-75/gct231/fresh/`:

- `zero_edge_rational_certificate_review.py`: independent replay source.
- `zero_edge_rational_certificate_review.log`: complete successful log with input hashes.
- `zero-edge-rational-independent-review.json`: independently computed exact fractions and provenance.

The reviewed high-precision data has SHA256 `f6c593f7f88a75e1e6750dffd35312483a8441fd7a833a705bc1a459e56f922a`; the original rational certificate JSON has SHA256 `a77384ac990daf4fcad3c17812b7942b4a6c97336c89bc66ebc0c206782b6f6a`. The review exits zero and performs no numerical search, native solver call, or Lean build.
