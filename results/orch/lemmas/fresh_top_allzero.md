# The top-row chart with all three binary diagonal forms zero

Let the three-dimensional slice of the homogenized pencil have the form

```
N(t) = [[0,tᵀ],[t,C(t)]],
per(yJ+N(t)) = 24(y+ℓ(t))⁴.
```

Here `C` is a symmetric three-by-three matrix of linear forms. Suppose for each leaf `k` that the restriction of `Ckk` to `t_k=0` is zero. Then `Ckk=c_k t_k`. Write `b_i=Cjk` for the opposite off-diagonal entry and `H=Σ t_i b_i`. Expansion by permutations gives

```
per N = H² + Σ_i t_i² Cjj Ckk + 2 Σ_i t_j t_k b_i Cii
      = H² + t_0 t_1 t_2 [Σ_i c_j c_k t_i + 2 Σ_i c_i b_i].
```

Take a square root of 24. On every coordinate pair, `H` equals one of the two signed multiples of `ℓ²`. If `ℓ(e_i)` is nonzero, evaluating at `e_i` fixes the sign on both incident pairs. Any two active coordinates share a pair. A pair with two inactive coordinates has `H=0`. Thus one signed square root `h`, with `h²=24`, works on every pair. If `ℓ=0`, either square root works. The three restrictions determine the entire quadratic polynomial, so `H=hℓ²`.

Set `A_i=hℓ(e_i)`. The linear forms `h b_i` must be of the form

```
h b_i = A_i (Σ_j A_j t_j) + (Zt)_i,
```

where `Z` is skew-symmetric. The linear coefficient in the level identity gives

```
h c_i = 16 A_i − 2h − 2 (Σ_j A_j) A_i − 2 Σ_j Zji.
```

The remaining parameters are the three `A_i`, the three upper off-diagonal entries of `Z`, and `h`. The quadratic, cubic, and quartic conditions supply 6, 10, and 3 polynomials respectively. For the quartic conditions use the coefficients of the bracket above. The input `fresh_top_allzero_0.msolve` contains these 19 polynomials and `h²−24`. Its SHA-256 is `ec892e0a1026f3a715d1960ef0803805c2d8b1111303231134cdb4b353a47930`.

Exact rational Gröbner computation returned `[1]` in 37.70 seconds. The attached input, output, and log document that computation; the generator includes all signs by using the variable `h`. A separate direct 24-permutation evaluation agreed at six exact points over `Q(√24)`. The reported basis gives diagnostic evidence for this branch. Independent verification of a rational unit identity and its Lean certificate are pending.

Once the rational unit identity has been independently verified, the remaining full top-row chart case has a coordinate pair with nonzero complementary diagonal form `D`. Leaf permutation then selects that pair. The parameterization above covers every support of `ℓ`.
