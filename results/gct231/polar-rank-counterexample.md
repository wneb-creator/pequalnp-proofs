# Polar rank drop does not imply transposition stability

There is an exact constant-permanent pencil with diagonal projection rank one, polar rank six, and no nonidentity vertex-permutation symmetry. Thus even in the diagonal-rank-one locus, the necessary polar-rank bound of seven does not force a pencil to be transposition-stable. This pencil itself has no third independent direction.

Set `r=sqrt(2)` and

```text
A = [[0,1,0,0], [1,0,-2,1], [0,-2,0,0], [0,1,0,0]],
B = [[-1-r,0,0,1], [0,0,0,0], [0,0,0,0], [1,0,0,-1+r]].
```

Independent Ryser expansion gives `per(J+xA+yB)=24`. More generally, replacing the two nonzero diagonal entries of `B` by `a,b` gives

```text
per(J+xA+yB(a,b))-24
  = (a+b+2)(x^2-4x+6)y + (ab+1)(4x^2-4x+2)y^2.
```

The basis has rank two and its diagonal image has rank one. For an arbitrary symmetric direction `C`, the coefficient of `z` in `per(J+xA+yB+zC)` has ten coefficients, indexed by the monomials in `x,y` of total degree at most three. The exact `10 x 10` matrix of these linear functionals on `Sym_4` has rank six. The script constructs its columns from independent Ryser calculations of the `3 x 3` permanent cofactors, with factor two for off-diagonal symmetric coordinates. The complete matrix is saved in `rank-check-results.json`.

Any permutation stabilizing this pencil must stabilize its diagonal image. The two nonzero diagonal entries of `B` are neither equal nor opposite, so it must fix vertices 0 and 3 individually. The only remaining possible nonidentity permutation is `(12)`, which moves the center of `A` and does not preserve its line. Since `A` is the pencil's entire zero-diagonal subspace, that permutation cannot stabilize the pencil either. All six transpositions were also checked directly.

## The new pencil does not extend

Subtract multiples of `A,B` to normalize a third direction to `C01=C03=0`. The polar equations leave only `p=C12`, `q=C33` free. The remaining quadratic and cubic coefficients in the new parameter are

```text
F2 = 2 G,
G = p^2-(6+3r)pq-(189/2+63r)q^2,
F3-(2+r)q F2 = (240+168r)q^3.
```

Their vanishing forces `q=0`, then `p=0`. This is already an elementary obstruction; no quartic condition is needed. The exact residual Groebner basis is `[G,q^3]`, and both projective parameter charts give `[1]`, providing redundant checks. Therefore the normalized third direction vanishes.

## A canonical first-variation witness

Choose the normalized polar direction with `C12=0`, `C33=2-sqrt(2)`, and swap vertices 2 and 3 in all three matrices. The resulting matrices have canonical entries `T01=x`, `T02=y`, `T03=z`; the new third direction is

```text
C' = [[2+r,0,0,1], [0,-9,0,0], [0,0,2-r,1], [1,0,1,1]].
```

An independent full Ryser calculation gives

```text
per(J+xA'+yB'+zC')-24 = -6z^2(9z^2+26z+21).
```

Thus all pencil equations and all coefficients linear in `z` vanish, despite `C'03=1`. The corresponding 21-equation subset cannot generate the unit ideal. The higher powers of `z` obstruct a full solution. Source and full log are `first_variation_witness.py/.log`, completed 2026-11-25 11:04:51 UTC. Finite_cases independently confirmed the same coefficients against the exported equation table.

## A small classified family

The source also fixes the same block direction `B` and allows an arbitrary zero-diagonal companion `A`. First variation leaves four parameters. The mixed cubic factors into two linear branches. Their exact projective reduction shows that there are precisely four nonzero companion lines: star differences centered at 0 and 3, and stars with weights `(1,-2,1)` centered at 1 and 2. The differences have polar rank five and are `(12)`-stable; the triple-weight stars have polar rank six and no transposition symmetry. This classification is only for the fixed block `B`.

The previously reviewed two-block pencil has polar rank four but diagonal rank two; it is recorded solely as a separate check and is not used to refute the sharper diagonal-rank-one assertion.

## Reproduction and scope

Exact sources, full logs, and the polar matrices are in `/tmp/oec/pequalnp-pilot-75/gct231/fresh/polar_rank/`:

- `block_companions.py/.log`: fixed-block companion classification, completed 2026-11-25 10:59:55 UTC.
- `rank_checks.py/.log` and `rank-check-results.json`: permanent identities, polar ranks, diagonal ranks, and transposition checks.
- `triple_star_extend.py/.log`: elementary nonextension certificate and exact two-variable checks, completed 2026-11-25 11:02:05 UTC.

Each source is run with `python`, redirecting stdout/stderr to its corresponding log, from `/workspace/pequalnp-proofs`. All runs exit zero. No heavy solver or Lean build is used. These exact mathematical/CAS results invalidate the proposed symmetry inference but do not settle the general three-plane problem.
