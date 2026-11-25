# Independent review of the nonzero-product C4 reduction

The reduced systems for permutation cases 2 and 3 pass exact mathematical and coefficient-lineage review. The argument covering degenerate four-dimensional restrictions also passes independent review without Groebner calculations. This review does not assert a solver verdict for the remaining open systems or exclude all C4-supported three-planes.

## Open cases and exact input lineage

On a two-plane `K` in `e=0` with `fab=HXY` nonzero as a polynomial, unique factorization gives a permutation of `(f,a,b)` and nonzero scalars `alpha,beta,gamma` with product one such that

```text
H=alpha*perm[0], X=beta*perm[1], Y=gamma*perm[2]
```

on `K`. Repeated or proportional factors cause no loss: one may still pair the three linear factors with multiplicity. These equations define an ambient three-space `W3` containing `K`.

Drop the last graph equation to obtain a four-space `W`. In the open case where `q|W` is nondegenerate, a maximal isotropic `K` is its own orthogonal complement within `W`. Therefore any extension direction with `e=1` can, modulo `K`, be normalized to

```text
w=e_direction+G6^(-1)(u*n1+v*n2),
n1=d(H-alpha*perm[0]), n2=d(X-beta*perm[1]),
```

where `G6` is the Gram matrix of the corrected quadratic on `e=0`. The inverse exists and the displayed two normals are independent.

The remaining form `ell=Y-gamma*perm[2]` vanishes on `K`. Its metric dual in `W` belongs to `K`; multiplying that dual by the nonzero determinant of `GW` gives `nv=adj(GW)*ell`. Necessary equations are consequently `q(w)=c(w)=0`, `ell^t nv=0`, `R(nv)=0`, and `L(nv)=0`, where `R,L` are the coefficients of `t,t^2` in `c(k+tw)`. The review recomputes these mixed coefficients by direct substitution, independently of the parent's directional-derivative implementation.

For case 2, permutation `(a,f,b)`, substitute `alpha=P/beta`, `gamma=1/P`, `u=U`, `v=V/beta`, then `B=beta^2`. For case 3, permutation `(a,b,f)`, substitute `gamma=1/(alpha*beta)`, `u=U`, `v=V/alpha`, then `A=alpha^2`. Every retained numerator has the stated even powers. The exact recorded denominators are nonzero constant multiples of monomials in the scale parameters. Saturation by `P*B*detW_numerator` or `A*beta*detW_numerator` makes them invertible. Each original expression times its recorded denominator was independently compared with the lifted reduced polynomial, with exact equality.

The final systems each have five ordered variables and six equations, with 134 and 132 terms. Their SHA256 values are:

```text
case2 0ab9ffa48a2b21f637556a635ff1f835fd59836ad48c77cec594a1751f7dc87b
case3 72b12e2f543766e57aec78a88717f5133442553a207566956022363aa89a867f
```

The determinant-square equation is intentionally omitted, so these remain necessary systems. No degenerate `W` point is included in these saturated inputs. Clearing the recorded denominators is also valid in characteristic 1009; a finite-field diagnostic nevertheless remains separate from a characteristic-zero proof.

The exact symmetry

```text
S:(e,f,a,b,H,X,Y) -> (-e,-f,b,a,H,X,-Y)
```

preserves `q` and negates `c`. It carries case 2 to case 4 with scales `(alpha,-beta,-gamma)`, and case 3 to case 5 with unchanged scales. These identities were independently expanded and checked.

Source/full log: `fresh/c4_nonzero_reduced_review.py/.log` in scratch, completed 2026-11-25 11:15:59 UTC. Two initial reviewer-only Sympy parsing failures involving the built-in name `beta` are preserved as attempt logs; explicit symbol parsing fixes them. No solver is called by the review.

## Complete boundary argument

Restrict `q` to `W3`. Rank three cannot contain an isotropic two-plane. At rank two, its one-dimensional radical lies in `K`. At rank one, `K` equals its two-dimensional radical.

Suppose first that the rank is two and both four-space restrictions obtained by dropping the `Y` equation or the `X` equation are degenerate. If `r` spans the radical of `q|W3`, degeneracy of the first extension forces `Bq(r,eY)=0`, and degeneracy of the second forces `Bq(r,eX)=0`. Indeed, adjoining one direction to a rank-two symmetric form on a three-space gives determinant `-det(G2)*Bq(r,w)^2` in a suitable basis. This exact block determinant identity is checked by the review.

Thus `r` is orthogonal to the five-space defined only by the `H` graph equation. Its metric image is proportional to that equation's normal `nH`; because `r` belongs to all three graph hyperplanes, the first column of the normal Gram matrix `N G6^(-1) N^t` must vanish. The independently computed columns are

```text
H paired with f: (alpha^2/2-1, 0, 0),
H paired with a: (2alpha^2/3-1, alpha/3, alpha/3),
H paired with b: (2alpha^2/3-1, alpha/3, -alpha/3).
```

The last two are impossible because `alpha` is nonzero. The first forces `alpha^2=2`; its radical is the line `f=1,H=alpha,a=b=X=Y=e=0`. For every extension vector `w`, the coefficient of `t` in `c(r+tw)` is exactly `4e(w)`. Hence that line cannot extend to an `e=1` direction.

If just the four-space dropping the `X` equation is nondegenerate, use the symmetry

```text
T:(e,f,a,b,H,X,Y) -> (e,-f,a,-b,H,Y,X).
```

It preserves both `q` and `c`, exchanges the two four-space choices, and carries the graph equations to another scaled-permutation case. Therefore the already defined open charts cover this alternative.

For rank one with `H` paired with `f`, the three-space Gram matrix splits as `(2-alpha^2)` on the `f` axis plus a two-coordinate block. If the first coefficient is nonzero, that block vanishes and `K` lies in `f=H=0`, already excluded by the zero-product extension argument. If it is zero, `K` contains the forbidden `f,H` line above.

For rank at most one in case 2, the last two rows of its Gram matrix have the same nonzero first entry `-beta/2`, so they must be equal. This gives

```text
alpha^2=1+gamma/2,
(gamma-2)(2gamma+1)=0,
beta^2(2gamma-1)=4gamma.
```

The two possibilities force `(alpha*beta*gamma)^2` to be `64/3` or `3/16`, contradicting product one. In case 3 the corresponding rows have opposite nonzero first entries, so they must be negatives. This gives

```text
alpha^2=1-beta/2,
(beta+2)(2beta-1)=0,
gamma^2(2beta+1)=4beta,
```

and the same contradiction. Cases 4 and 5 follow from `S`. These are direct row and principal-minor arguments; no Groebner basis is needed.

Finally, rank zero in the `H=f` cases would require `alpha^2=2`, `gamma=-beta` or `gamma=beta`, and `beta^2+beta-1=0`. Product one then gives `beta^4=1/2`. Reducing the latter equation modulo the former gives `beta=1/2`, which fails `beta^2+beta-1=0`. Thus rank zero is also excluded directly.

The boundary review source/full log is `fresh/c4_boundary_review.py/.log`. It independently checks both symmetries, all normal columns and Gram matrices, the scalar alternatives, the forbidden-line coefficient, and the general rank-two extension determinant. It makes no Groebner call. The conclusions reduce the remaining nonzero-product analysis to nondegenerate four-space cases; their open-system consistency remains a separate question.
