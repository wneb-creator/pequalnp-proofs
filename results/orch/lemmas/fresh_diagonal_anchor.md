# Diagonal anchors and the four row constraints

Let J be the all-ones matrix. Suppose L has dimension three, consists of symmetric matrices, and satisfies per(J+T)=24 for every T in L. The sum U=ℂJ+L is direct because −J cannot belong to L. Define η(sJ+T)=s. Homogeneity and polynomial identity give per(M+jJ)=24(η(M)+j)⁴ for every M in U.

## An isolated row

Suppose M in U has block diagonal form diag(a,S), with S of size three. Write P(j)=per(S+jJ₃)=c₀+c₁j+c₂j²+6j³. A permutation either fixes the first index, or selects one off-diagonal j from its row and another from its column. The latter terms sum all permanental cofactors of S+jJ₃. Hence

    per(M+jJ) = (a+j)P(j) + j²P′(j).

Equating coefficients gives

    a c₀ = 24η⁴,    c₀+a c₁ = 96η³,
    2c₁+a c₂ = 144η²,    3c₂+6a = 96η.

Successive substitution, including when either scalar vanishes, gives

    a⁴ − 16ηa³ + 72η²a² − 96η³a + 24η⁴ = 0.

Let λ₁,…,λ₄ denote the roots of X⁴−16X³+72X²−96X+24. For each i, restrict the identity to the vector subspace on which the three off-diagonal entries in row i vanish. Its polynomial coordinate ring is an integral domain. One of the four forms Mᵢᵢ−λᵣη(M) therefore vanishes on this whole subspace. Thus, for a fixed r(i) and three scalars βᵢⱼ, all M in U satisfy

    Mᵢᵢ = λᵣ₍ᵢ₎ η(M) + Σⱼ≠ᵢ βᵢⱼ Mᵢⱼ,    Σⱼ≠ᵢ βᵢⱼ = 1−λᵣ₍ᵢ₎.

A row of T in L with all off-diagonal entries zero must vanish. If all entries of a row of T instead equal c, apply the quartic to T−cJ, where a=0 and η=−c, to get c=0. The row, its off-diagonal restriction, and its three differences have the same kernel on L.

In the full-row chart per(sJ+N(w))=24(s+ℓ(w))⁴, the top row of N(w) equals (0,w₁,w₂,w₃). Taking s=−1 and w=(1,1,1) gives the quartic for a=−1 and η=ℓ(1,1,1)−1, independently of all lower-block coefficients.

## Exclusion of a diagonal matrix in J+L

Suppose A=diag(aᵢ) belongs to J+L. Coefficient comparison in per(A+jJ)=24(1+j)⁴ gives e₁(a)=16, e₂(a)=72, e₃(a)=96, e₄(a)=24. The four entries are precisely the roots above. They and their six pair sums are each distinct. Both monic discriminants are nonzero modulo 461, where the roots are 21,39,61,356 and all six pair sums are distinct.

Use ten basis matrices for the ambient symmetric matrices. The first four are diag(aᵢᵏ), 0≤k<4. The last six have zero diagonals and entries (aᵢ+aⱼ)ᵏ off the diagonal, 0≤k<6. Their independence follows from the two Vandermonde determinants. The four functionals d per evaluated at A+jJ for j=0,1,2,3 annihilate L. Add the functional extracting the coefficient of the first off-diagonal basis matrix. The five functionals share a five-dimensional kernel K. The last functional takes value −1 on A−J, so E=K∩L has dimension two. Let H₀,H₁,H₂ denote the coefficients of 1,j,j² in the Hessian of per at A+jJ, restricted to K. All three vanish as bilinear forms on E.

Since H₀ is invertible, put O=H₀⁻¹H₁. E and O(E) both lie in the three-dimensional H₀-orthogonal complement of E. The map from E to that complement modulo E therefore has a nonzero kernel vector v. Both v and Ov belong to E. Seven quadratic equations on v follow, with matrices

    H₀, H₁, H₁O, OᵀH₁O, H₂, H₂O, OᵀH₂O.

Multiplying each equation by each of the five coordinates gives 35 cubics. Their coefficient matrix in the 35 cubic monomials is invertible. Hence all the coordinate cubes of v vanish, a contradiction.

Two independent exact computations establish invertibility. The symmetric basis makes the gradient and Hessian entries symmetric polynomials of the roots. The integer computation evaluates them using Newton power sums, then constructs the exact rational kernel and all 1,225 cubic-matrix entries. The finite-field computation forms its matrices directly from the four displayed roots and all 24 permutations. All corresponding entries agree modulo 461. In the common basis det(H₀)=9803356117276277820358656, congruent to 74. The cubic determinant is congruent to 312. Thus the rational matrix is nonsingular. This mathematical and exact computational proof awaits a Lean bridge.

In the nonzero-edge Cauchy four-frame case, u₀₃=u₀₁u₀₂/(u₀₁−u₀₂), u₁₃=u₀₁u₁₂/(u₀₁−u₁₂), and u₂₃=u₀₂u₁₂/(u₀₂−u₁₂). The frame point (x,y,z)=(1/u₁₂,1/u₀₂,1/u₀₁) has all six off-diagonal entries equal to one. Subtracting its matrix from J gives the excluded diagonal anchor.
