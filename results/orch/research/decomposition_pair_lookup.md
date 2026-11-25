# Explicit barrier for proofs using only singleton and pair inputs

For the projective plane over the field with five elements, the generator produces an AO2 circuit with 62 inputs and 212 gates. The sharp read-1 bound is 31 * 7 - 1 = 216. The circuit agrees with the incidence function on all 1953 unordered singleton/pair inputs, but is not a circuit for the full incidence function.

Points are the 25 affine points (x,y), five points at infinity indexed by slope, and the vertical point at infinity. Lines are the 25 lines y=m*x+b, five vertical lines x=a, and the line at infinity. Arithmetic is modulo five.

The general prime-order construction uses onehot coordinate buckets. Four families of coordinate OR buckets cost 4q(q-1) gates. A multiplication lookup costs 2q²-q gates; an addition lookup costs the same. Equality with the point's y-coordinate costs 2q-1 gates. The four remaining projective incidence branches and their union with the affine branch cost 6q+3 gates. Total: 8q²+2q+2, which is 212 at q=5.

The independent input triple with active wires 5, 32, 36 is a false positive: point (1,0), line y=1, and line y=x. The lookup mixes slope zero from the first line with intercept zero from the second. Neither active line contains the active point.

The generator independently checks every line has six points, every distinct pair of points has exactly one common line, every singleton/pair input agrees with the incidence function, the gate count, backward reads, and the false-positive triple. Root independently repeated these checks. The frozen Lean artifact `../lemmas/decomposition_pair_lookup_geometry.lean` additionally proves circuit validity, size 212, the strict size comparison, the projective-plane axioms, and the false-positive triple. The all-pairs correctness check remains external exhaustive evidence; it is not yet a Lean theorem.

The exact degree-two relaxation is a circuit in the lattice of subsets of unordered vertex pairs, diagonals included. Input vertex v denotes the set of pairs containing v; OR is union and AND is intersection. Equivalently, use squarefree Boolean polynomials with all monomials involving three or more distinct variables erased. The q=5 example proves this relaxation cannot establish the requested universal lower bound.

Files: `decomposition_pair_lookup.py`, `decomposition_pair_lookup_q5.json`, and the complete successful output `decomposition_pair_lookup_q5.log` in this directory. Reproduce with `python decomposition_pair_lookup.py --q 5 --out result.json`.
