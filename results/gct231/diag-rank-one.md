# A diagonal-rank-one pencil exists

The proposed assertion that a constant-permanent two-plane cannot have diagonal projection rank one is false. This is an explicit exact counterexample; it does not supply the three-plane required by GCT-231.

Let r=√2 and define symmetric matrices

    A = [0, 1,−1,0;
         1, 0, 0,0;
        −1, 0, 0,0;
         0, 0, 0,0],

    B = [−1−r,0,0,1;
          0,  0,0,0;
          0,  0,0,0;
          1,  0,0,−1+r].

For every complex x,y, permanent(J+xA+yB)=24. More generally, replacing B00 and B33 by a,b gives the identity

    permanent(J+xA+yB)=24+6(a+b+2)y+2(ab+1)y².

Our values have a+b=−2 and ab=−1. The matrices are linearly independent because their (0,1) and (0,3) entries independently recover x,y. A has zero diagonal and B has nonzero diagonal, so their span has diagonal projection rank exactly one.

Exact source/log: scratch `fresh/rank1_pencil.py/.log`. The check uses all24 permanent terms, verifies basis rank two by flattening both matrices, and verifies diagonal rank one. Independent Ryser review passed for the general identity, the counterexample, and both extension arguments; see `diag-rank-one-review.md`.

## This particular pencil does not extend to dimension three

For an arbitrary symmetric extension direction C, subtract multiples of A and B to normalize C01=C03=0. All coefficients linear in the new parameter then leave only C22,C23,C33 free. The remaining exact coefficient ideal over Q(√2) contains the fourth power of each of these three parameters, so all vanish. The normalized C is therefore zero. Source/log: `fresh/rank1_pencil_extend.py/.log`.

There is also a more general structural explanation. Any solution space containing A is stable under the transposition of vertices1 and2. For a direction T, normalize T01=0 modulo A. The first-variation equations give

    T11=−T13+T22+T23,
    T12=−T13/2+T22+T23/2.

The mixed coefficient of x²y² in permanent(J+xA+yT) is (T13−T23)², forcing T13=T23 and T11=T12=T22. Adding (T02/2)A makes the resulting direction invariant under that transposition. Since A is anti-invariant, the whole space is stable. The separately reviewed exclusion of transposition-stable three-planes thus excludes any three-plane containing this particular A, not only the displayed pencil.

These extension arguments remain scoped mathematical/CAS results, not Lean proofs. The rank-one pencil counterexample invalidates the proposed route from diagonal projection rank at least two to diagonal injectivity. It does not decide whether all three-plane candidates can be excluded by another argument.

A brief normalized eleven-variable numerical pencil search also found several approximate nonsimple roots, with residuals around1e-16. They were not reconstructed exactly and are not additional exact examples. All five tested first-variation matrices had numerical rank8, leaving only the known two basis directions in their kernels; the next singular values were0.055–0.984. None suggested a third-direction extension. This candidate-generation diagnostic is not a nonextension proof.
