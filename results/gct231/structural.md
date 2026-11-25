# L-gct-231 structural route

The full statement remains unresolved by this route. No three-dimensional
witness or general nonexistence theorem is claimed here.

## Row-sum-zero ansatz

Let V have columns (1,1,-1,-1), (1,-1,1,-1), (1,-1,-1,1).
Every complex symmetric row-sum-zero matrix is V A Vᵀ for a symmetric
three-by-three matrix A (with the corresponding harmless scaling of A).
Writing A's diagonal as a,b,c and off-diagonal entries as d,e,f, exact
24-permutation expansion gives

    permanent(J+z V A Vᵀ)
      = 24 + 16 z² (a²+b²+c²+2d²+2e²+2f²)
           + 64 z³ (abc+af²+be²+cd²+2def) + z⁴ permanent(V A Vᵀ).

Thus a three-dimensional row-sum-zero witness would be a maximal totally
isotropic plane for the displayed quadratic form and would annihilate the
displayed cubic. The quartic condition is not needed for the obstruction
found below.

Set r²=-2 and a_i=r(X_i+Y_i), off_i=X_i-Y_i. The quadratic becomes
-8 times the sum of X_i Y_i. Each admissible coordinate chart takes the
chosen X coordinates as free and writes Y=S X, where S is skew-symmetric
with three parameters. Swapping either coordinate of each hyperbolic pair
gives eight charts. All eight cubic coefficient ideals have Gröbner basis
[1] over Q(r). They reduce to two parity-distinct systems, because each
swap changes an off-diagonal sign and the cubic depends on these signs
only through their product.

The chart coverage has an independently reviewed linear-algebra argument:
projection of an isotropic three-plane onto any j hyperbolic coordinate
pairs has rank at least j. Its kernel is isotropic in the nondegenerate
complement of dimension 2(3-j), so that kernel has dimension at most 3-j.
Rado's independent-transversal theorem therefore selects three independent
coordinate columns, one from each pair. This is an invertible admissible
projection, and isotropy forces the graph matrix to be skew-symmetric.
This coverage argument is not formalized in Lean.

## Exact certificates and checked scope

The frozen `rowzero/` archive contains all source scripts, complete logs,
all eight explicit degree-one Nullstellensatz certificates, and a SHA256
manifest. Each certificate was checked by exact expansion. Clearing
denominators gives an integer identity

    sum_i H_i F_i - D = (r²+2) H.

`RowzeroCharts.lean` contains two independent polynomial contradiction
lemmas corresponding to the parity representatives. It compiled with only
unused-hypothesis warnings. It imports only PEqualNP.Defs and uses
`linear_combination` and `norm_num`; no computational oracle is trusted.
Its SHA256 is
`25037c36ccebc6181f1e4554611db1b33f1691084452cad91dee95ff8ac86856`.
These are polynomial lemmas only: they do not establish the geometric
reduction or refute the full unrestricted gap in Lean.

The status_review agent independently reproduced the permanent expansion,
all eight Gröbner bases, the parity reduction, and the chart-coverage
argument. An independent Lean source/axiom audit was requested after the
successful build.

## Path-support and full path chart

`path_support.py` independently parameterizes variations supported on
off-diagonal edges 01,12,23, with these entries x,y,z. Diagonal00,11,22 are
arbitrary linear forms; diagonal33 enforces total entry sum zero. The
resulting 31 equations in nine unknowns have exact QQ Gröbner basis [1]
(99.64 seconds, complete log preserved in task scratch). This excludes
only that fixed-support family.

The full path chart allows the other three off-diagonal entries to be
arbitrary linear forms as well, yielding 18 unknowns. A bounded 300-second
run of the finite agent's shared exact generator is underway. Its outcome
must be recorded separately; a time limit is UNKNOWN, never nonexistence.
