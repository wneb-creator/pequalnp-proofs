# L-meta-2583 counterexample search

The current target is read-1 normalization for projective-plane incidence functions.
The order-two case was not searched: the existing checked `L_meta_971` already
establishes its unrestricted monotone binary lower bound of 27 gates. These
artifacts target the order-three plane, whose standard 64-gate read-1 circuit
would be beaten by an exact 63-gate monotone binary circuit.

`plane3.py` builds PG(2,3) using canonical nonzero ternary vectors, normalized so
their first nonzero coordinate is one. A point is incident with a line when their
dot product is zero modulo three. Inputs 0 through 12 are points, and inputs 13
through 25 are lines. The script independently checks line sizes and unique
incidence of pairs, then constructs the ordinary 64-gate star circuit.

`plane3.json` contains that circuit and a complete monotone testing basis:

* 52 minimal true assignments, one for each incident point-line pair;
* 704 maximal false assignments, enumerated by closing all 8,192 point subsets.

The maximal false assignment sizes have histogram `{6:52, 7:468, 8:156, 10:26,
13:2}`. Hence a monotone circuit agrees on all inputs exactly when it agrees on
these 756 boundary assignments. Every true input contains a minimal true input,
and every false input lies below a maximal false input. The independent Python
validator also verifies that every gate is a backward-reading binary AND or OR,
so the monotonicity premise is checked structurally.

The first C++ phase (`monotone63.cpp`) generated 505,400,000 mutations from 1,755
random star-cover seeds in 300.037 seconds. It weighted each missed edge by 12
and each erroneous maximal false assignment by one. The best result still omits
one edge and introduces no false positive. This is the trivial defect obtainable
by deleting one OR gate from the standard construction; it is not evidence of a
counterexample. `seed63.json` preserves an especially simple deterministic
version of that defect for exact local repair. `best63.json` is the stochastic
version, independently checked in `best63-validation.log`.

The second phase (`monotone63-positive.cpp`) starts by removing only AND gates,
which preserves all true inputs. It weights missing edges by 1,024 and records
the best approximation accepting all 52 edges separately. This phase aims to
find a structurally different SAT-repair seed with few false positive maximal
inputs. Its complete log and candidates are preserved alongside the source.

No result here proves the posted statement or refutes it. A successful zero-error
candidate would still require a Lean proof and the read-1 lower bound before it
could serve as a refutation.

## Literature observation

Read on 2026-11-25 through the read-only built-in web tool:
[Jukna, Notes on Boolean Read-k and Multilinear Circuits, arXiv:2207.08701v3](https://arxiv.org/html/2207.08701).
Its read-k definition matches the library: every prime implicant must have one
formal monomial with the same variables and degree at most k in each variable.
Other monomials may repeat variables. General read-2/read-1 separations therefore
do not by themselves settle the specialized projective-plane question.

The local reduction `R_meta_1999_103.lean` cites classical results saying AND gates
do not help Boolean-sum families whose rows intersect in at most one variable.
That rules against treating the thirteen separate neighborhood sums as an easy
compression route, although that file contains only a hypothesized transfer
bound rather than the exact-size theorem needed here. The actual Tarjan family
in `L_meta_3679.lean` has larger intersections and does not have plane incidence.
