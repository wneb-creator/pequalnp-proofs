Generic center-kernel triangle chart, 2026-11-25

This is a necessary-system transformation, not an inconsistency proof.

Start with the independently reviewed twelve-variable triangle chart, whose
first three off-diagonal entries are x,y,z and whose fourth star has rank at
most two. In the branch where a kernel vector has three nonzero coordinates,
scale that vector to (1,S,T), with S*T nonzero. Change only parameter
coordinates: x=X, y=S*Y, z=T*Z. The original first three edge weights become
1,S,T; they are retained, rather than all being set to one.

The center-star kernel equations give the other edges
A*(X-Y), B*(X-Z), C*(Y-Z). The three earlier isolated-vertex diagonal zeros
put the first three diagonal entries in the form
D*X+E*Y, F*X+G*Z, H*Y+I*Z. The fourth diagonal must vanish at (X,Y,Z)=(1,1,1)
by the isolated-vertex lemma. Together with the tangent entry-sum equation,
this gives

I = -D-E-F-G-H-2*(1+S+T).

The last diagonal is J*(X-Y)+K*(X-Z), where
J=E+H+2*(S-A+C), K=G+I+2*(T-B-C).

The generator directly checks the matrix pullback from the reviewed source,
the zero total entry sum, and the zero fourth row/column at (1,1,1). It then
expands the defining permanent by all24 permutations. Retained equations are
all six quadratic coefficients, all ten cubic coefficients, and the three
quartics X²Y², X²Z², Y²Z², plus w*S*T-1. Every retained coefficient is also
checked against its exact pullback from the reviewed source polynomial.
Dropping the other quartics only weakens a necessary system; no converse is
used. All retained coefficient normalizations divide nonzero rational
integer contents only.

The resulting system has11 variables,20 equations and1050 terms. It has fewer
variables and equations than the earlier twelve-variable chart but more
expanded terms. No performance improvement or characteristic-zero verdict
is inferred from this transformation alone. Coordinate-zero kernel strata
are handled separately by lean_setup; this chart does not cover them.
