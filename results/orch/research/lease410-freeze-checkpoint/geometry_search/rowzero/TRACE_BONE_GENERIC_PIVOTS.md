# Honest pivot cover for the remaining B-rank-one problem

The generic B-rank-one problem is still open. This note records only two
justified first-variation pivots and their exceptional cases.

Choose a trace-zero plane basis (A,K) with B(K)=0 and B(A)=b nonzero.
In the rank-three diagonal-image application, the checked D-injectivity
gives D(K)=d nonzero. If the supports of b and d are disjoint, the already
audited exceptional chart excludes the plane. Otherwise choose a common
nonzero coordinate, permute it to0 and scale the two basis vectors, then
subtract a multiple of K from A. This gives

    B(A)=(1,tau,−1−tau), D(K)=(1,d1,d3), D(A)=(0,u,v).

The coefficient of tau in the cubic first variation is d1²−d3². A suitable
overlap coordinate makes it nonzero except in two already identified
boundary types:

- D(K) has only one supported coordinate;
- all three D(K) coordinate squares are equal and nonzero.

Indeed, if the other two squares at an overlap coordinate agree, write
their common value as c. If c=0, the D support is one. Otherwise both
other D coordinates are nonzero. Unless all three squares agree, the
chosen square differs from c. Since sum(b)=0 and its chosen coordinate
is nonzero, another b coordinate is nonzero. Choosing that coordinate
produces two unequal remaining D squares. The support-one boundary has
an independent exact audit; the equal-square boundary has exact
certificates for both cubic root families, with a second-agent chain
audit pending at this note's creation.

Independently, some R-coordinate quadratic pivot is nonzero on every
nonzero valid B=0 kernel direction. Its three values are proportional to
R_i+3D_i. If all vanish, substitute R=−3D. The checked exact identities are

    Q=3*sum(D_i²),
    C=15*D0*D1*D2,
    P=(25*sum(D_i⁴)+14*sum(i<j,D_i²D_j²))/16.

C=0 gives a zero coordinate. Q=0 makes the two remaining squares
opposite. P=0 then forces both remaining coordinates to vanish. Thus
R=D=0, which is not the chosen nonzero direction. The source and full
diagnostics are `trace_Bone_q_pivot.py` and `trace-Bone-q-pivot.*`.

Consequently the remaining generic chart can eliminate tau by the cubic
first variation and one of the three R(A) coordinates by the quadratic
first variation. This is a finite cover by three conditional pivots. It
does **not** establish a nonzero quartic pivot, eliminate its degeneracy
locus, or prove the remaining equations inconsistent.
