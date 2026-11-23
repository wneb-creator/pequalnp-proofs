# L-meta-952 direct proof pass

> Archive note: These are historical research-phase notes. Statements that no repository files were changed describe that phase, before this authorized archival checkpoint. Scratch paths and unpreserved search artifacts below are provenance, not archive dependencies.

The posted projective-plane one-NOT gate lower bound remains unproved and
unrefuted. No repository file was changed.

## Checked semantic helpers

`NotReplacement.lean` compiles with an empty complete log
`not-replacement-build.log`. It treats a monotone pre-NOT function h and
an independently monotone cut circuit F(x,z), assuming that
F(x,not h(x)) computes the OR of a finite point set S.

It proves:

- F(x,false) implies OR_S(x), and OR_S(x) implies F(x,true).
- If h is false on the maximal assignment outside S, replacing the NOT
  by true preserves that output on every assignment.
- If h is true on every singleton from S, replacing the NOT by false
  preserves that output on every assignment.
- If neither replacement preserves that output, h must be true on the
  outside assignment and false on at least one singleton in S.

The formal-audit agent independently read the entire file and found no
logical issue. These lemmas do not construct the cut of an actual circuit
or prove a gate-count-preserving global replacement.

`RectangleExtension.lean`, appended to that file as `RectangleFull.lean`,
also compiles with an empty complete log `rectangle-build.log`. For a
monotone h, let A be its true singleton points and B the lines whose
maximal outside assignment makes h false. Every pair in A times B is an
incidence. Therefore pairwise line intersections of size at most one
imply |A| <= 1 or |B| <= 1. The formal-audit agent independently checked
this proof as well.

`SharedUpperExtension.lean`, combined after those files as
`SharedUpperFull.lean`, compiles with an empty `shared-upper-build.log`.
It proves that a wire true at zero with cut input true has true cofactor
identically true. Consequently two AND outputs sharing their zero-parent
and having other parents true throughout h=false agree throughout that
region. Their symmetric-difference singleton points must trigger h.
Under intersection size at most one, either line then has at most one
point outside the singleton support of h. This structural lemma has not
been converted into a sufficient global gate charge.

## Direct proof attempts and their exact limits

The root's conjunction case has a plausible common-restriction argument:
for h=AND_T, lines meeting T admit the globally safe true cofactor, and
lines disjoint from T admit the same cofactor after setting T to zero.
The general common-deletion extension fails already as a mechanism for
h=x_a OR x_b: killing h requires deleting both points, but most lines
meeting that deletion set are not globally safe cofactor outputs.

For h=OR_H, a prospective split charges points in H using the false
cofactor and points outside H using the true cofactor. Each line needs
its two within-color connection counts plus one mixed connection if both
colors occur. A gate can merge both colors simultaneously only after
mixed components already exist, suggesting that released mixed-component
credits could pay for double counting. An AND may choose different safe
operands in the two cofactors and would have to serve as a mixed
connection. No global invariant or disjoint charging proof was obtained.
This also does not yet address general monotone h.

## A complete mathematical q=2 counting argument

A separate endpoint argument gives the required 2m count for three-point
lines. This has not been formalized in Lean here. Choose the earliest
wire computing each line OR. The m selected output wires are distinct
gates. They cannot be inputs, constants, unary identity gates, or the
unique NOT gate, since the latter has a monotone input.

For an OR output, one operand is true on at least two of its three
singletons. That operand is globally bounded above by the line OR. It
cannot be a corresponding lower operand for another line, because two
line points would lie in their intersection. It cannot dominate another
equal-size line OR either, by containment.

For an AND output, select an operand false at the maximal outside-line
assignment. This operand globally dominates the line OR. It cannot
dominate any other line OR: that other line is true at the selected
outside assignment. Nor can it be bounded above by a different equal-size
line OR, again by containment.

Thus the selected helpers are distinct across all output types. Each is
a gate rather than an input wire. None is one of the selected earliest
output gates: equality with a different line OR contradicts containment,
and equality with the same line OR contradicts earliest selection. The
m output gates and m helper gates give 2m gates.

The fresh child independently obtained the same three-point counting
argument using a two-point assignment to rule out two shared AND
parents. Extending the private-helper charge beyond one helper per line
is still unresolved, so this does not prove the posted all-q theorem.

## Limits of critical-assignment searches

Singleton and outside-line tests have a useful representation. A wire is
represented by A, its true singleton points, and B, its false outside-line
assignments. AND maps (A1,B1),(A2,B2) to (A1 intersect A2,B1 union B2),
while OR maps them to (A1 union A2,B1 intersect B2); NOT complements both.
The monotone rectangle condition is A times B contained in incidence.

Those test assignments alone do not generally certify the full function.
For z=NOT(threshold at least two), take a monotone U_L having the correct
singleton membership of line L, and choose distinct a,b on L. The circuit
`(U_L AND z) OR x_a OR x_b` matches the singleton and outside-line tests,
yet may fail on other pairs of active points. Thus restricted SMT results
must retain their stated scope.

The reactivated child `fresh_simulation` ran smaller full truth-table
searches; its exact results and limitations are recorded separately in
`fresh-search-scope.md`. No synthesized counterexample or universal elimination
theorem has been obtained in this pass.
