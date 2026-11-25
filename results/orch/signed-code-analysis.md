# Signed-support counting route for L-meta-2602

The Fano-style maximal-false-row injection gives, conditionally on at most
twelve AND gates after singleton stripping, signed words of width at most
four for all 26 variables. Unsigned support unions have size at most six
for two variables on one bipartition side, and at most five for a cross
nonedge. The same-plane-side words also admit partial-assignment separation
of every selected subset of at most three words: every set of at most
three points is exactly the point part of a maximal independent row.

These one-side conditions do **not** imply that thirteen coordinates are
needed. An independently enumerated counterexample is the following five
words on four coordinates:

- `{c-, d+}`
- `{a+, b+, c+, d+}`
- `{a+, b-}`
- `{b+, d-}`
- `{a-, c+}`

Every selected subset of at most three words is exactly the set of words
avoided by some partial assignment. Indeed, among all 32 selected subsets,
the only unrealizable one is the set of four two-literal cycle words.
This was independently checked over all 81 ternary assignments, after
CaDiCaL found the code. Adding eight singleton words on fresh coordinates
gives thirteen words on twelve coordinates, with all widths at most four
and all pair support unions at most six.

The four cycle words can be assigned to the four collinear plane points
`{0,1,3,9}`. The all-positive four-literal word can be assigned to point2.
Every closed point subset other than all points omits at least one of
the four collinear points. Consequently even requiring *all actual
closed point rows* does not rule out this compressed point code.

Cross-side constraints are essential. The search script
`plane_signed_code.py` encodes all704 maximal-false-row separations with
26 unknown signed words on twelve coordinates. With the preceding point
words fixed and all thirteen line words unknown of width at most four,
CaDiCaL returns UNSAT in less than one second. This remains UNSAT when
all pair-support-union cuts and all line-width bounds are omitted. This
only rejects that concrete point code; it is not a general lower bound
or a Lean certificate. With all26 words unknown, the full instance was
UNKNOWN at a45-second wall-clock limit.

The fixed-cycle obstruction has a direct explanation using three rows.
The all-lines row requires hitting every point word. The four implication
cycle clauses and the all-positive clause force all four cycle coordinates
positive; the eight singleton words force the remaining coordinates positive.
Consequently the word for line0 can contain only negative literals. The
row containing line0 and its nine nonincident points avoids the all-positive
word and hits all four cycle words, forcing the cycle coordinates negative.
Thus the line0 word cannot contain any cycle-coordinate literal. Finally,
the row containing just one point of line0 forces all eight fresh singleton
coordinates positive, while line0 is outside that row and must be hit.
No negative literal remains available to hit it, a contradiction.

The row certificates must use partial assignments. An internal AND gate
can be true on a false input; assigning a false side at every gate is
therefore unjustified. The actual Fano injection uses the left-side bit
on coordinates free of the fixed input variables and a merge induction.
The signed separation certificate uses `none` where both gate sides are
true.

Artifacts in job scratch:

- `signed5-4-witness.json`, `signed6-5-witness.json`: checked countercodes.
- `signed5-4-solve.log`, `signed6-5-solve.log`: complete SAT output.
- `plane-signed-fixed-solve.log`: fixed-point code, all bounds, UNSAT.
- `plane-signed-fixed-no-pair-solve.log`: fixed-point code, width bound only, UNSAT.
- `plane-signed-fixed-wide-solve.log`: fixed-point code, no width or pair cuts, UNSAT.
- `plane-signed-generic-solve.log`: generic code, all necessary bounds, UNKNOWN.

These are computational research results, not proofs of the posted gap.

## A possible later structural lemma

Suppose a point word has no signed literal private among the thirteen
point words. Select another point sharing each of its at most four
literals. Their selected point set covers the word, so no row certificate
can contain all selected points while excluding the original point.
Any set of at most three points is closed, so the word must have exactly
four literals and the four selected points must lie on the four different
lines through the original point. Fixing three selected representatives
and varying the fourth shows that every other point sharing that literal
lies on its one corresponding line. Thus a point word with no private
literal has precisely four literals, with their other point occurrences
confined to its four incident lines. This argument uses the maximal-row
separation property and plane geometry; it is not yet formalized and does
not by itself bound the number of coordinates.
