# Frozen independent exploration

The independent construction attempt did not find a ten-gate monotone
circuit. The known eleven-gate formula is

    (x0 OR x2)(x6 OR x7) OR x0x4 OR x7(x1 OR x3 OR x5) OR x1x5.

The graph is a C4 and a triangle joined at articulation 7, with pendant 4 at
vertex 0 and pendant 3 at vertex 7. A hoped-for circuit cost additivity lemma
across these pieces was not proved. No general NOT elimination theorem was
claimed.

The exploratory LP in `kw_formula.py` gave an exactly rechecked rational
monotone KW rectangle weight of 23/2, hence a lower bound of twelve leaves
for monotone formulas. This matches the displayed formula. It is a Python
certificate, not a Lean theorem. Allowing negative-literal rectangles on the
same minimal-positive/maximal-negative submatrix gives only 10/3 and does
not usefully constrain the one-NOT case.

A normalized ten-gate circuit containing one unary NOT and nine binary gates
has at most nineteen input incidences. If all eight inputs are essential and
all nine nonoutput gates are live, at least eight incidences are external and
nine are internal. Therefore external repeats plus internal fanout surplus
are at most two. Turning this into an actual-circuit Lean lemma was requested
but was not started before the public exact proof was found. The normalized
arity, liveness, and external essentiality premises must not be omitted.

There is a simple formula observation, not formalized here: when x occurs
once positively and once negatively, and the output is monotone in x, the
negative occurrence can be set to zero if their lowest common ancestor is
AND, or to one if it is OR. Compare the two x cofactors at that ancestor and
use monotonicity of its outer context. For a ten-leaf one-NOT formula, every
essential variable needs a positive occurrence, leaving at most two negative
leaves. This observation handles several cases but leaves the case with two
positive x occurrences and one negative x occurrence. No complete formula
or circuit lower bound was obtained from it.

Exploration stopped on root's instruction when the exact public PR18915
proof became available. Its successful replacement strategy is instead a
signed ten-binary-operation lower bound, lifted from a five-variable
cofactor, and an eleven-gate monotone upper bound.
