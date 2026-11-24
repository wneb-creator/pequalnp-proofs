# Global fanout charging

Status: mathematical work, no unrestricted lower bound proved.

For a useful binary circuit with thirteen output sinks, let R be the total
number of edges directly leaving raw inputs and let B be the sum of fanout(v)-1
over nonoutput generated vertices. Every such vertex has positive fanout.
Counting edges gives g = R - 13 + B. Thus the target39 is equivalent to
R+B>=52, the number of point-line incidences.

Moving one raw input through a shared guard is not itself a loss: its later
branching vertex pays the transferred excess fanout. The difficult situation is
a branching vertex carrying two raw variables, when their four-line families
would both charge the same resource. One needs a principal-variable assignment
or an uncrossing theorem directing the other incidences around that branch.
The checked collective-avoidance premise supplies pairwise whole-cone bypasses,
but a simultaneous resource assignment is still missing.

## Restricted raw-neighbor fanout lemma

Assume p is a raw input and every gate directly reading p is a binary AND or OR
of p with a distinct raw input q. Repeated/copy/constant operands are excluded
from this lemma. Then any circuit satisfying the posted band specification has
at least four such gates. No global-normality hypothesis is required.

Suppose instead there are at most three gates. Let A be their AND neighbors and
O their OR neighbors.

If A and O are disjoint, choose a line L through p containing no point of O.
There are four lines through p, and each q!=p rules out only one of them. Set
the other three L points and all points of A to zero, all points of O to one,
and p to one. This specifies at most six zeros and at most four ones. Extend
the zero set to cardinality six while retaining p and O as ones; at least nine
positions remain available for zeros. Call this band input x. Change p to zero
to obtain y. Every direct p-consumer has the same value on x and y; induction
through the circuit gives the same value at every generated output. The seven
zeros of y contain L, so remove one foreign zero to obtain a negative six-zero
band input z>=y. Monotonicity forces the L-output at y to be zero, while the
same output at x must be one, contradiction.

If A and O intersect, choose q appearing in both an AND and OR comparator gate.
At most one additional p-consumer remains. Choose a p-line L avoiding q and,
if the remaining gate is OR(p,r) with r!=q, also avoiding r. Set all other L
points zero. Compare x with (p,q)=(1,0) to y with (p,q)=(0,1), keeping all other
raw inputs fixed. If the remaining gate is AND(p,r), set r=0; if it is OR(p,r),
set r=1. When r=q it is another comparator gate and needs no extra assignment.
The fixed requirements can be extended to six zeros in each assignment: there
are at most five prescribed zeros and at most two prescribed ones in x, with
the swap preserving cardinality. Every p-consumer is unchanged. Every other
raw input is unchanged or increases, so every generated value weakly increases
by monotonicity and induction. But the L-target changes from one to zero,
contradiction.

Thus a raw input of fanout at most three must have a generated side guard,
unless a copy/constant gate is present. Turning generated guards into distinct
charges against R+B is the remaining step; this lemma alone does not do so.

## A false stronger two-output bound

Two nonordinary line outputs can be computed in nine total gates: for
A=pabc,B=pdef and q outside their union, set U=OR(a,b,c), V=OR(d,e,f), and
H=p AND (U OR V OR q), then output U OR H and V OR H. Each effective foreign
guard has four points. This prevents charging four extra gates independently
to every nonordinary output and also warns against treating guards as
syntactically foreign to every output that uses them.

## Type-specific conjecture, not established

Tarjan's globally exact multi-conjunction transformation preserves AND count,
and its linear-family lower bound yields3N AND gates forN exact four-point
conjunction outputs. The tempting extension is that N normal dual outputs,
exact on all input sets of size at most6, still need3N AND gates even with ORs
free. This remains unproved and may be false. Degree>=7 garbage can remove all
mandatory variables from a helper, so the source theorem does not apply.

If that extension and a mixed-router-safe2A-AND bound forA abnormal primal
outputs both held, sink normalization would separate theirA OR output roots
from the normal subcircuit and give3N+2A+A=39. Neither missing assertion has
been justified. A small falsification target is two normal dual line outputs
with at most5 AND gates and a generous OR budget; no search was launched here.

## Internal forest consequence for the five-output residual

The newly checked all-five formal-cost5 bridge has a useful consequence after
canonicalizing output pairs. Suppose all nine internal gates are valid binary
merges of distinct previously disconnected raw-containing weak components.
Then a root whose parents belong to different components has a tree ancestor
cone. At its normal line complement, a selected false certificate uses each
raw input at most once; its support is exactly its four-point line, so its
formal minimum cost is at most4. This contradicts the all-five-cost5 premise.
All roots must therefore stay within an internal component. Their designated
lines lie inside those components, and pairwise line intersections force all
five roots into one component containing the union of the five lines, at least
11 raw points. Connecting those points needs at least10 internal merges.
Thus a nine-internal forest is impossible. Toolchain independently checked the
argument, with the caveat that output duplicates must be canonicalized before
applying additive cost5; OR(h,h) otherwise doubles cost artificially.

This would eliminate rank-nine forced-set survivors once syntactic saturation
is formalized. It does not eliminate internally cyclic cases or prove the
unrestricted39-gate claim.

## Sole-AND consumer exclusion

This mathematical lemma was independently reviewed by special_status. Assume
the circuit has no constants/copies and every generated gate is false on some
eight-true input, as supplied by the reviewed minimum-count normalization.
Then no raw input p can have exactly one direct consumer AND(p,h).

The side h precedes the sole consumer, so it is independent of p. Take an
eight-true input on which h is false and discard p from its zero set, obtaining
at most five outside-p zeros Z. The four line triples through p partition the
other twelve points. Some triple T satisfies |Z union T|<=6: for |Z|<=3 any
triple works; size4 requires one overlap, and size5 requires two overlaps,
both supplied by the partition. Fill Z union T to six zeros outside p. The
resulting band input still has h false and has p as its only true point on
L={p} union T. Dropping p leaves every generated value unchanged. But the
resulting seven-zero input lies below a six-zero negative band input retaining
all of L as zeros, so its L-output is false by monotonicity. Contradiction.
Raw/invalid output exclusion follows from band correctness.

The sole-OR case remains possible. This is a base case, not a full input-fanout
lower bound or a distinct charging argument for generated guards.

## Productive-line pencil restriction

For a normal dual output L, choose a certificate parse and let R be the raw
variables outside all occurrences of a shared gate g. The checked cross-context
lemma gives |L\R|<=1 whenever g is also true on another line M. If p is the
one missing point, then p belongs to every productive line M of g. Thus any
shared gate essential for a variable in such a parse has all its productive
lines in a pencil. A gate true on a nonconcurrent family is individually
redundant for every variable of every line parse. This does not make the gate
removable: repeated certificates can make individually redundant branches
collectively necessary. A global accounting of that reconvergence remains open.
