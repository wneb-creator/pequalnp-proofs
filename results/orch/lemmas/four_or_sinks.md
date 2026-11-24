# Four OR sinks with large essential supports

Conditional claim. A monotone binary-fanin circuit on the thirteen raw
inputs cannot have at most eleven gates and four distinct OR-gate sink
outputs satisfying all of the following: their target lines are distinct;
they are correct on the five/six-zero band; each output is globally at
most the OR of its line; each output has at least eight essential inputs.

There are at most seven internal (non-output) gates. Order them
topologically. Every output must directly read one of the last two
internal gates: otherwise its entire ancestor cone has at most five
internal gates plus its own gate, which supports at most seven essential
raw variables. Count only valid backward reads; invalid reads are zero.
Call the last two internal wires h and j. The remaining parent of a root
that uses exactly one of h,j is a low wire, computed using the first five
internal gates, or a raw input/constant zero.

Shared-high-parent lemma. Suppose outputs for A and B both directly read
h, and output A is h OR k. For each p in A minus B, k essentially depends
on p. Set exactly B union (A minus {p}) to zero. This is a six-point zero
set, so the resulting x is a band input. At x, h is zero because h is at
most output B, which is globally at most OR_B. Output A is one because p
is its only true line variable. Thus k(x)=1. Now change p to zero, obtaining
y. All of A is zero, so k(y)=0 because k is at most output A and output A
is globally at most OR_A. This proves essential dependence on p.

At most one output can read both h and j, since any two such OR outputs
would compute the same function, contradicting their different band
targets. (Repeated/unary inputs only make the relevant partner constant
or identical and do not evade the shared-parent lemma.)

Selection of three low partners:

* If an output A reads both h and j, the other three outputs have low
  partners. Two of them, B,C, use the same high wire. The third output D
  uses a high wire also used by A. Hence their partners essentially depend
  on B minus C, C minus B, and D minus A, respectively.
* If no output reads both high wires, all four have low partners. If one
  high wire is used by at least three outputs, choose three of those and
  use triples B minus C, C minus B, D minus B. Otherwise the high-wire
  user groups have sizes two and two; choose both B,C from one group and
  D from the other, whose partner line is A. The required triples are
  B minus C, C minus B, D minus A.

In every case three low functions essentially depend on three three-point
sets T1,T2,T3. T1 and T2 are disjoint; T3 meets each in at most one point.
The union of their dependency components requires at least six gates:

* If T3 meets both T1,T2, their union has at least seven points and all
  their labels lie in one component, so at least 7-1=6 joins are needed.
* If it meets exactly one, the union has at least eight points and at most
  two components, so at least 8-2=6 joins are needed.
* If it meets neither, there are nine points in at most three components,
  so at least 9-3=6 joins are needed.

This is exactly the existing Cut.components source/join inequality.
But the three low partners are computed by at most five internal gates,
a contradiction.

Normalization interface still requiring care: OR-FIRST is not immediately
the same as having these actual globally-bounded output roots be OR. An
earlier band-equivalent wire might have off-band false positives, while a
later AND mask produces a globally-bounded output. Retargeting preserves
the band but may lose the global upper bounds. The conditional argument
above needs a bridge establishing both properties simultaneously.
