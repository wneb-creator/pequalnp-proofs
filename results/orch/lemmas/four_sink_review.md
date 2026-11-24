# Independent review of the four-exception argument

This is a mathematical review, not a Lean certificate.

Assume the existing reduction supplies a raw-input circuit of at most eleven
gates, with four distinct target lines and four output sinks, all band-correct.
Assume also the already checked theorem excluding a full thirteen-output
circuit of at most thirty-eight gates with at most three nonordinary outputs.

## Recovering OR roots and global upper bounds together

For each target line L, consider the earliest gate whose entire band truth
table equals OR_L. It cannot be a raw input or a constant. If it is AND,
it must have two valid, distinct predecessor gates a and b. Neither parent
can be a raw input: each parent is pointwise at least OR_L on the band,
whereas no raw literal has that property. Neither parent has the target
truth table, by earliest occurrence. Thus a, b, and their AND are three
distinct gate slots.

Replace every valid later use of these three wires, in the computations of
the other targets, by constant one. This preserves each other target M on
the band. Indeed, at a row where any replaced wire was zero, OR_L was zero,
and every other line OR_M was one: distinct four-point lines have union
seven, while the band has only five or six zero positions. Raising wires
therefore preserves the already true output. At rows where every replaced
wire was one, nothing changes. Delete the three slots and propagate
constants without adding gates. Rebuild L by its direct three-OR circuit.
The four-output gate budget has not increased, and L is now globally exact.
Rebuilding the nine ordinary outputs by twenty-seven OR gates contradicts
the existing at-most-three-exceptions theorem. Consequently no target's
earliest occurrence can be AND.

Retarget all four outputs to their first occurrences, now OR gates.
Normalize them to sinks in topological order by replacing their valid later
uses by one. The same disjoint-zero-region argument preserves every band
target. Propagate constants but retain each output slot as an OR gate or
unary OR copy. A target cannot become constant one or zero because its
band truth table is nonconstant. No gate count increases. Invalid forward
reads remain zero throughout, rather than being redirected.

There are still at most eleven gates and four sinks. A single output cone
excludes the other three sinks, hence contains at most eight gates and
depends on at most nine raw variables. All four variables of its own line
are essential: choose a pair of band inputs that differ only at the chosen
line point, with the other three line points zero and exactly two outside
points zero. Thus at most five essential variables lie outside the line.

Set all line variables to zero and every foreign essential variable to one.
Extend the foreign ones to an eight-point subset of the nine outside
points. This is a negative band row; changes in inessential coordinates
cannot affect the output. Therefore the output is zero at the maximal
assignment with line variables zero, proving globally H_L <= OR_L.

If any output is now globally exact, rebuild the other nine targets
directly and again contradict the at-most-three-exceptions theorem.
Otherwise all four have at least eight essential inputs, so the hypotheses
of fresh/four_or_sinks.md hold simultaneously.

## Review of the high-parent combinatorial lemma

Let h and j be the last two internal wires. Every output directly uses one
of them, since otherwise its cone has at most five internal gates plus its
output gate and hence at most seven essential inputs.

If outputs A and B both use h and A is h OR k, then k essentially depends
on every p in A minus B. The zero set B union (A minus {p}) has cardinality
six. At its band row, h is zero and output A is one, forcing k to be one.
Turning p to zero makes all A zero; the restored global upper bound then
forces k to zero. This establishes the required three essential labels.

The selection of three low partners and the six-join component contradiction
in fresh/four_or_sinks.md are sound, with this explicit edge case:

* A unary or repeated highest-wire root j computes j itself. No other
  target OR root can read j, since distinct band targets are incomparable.
  Hence the other three roots use h and have genuine low partners; choose
  those three.
* A unary or repeated second-last-wire root h has at most six internal
  ancestor gates and therefore at most seven essential inputs, impossible.
* Nullary and constant output roots are impossible by band nonconstancy.

For ordinary binary roots, at most one reads both h and j. The remaining
case split selects triples T1, T2, T3, with T1 and T2 disjoint and T3 meeting
each in at most one point. Their three dependency components need at least
six joins, but all low partners use only the first five internal gates.

The combinatorial argument and normalization bridge appear sound. All
circuit surgery and component-count steps still require Lean formalization
before this can be used as the posted proof.
