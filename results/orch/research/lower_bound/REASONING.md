# L-meta-2583: independent lower-bound and exact-search notes

Recorded 2026-11-25 UTC. This is research, not a proof of the posted statement.

## The missing mathematical claim

The prepared star constructor gives a read-1 AO2 circuit of size
`N * (q + 2) - 1`. The desired theorem would follow from the unrestricted AO2
lower bound `N * (q + 2) <= C.size + 1` for projective-plane incidence.

Since `N = q^2 + q + 1`, this is an explicit superlinear lower bound in the
number `2N` of input bits. It is substantially stronger than the available
linear general bounds or bounds that assume read-2/read-3.

The site's article, read directly on 2026-11-25 at
<https://pequalnp.com/papers/note-1>, section 7, identifies superlinear explicit
graph-function bounds for unrestricted monotone Boolean circuits as an open
problem in the cited literature. Its `|E|/2` statement concerns multilinear,
tropical, and arithmetic circuits. This article is evidence about the known
barrier, not a proof that this individual conjecture is unsolved today.

## Why pair-only counting does not suffice

On assignments selecting exactly one point and one line, a wire can be
identified with an arbitrary subset of `Points x Lines`. OR is union and AND
is intersection. In this abstraction, an AND gate can filter two large
relations; neither operand need be a star. Consequently a proof that charges
accepted pairs alone and silently treats each AND as producing a biclique
loses constraints from larger false assignments.

Even a below-output wire can have dirty, non-below-output ancestors. The
explicit P4 formula

`((a OR d) AND (b OR c)) AND (a OR b)`

computes `ab OR ac OR db` with five gates. Replacing the inner AND by either
operand changes the function. A four-gate read-1 circuit does exist, so this
is an obstruction to local deletion, not a counterexample to normalization.

## A differentiation route and its gap

Specializing the point inputs to each singleton yields the `N` neighborhood
OR functions on line inputs. If these linear outputs could be extracted from
an arbitrary scalar circuit at cost at most `C.size - (2N - 1)`, the familiar
linear-system lower bound `Nq` would give the desired exact bound. No such
extraction was established. Boolean idempotence and AND filters are precisely
what obstructs a direct application of arithmetic multilinearization.

## Fano exact synthesis

The program `synthesize_cnf.py` uses 14 inputs. Points are 0 through 6, lines
are 7 through 13, and incidence is `(p-l) mod 7 in {0,1,3}`.

The 21 true edge assignments together with 37 maximal false assignments
characterize the function among monotone functions. The program generates
these sets and checks their antichain characterization against all 16384
assignments before encoding a circuit. Every SAT model is separately checked
on all 16384 assignments. AND/OR are monotone, so the characterization applies.

For each of `k` gates, independent one-hot selectors choose two earlier
wires. Each test assignment has two selected operand bits and one output bit.
Six clauses impose the AND/OR operation according to a gate-type bit.
Selector implications connect operands to constants or earlier gate bits.

Safe symmetry constraints in the baseline:

- The first predecessor is at most the second, by commutativity.
- The output is the final gate. The target depends on more than one input.
- Every nonfinal gate is used later. Any at-most-k circuit can first be
  stripped of dead gates and then padded at the output by repeated-operand
  copies. Repeated operands are allowed by `IsAO2`.

No assertion forbids duplicate gate functions, duplicate input operands, or
multiple uses of a wire. Such restrictions require separate arguments and
were not smuggled into the baseline.

Sanity checks:

- P4, fixed known four-gate circuit: SAT, independently verified on all 16
  assignments.
- P4, any three-gate circuit: UNSAT from Z3 (not Lean-certified).
- C4, any three-gate circuit: SAT, independently verified on all 16
  assignments.
- Fano, fixed known 27-gate star circuit: SAT, independently verified on all
  16384 assignments; 165783 clauses.

An unrestricted 26-gate search is running with a 900-second solver timeout.
An UNKNOWN result is only a failed search. Even an UNSAT result would need a
Lean-checkable certificate before it could count as a proof.

## Sound first-gate symmetry partition

`validate_symmetry.py` exhaustively enumerates the 168 point permutations
preserving Fano lines, extends them to lines, and composes with the duality
`p -> line(-p)` and `line(l) -> point(-l)`. It verifies all 336 resulting
vertex permutations preserve the entire edge set.

The unordered distinct input pairs form exactly three orbits:

| Representative | Kind | Orbit size |
| --- | --- | --- |
| `(0,1)` | Same part | 42 |
| `(0,7)` | Incident | 21 |
| `(0,9)` | Nonincident | 28 |

These exhaust all 91 pairs. A minimum circuit's first gate has distinct
operands, since an equal-input gate is only a copy and can be removed. Thus
the six choices of pair orbit and AND/OR cover any minimum witness. After
canonicalization, output copies can restore an exact requested gate count.

## Useful-gate pruning (paper argument, not yet formalized)

The other search agent proposed the following strengthening, and I checked
the argument independently. Every gate in a minimum circuit is true at some
positive edge input and false at some maximal false input.

If a gate is false at every positive edge input, replace its wire value by
constant zero. All those evaluations are unchanged. Monotonicity of the
surrounding circuit means the output can only decrease; it therefore remains
correct on false inputs, and it remains correct on true inputs because every
true input contains a positive edge. Propagate the constant through gates;
this removes at least the selected gate. The target is nonconstant, so a
constant cannot remain as the final output. The resulting circuit uses only
ordinary AND/OR gates and earlier input wires, contradicting minimality.

Dually, if a gate is true at every maximal false input, replace it by one.
Those false evaluations remain unchanged, outputs can only increase, and
every false input lies below a maximal false input. Constant propagation
again removes the gate without changing the target.

Padding copies of the final output retain both properties. Thus these
conditions preserve existence of an at-most-k witness even when the solver
uses exactly k gates. In particular, a first AND gate must use an incident
pair; same-part and nonincident pairs are false on every positive edge
input. With first-gate symmetry, only four cases remain: AND incident, and
OR of each of the three pair types.

This useful-gate argument is not yet a replacement for the missing global
normalization theorem: it still permits dirty AND gates and repeated reads.

## Minimum alone is insufficient: a verified P4 counterexample

The other proof agent exhaustively enumerated four-gate P4 circuits and found
a minimum circuit that is not read-1. The independent CNF model also found one
for path edges 01,12,23:

- gate 4: x0 AND x1;
- gate 5: x2 OR gate 4;
- gate 6: x1 OR x3;
- gate 7: gate 5 AND gate 6.

Its output expands to x0*x1 OR x1*x2 OR x2*x3. On edge 01, every
proof repeats x1. The CNF solver verifies the full 16-assignment truth table
and the exact read1 flag recursion. Three-gate synthesis is UNSAT (solver
evidence, not a Lean certificate). The exhaustive enumeration agent reports
no circuits of size at most three and 6 non-read1 circuits among 12
irredundant four-gate solutions.

This refutes the stronger strategy that every minimum circuit is already
read-1. It does not refute the target, since lifting the below-function gate
4 through gate 5 produces a different four-gate read-1 circuit. A viable
structural strategy must account for minimum size plus lifting normalization.

The tiny exact propagation for read1 on edge {a,b} records whether a wire
has a proof of monomial a, b, or ab. OR takes unions. AND produces only ab,
from a*b or b*a; its single-variable flags are false. There is no empty
monomial because every gate has exactly two inputs and there are no
constant gates. This tracks existence of a multilinear proof tree exactly.

The strengthened Fano CNF variant fixes one failed-read edge to (0,7),
adds useful-gate predicates, and runs separately from the unrestricted
baseline. Completeness of the bad-edge restriction additionally uses the
known read1 lower bound of 27 and edge transitivity. It must NOT be combined
with an independently fixed first-gate orbit, since the same automorphism
would have to satisfy both normalizations. No UNSAT result from this
variant is claimed as an unconditional Lean result.

## Stop status, 2026-11-25 15:06 UTC

The parent reported HTTP 410 from the lease desk. All proof work and searches
were stopped. The unrestricted 26-gate CNF run returned UNKNOWN due to its
900-second timeout; the useful-gate/bad-edge variant was terminated without a
conclusion. Neither search proved or refuted the Fano case.

Before the stop, constant_folding_work.lean completed compilation successfully.
Its exact 459-line checked snapshot is constant_folding_delete_checked.lean,
SHA256 9d8ca7a088b682cc72e48f36571bcfa1fabcfe84901796bcc85b785059014f2b.
It proves AO2-preserving constant compaction, strict deletion of a forced gate
when the resulting function is nonconstant, and minimal_forced_ne: forcing
any gate of a size-minimum nonconstant AO2 circuit to either constant changes
the computed function. This is a genuine necessary condition and a partial
component, not the posted projective-plane normalization statement.

Full build logs: constant-folding-delete-002.stdout and .stderr. The exact
stop/search/build record is STOP_STATUS.json. No final gap theorem or checker
acceptance was obtained by this subtask.
