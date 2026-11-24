# Seven fixed tails: complete overapproximation for shard 17

Verdict: PASS. This is a mathematical reduction and an encoding review, not a
Lean proof or a solver certificate. No suffix-junk property is claimed after
the rewrite. Repeated leaves, semantically redundant gates, and free constants
are permitted. There is no minimality or five-distinct-leaves assumption.

## Premises and conclusion

Use the previously reviewed output-last/all-live normalization for the original
size-at-most-21, first-junk-17, at-least-two-junk shard. The resulting circuit has
17 clean prefix gates and four live suffix gates. A clean AND is false on every
independent input. L-meta-1407 and the graph's cover number seven give the
22-gate clean-circuit lower bound used by that earlier normalization.

The output is clean and gate 17 is dirty. On a live path from a dirty gate to
the output, some later gate is a clean AND: OR cannot remove a false positive.
Together with the two junk ANDs, this requires at least three ANDs among the
four suffix gates. Hence the suffix contains at most one OR.

Every such circuit yields a circuit in at least one of the following seven
fixed-tail searches. Prefix ANDs remain clean, but suffix junk requirements
are completely dropped. Therefore UNSAT for all seven searches excludes the
original shard. SAT is an overapproximation witness and requires separate
original-model and gate-count validation.

## Four-gate DAG to a formula without a minimality assumption

The four live binary suffix gates have eight operand occurrences. Each of the
three non-output suffix gates has at least one later reader, accounting for
at least three internal occurrences. Thus at most five operand occurrences
come from prefix wires or inputs/constants. Repeated external operands and
extra internal fanout can only decrease the number of distinct external wires.

If there is no OR, the suffix is a conjunction of a subset of those wires.
If there is one OR, collect its AND-only operands into conjunctions B and C.
Collect the remaining AND factors above or beside the OR into a conjunction A.
Repeated uses of the OR collapse by idempotence. The function is

    meet(A) AND (meet(B) OR meet(C)).

Remove the A factors from B and C. Move the common factors of the resulting B
and C into A. Now A, B, C are pairwise disjoint sets. If an exclusive branch is
empty, its empty conjunction is TRUE and the OR disappears. Simplify free
TRUE/FALSE constants as usual. The result is either a conjunction, a constant,
or the displayed formula on at most five distinct external wires.

This construction handles sharing, repeated operands, and redundant gates.
It does not assume that the original suffix was a smallest realization.

## Exactly seven five-leaf forms

Letters below are five leaf occurrences, not five distinct wire indices.

| Case name | Formula |
|---|---|
| meet5 | A B C D E |
| or1meet4 | A OR (B C D E) |
| or2meet3 | (A B) OR (C D E) |
| meet1or1meet3 | A AND (B OR (C D E)) |
| meet1or2meet2 | A AND ((B C) OR (D E)) |
| meet2or1meet2 | A B AND (C OR (D E)) |
| meet3or2 | A B C AND (D OR E) |

Juxtaposition means AND. To reach five leaves from a smaller conjunction, pad
with TRUE or repeated factors. To pad a one-OR form, insert TRUE factors in
any of its three conjunction groups until the total is five. Both OR branches
are nonempty after the simplifications above. With zero outer factors, the
two branch sizes are 1+4 or 2+3, up to exchange. With a nonempty outer group,
the sizes are (1,1,3), (1,2,2), (2,1,2), or (3,1,1). These are exactly the table.
Constant functions are also represented using constant leaves; the actual
target is nonconstant, so this is not needed for the main argument.

Each row has a binary formula with exactly four gates, all syntactically live.
Associativity and commutativity let the implementation fix any particular
schedule for each row. Junk status no longer restricts that scheduling.

## Prefix liveness, productivity, and sorting remain available

The suffix rewrite can discard prefix dependencies. Delete all now-unused
prefix gates, leaving k <= 17. Pick a prefix-to-leaf edge whose value is used
by the new formula and insert an OR-copy chain of length 17-k on that edge.
Redirect that leaf through the chain. All prefix gates are now live and the
prefix again has length 17. Every new prefix gate is OR, so prefix cleanness
and the productive-prefix AND condition are preserved. The copies may repeat
their operand; forbidding repeated operands would invalidate this step.

If productivity is normalized separately, a prefix AND with an operand having
empty singleton support may be replaced by an OR copy of that operand. The
operand is false on all independent inputs. The replacement only increases
wire values, and changes none on independent inputs. Since the whole circuit
is monotone and already computes F, it still computes F: positive inputs stay
positive and independent inputs stay negative. The replaced gate's singleton
support remains empty, so later prefix cleanliness tests remain valid. Prune
and pad after these replacements if required.

Finally sort the prefix by (maximum operand, minimum operand, AND-before-OR).
Choose the least key among currently available nodes in a topological sort.
A newly available node reads the wire just emitted, so its maximum operand
exceeds all prior available keys. Thus the chosen keys never decrease. Update
all references, including leaf ports. Relabel symmetric leaves after this
renumbering to satisfy the case's leaf-order restrictions.

## Review of fixed_tail_cases.py and its seven generated cases

The reviewed source is /tmp/oec/pequalnp-pilot-18/fixed_tail_cases.py. Its input
is shard17-live-productive-lex.cnf and output directory is tail7/.

The code removes exactly the unit [junk17] and the clause
[junk18,junk19,junk20], retaining the definitions of those variables. Keeping
either requirement would require a further theorem and is not justified by
this overapproximation. Prefix cleanliness and all 40 target rows stay in place.

The fixed templates compute the seven table entries. Every internal reference
points to an earlier suffix gate, using wire 30+k for local gate k. Every leaf
port is confined to wires 0..29. Constants 11 and 12 remain available, and no
distinctness condition is imposed on leaf ports. Both-operand prefix ports are
sorted within symmetric groups. Leaf/internal pairs put the leaf on the left;
internal/internal pairs use increasing gate indices. These choices respect
the existing operand-index commutativity clauses.

The extra ordering B <= D in meet1or2meet2 chooses between the two symmetric
two-factor OR branches after ordering each pair. It is valid, including ties.
All other ordered groups consist of factors of one conjunction or operands
of the same OR, so their permutations preserve the function.

Productivity constraints in the source apply only to prefix ANDs. They do not
prohibit constant or repeated-operand padding in the tail or OR-copy padding
in the prefix. The source has no fixed last operation, and its last-output
and liveness constraints agree with all seven templates.

Metadata keeps first_junk=17 as the compression boundary and sets
enforce_junk=False. A model decoder must honor this flag rather than demanding
that gate 17 is actually junk. This is a decoding issue, not a CNF soundness
issue. Every SAT candidate still needs a full truth-table check and conversion
from the augmented free-constant model before claiming a Lean-model witness.

The independent finite cross-check and DIMACS audit are recorded separately in
suffix-seven-review.json. No solver, desk action, repository modification, or
rewrite of a running CNF is part of this review.
