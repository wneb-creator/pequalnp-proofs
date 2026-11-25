# Independent audit of Fano synthesis pruning

Recorded 2026-11-25 by the combinatorial-route agent. This is a mathematical
and source-level audit, not a Lean proof or a certified UNSAT result. No Lean
file or solver source was changed in this audit.

## Verdict

The useful-gate predicates, four first-gate cases, and separately fixed bad
edge preserve existence of an AO2 circuit of **at most** 26 gates, subject to
the conditions below. Full-group first-gate canonicalization and fixed-bad-edge
canonicalization must not be imposed independently in one search.

## Useful gates

Let F be a nonconstant monotone Boolean function on finitely many inputs, P
its minimal true assignments, and M its maximal false assignments. Choose an
AO2 circuit C of minimum size among all circuits computing F. For every gate
g of C:

1. g is true on some assignment in P.
2. g is false on some assignment in M.

For (1), suppose g is false throughout P. Replace g by a temporary constant
zero and keep its outgoing uses. The new circuit function H agrees with F on
P, because g already had value zero on each such assignment. Monotonicity of
the downstream AND/OR circuit gives H <= F everywhere. Also H is monotone in
the original inputs. Every true input of F contains a minimal true input, so
agreement on P gives F <= H. Hence H = F.

For (2), suppose g is true throughout M. Replace g by a temporary constant
one. Agreement on M is preserved, and monotonicity of the downstream circuit
gives F <= H. Every false input of F is below a maximal false input, so
monotonicity of H and agreement on M give H <= F. Again H = F.

In either case, eliminate the temporary constants in topological order.
Maintain a map from original wires to either a constant or an input/retained
wire. AND with zero and OR with one become constants. AND with one and OR
with zero alias the other operand. Gates with two nonconstant operands stay
ordinary two-input AND/OR gates with remapped earlier wires. Repeated
operands may be retained or aliased. This construction removes the selected
gate, creates no gates, and preserves the computed function. The final
mapped output cannot be constant because F is nonconstant. Thus it is a
valid AO2 circuit with strictly fewer gates, a contradiction.

This argument allows constants only as temporary simplification symbols;
it does not assume constants are legal gates in the AO2 model.

## Minimum circuits, output position, and padding

A minimum circuit has no dead gates: delete any gate outside the output
dependency cone and remap wires. A gate with equal operands is an identity
and may similarly be removed. These observations apply even when the source
model permits an output before the last gate or an arbitrary missing output
index. A missing output is constant false and cannot compute F. For Fano,
an input-wire output cannot compute the incidence function. Consequently a
minimum Fano circuit has at least one gate and, after deleting dead gates,
its output is its last gate.

To search for an at-most-26 circuit using exactly 26 slots, first choose a
minimum witness, canonicalize it, then append OR(output, output) gates until
there are 26 gates. Every appended gate computes F, hence satisfies both
useful-gate predicates. Every nonfinal gate then has a later use. These OR
copies preserve the first gate and all read-1 proof-existence flags.

The encoding must allow equal operands for padding, at least after the first
gate. An assertion that every gate has distinct operands would require a
different completeness argument or separate searches at every size. AND
copies preserve the Boolean function but can destroy read-1 proofs, so OR
copies are the appropriate padding for the bad-edge argument.

## Four first-gate cases

The first gate of a minimum circuit reads two distinct original inputs. On
Fano, the minimal true assignments are exactly the 21 incident point-line
pairs. If the first gate is AND, its pair must therefore be incident by the
useful-gate predicate. A same-part or nonincident AND is false on all 21
minimal true assignments.

For an OR first gate there are three orbits of unordered distinct input
pairs under incidence-graph automorphisms: same-part pairs, incident
point-line pairs, and nonincident point-line pairs. The supplied scripts
enumerate a subgroup of 336 distinct edge-preserving permutations and verify
orbit sizes 42, 21, and 28, exhausting all 91 pairs. Full knowledge of the
automorphism group is unnecessary: this verified subgroup already supplies
the required transitivity. Representatives are (0,1), (0,7), and (0,9).

Thus AND(0,7), OR(0,1), OR(0,7), and OR(0,9) suffice after minimizing and
canonicalizing a witness. Boolean commutativity also permits sorting the
two predecessor indices. All target assignments and prime-implicant/read
properties are transported by these input permutations.

## Separately fixing a bad edge

For a correct Fano circuit, the prime implicants are exactly its incident
pairs: every true set contains an edge, and every edge is minimally true.
The checked read-1 lower-bound theorem, specialized to the 21-edge graph
with the seven-edge matching p = l, gives 21 + 7 <= C.size + 1. Therefore a
correct circuit with at most 26 gates cannot be read-1 on every edge.

Choose a minimum witness and one edge with no read-1 proof. Edge transitivity
sends that edge to (0,7). Pad with output OR copies. This proves completeness
of the separately fixed-bad-edge search, conditional on the cited read-1
bound and its Fano specialization. No claim that every minimum circuit is
read-1 is needed. Separate finite exhaustive searches reported four-gate P4
circuits that are not read-1 and no circuit with at most three gates. That
minimality claim is computational evidence, not a Lean-checked certificate
here. The separately compiled five-gate P4 example only disproves that a
lift fixed point must be read-1; it is not minimum.

The three-bit recursion in synthesize-pruned.py correctly records proof
monomials a, b, and ab. OR unions possibilities. AND produces ab exactly from
an a-proof and b-proof in opposite operands. An AND cannot produce a
degree-one proof because there are no empty proof trees in the constant-free,
exactly-two-input model. Repeated-variable and higher-degree monomials can be
discarded permanently because later multiplication cannot lower degrees.
This recursion would need revision if constants or empty-input gates were
introduced.

## Why the two symmetry restrictions cannot simply be combined

Once the bad edge is fixed to {0,7}, only its setwise stabilizer remains
available for further symmetry breaking. For example, a first pair {1,2} is
disjoint from that edge, whereas the full-group same-part representative
{0,1} intersects it. No permutation preserving the edge can map one pair to
the other. The intersection cardinality alone is an obstruction.

An independent enumeration in this audit found 16 permutations in the
setwise stabilizer and 14 orbits on unordered distinct input pairs. Four are
incident-pair orbits. Hence a complete joint first-gate partition would have
14 OR cases and four AND cases, not the four full-group cases. The audit's
orbit table is in
/tmp/oec/pequalnp-pilot-137/combinatorial_route/stabilizer-orbits.json.

## Limits of this audit

The Boolean useful-gate and padding arguments establish search completeness
on paper. The finite orbit checks and solver sanity checks are computational
evidence. An UNKNOWN solver result is inconclusive; an UNSAT solver result
still requires a separately checked certificate before it becomes a Lean
result. None of these finite Fano searches alone proves the universally
quantified statement of L-meta-2583 for all projective-plane orders.

## Further audit: below-function gates and implicant lifting

The following stronger pruning has a complete semantic argument on paper.
It has not been formalized by this audit, and it is not the missing theorem
that every such circuit can be made read-1 without increasing size.

Write Below(w) for the assertion that the Boolean function at wire w implies
F. Since every AO2 wire function is monotone, Below(w) holds exactly when w
is false on every maximal false assignment of F. The forward implication is
immediate. For the converse, extend any false assignment x to a maximal
false assignment m; monotonicity gives w(x) <= w(m) = false. Thus the
solver's negative-test mask is sufficient to recognize Below exactly.

### A minimum circuit has no AND with a Below operand

Suppose an AND gate g reads operands a and b, and a is Below. Alias g to a
globally, delete g, and remap every later gate and the designated output.
The replacement only increases the gate value. On every true input of F,
monotonicity of all downstream gates preserves the true output. On every
false input of F, a is false, so both the original AND and its replacement
are false; all subsequent evaluations and the output are unchanged. Hence
the circuit still computes F and has one fewer gate, contradicting minimum
size. The same argument applies to the other operand.

The global rewiring is legal in AO2: a is an earlier wire than g. After
deleting g, send its old wire number to a, decrement higher gate-wire
numbers, and retain lower wire numbers. Every remapped predecessor is still
earlier than its remapped reader. An output formerly naming g becomes a.
No constant gate, extra gate, or increased fan-in is needed. Repeated
operands are allowed, so any repeats created by the rewiring cause no model
violation; they may also be removed.

### Mixed OR lifting preserves size and terminates

Suppose an OR gate v reads u and d, where u is Below and d is not Below.
Then v is not Below: d implies v. Delete v and globally alias its output to
d, obtaining a circuit fragment Cminus. Append one OR gate with operands
the remapped old output and u, and designate this new gate as output.

For any input on which u is false, v originally equals d, so the old output
is unchanged by the aliasing, and the appended OR changes nothing. For any
input on which u is true, F is true because u is Below, and the appended OR
is true. Thus the new circuit computes exactly F. It has one deleted OR and
one added OR, so its gate count is unchanged. Both new operands already
exist: u precedes the deleted gate, and the old output is a retained or
remapped existing wire. The new gate reads only earlier wires.

There is a simple strict termination measure:

    mu(C) = the number of OR gates whose functions are not Below F.

Replacing u OR d by d weakly decreases every retained wire function,
pointwise. This follows inductively through the topological AND/OR list.
Therefore every retained wire that was Below remains Below. The removed
OR was not Below, while the appended output OR is Below because it computes
F. The other OR gates correspond one-to-one to retained old OR gates, and
some formerly dirty gates may additionally become Below. Consequently mu
strictly decreases, by at least one.

Repeated mixed-OR lifting therefore terminates in at most the initial
number of dirty OR gates. Alternatively, choose a circuit lexicographically
minimal in (size, mu) among all AO2 circuits computing F. The AND bypass
contradicts minimal size, and a mixed OR contradicts minimal mu at that size.
This avoids any informal assumption that an unmeasured rewriting process
must terminate. Because lifting preserves the function and size, it also
preserves minimum-size status.

### What the resulting normal form does and does not establish

For OR gates, Below(a OR b) is equivalent to Below(a) AND Below(b).
The normalized circuit has no OR mixing a Below operand with a dirty one,
and no AND reading a Below operand. Hence a Below wire can feed only OR
gates with other Below operands. Its paths toward the output remain within
the Below OR network. For Fano, no input wire is Below, since every singleton
assignment is false for F. Thus that final network is fed by AND gates whose
two operands are dirty; these AND gates compute implicants of F.

This does not show that those boundary AND gates are stars. Their dirty
predecessors can contain AND gates and can accept nonedges. Neither a
star-cover cost bound for these blocks nor the read-1 property follows from
the normalization just proved. Those remain the substantive gap.

For at-most-26 synthesis, choose the lexicographically minimum witness,
perform the chosen input-automorphism normalization, then pad with OR output
copies. The copies read two Below operands and are themselves Below, so
both stronger predicates survive padding. They can be combined with the
useful-gate predicates and either of the separately justified symmetry
schemes. Combining the independent full-group first-gate and fixed-bad-edge
schemes still requires the stabilizer/joint-orbit correction above.
