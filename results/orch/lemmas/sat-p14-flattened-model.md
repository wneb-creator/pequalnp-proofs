Proposed compact p14 model (2026-11-25 12:00 UTC; no solver result)

The normalization assumes the already reviewed p14 equality consequences for an exact27-gate StrictLive Fano circuit: every AND output has empty singleton support; every primary label occurs in exactly two AND operand positions; there are no singleton-carrier merges; Bzero=0; and all surplus units are the14 reserved pure-singleton units. Thus every branching wire has fanout2 and singleton support{x}, with exactly one branching wire for each input labelx. The last consequence follows from equality of the reserved-unit set and the full surplus-unit set; it has not yet been separately packaged as a Lean lemma.

Flatten only OR gates, stopping at primary inputs and AND outputs. Number the a AND gates topologically. Operand slot(j,side) is the OR of a primary-label set S[j,side] and an earlier-AND-output set T[j,side]. Every slot has at least one argument. The final output is OR of a nonempty set F of AND outputs, allowing a singleton F with zero final OR gates. All58 original Fano boundary rows remain exact Boolean semantic constraints.

Necessary structural constraints:

1. Each primary label belongs to exactly two S sets. The two S sets at any AND gate are disjoint.
2. Every AND output occurs in at least one flattened consumer: a later T set or F.
3. Every AND output occurs in at most two flattened consumers. If twice, both are operand slots carrying a common primary labelx, and neither occurrence is in F. A common label is unique by the antichain property, but uniqueness need not be explicitly encoded for a safe overapproximation.
4. Positive-support or ordinary-minimality cuts are optional and must be justified separately; the base compact model does not need them.

Why item3 follows: an AND output starts with empty support. Before its first OR-region fork, it has a unique path because empty-support wires cannot branch. A fork has support{x}. Support only grows along OR paths, so any later fork in that OR region would have to be another pure{x} fork; equality allows only one such wire. Its two paths cannot merge again at an OR, because that would merge singleton carrierx. They therefore terminate at two distinct AND operand slots, both containingx. They cannot terminate at the final OR, whose support is empty. This argument concerns one OR-only region; intervening AND gates are separate signal nodes.

Suggested binary encoding:

- S[j,side,x] selects primary arguments.
- T[j,side,k] selects earlier AND outputs (k<j).
- F[k] selects final output arguments.
- For each AND outputk, a mode is either single-use or host labelx. In single-use mode require exactly one consumer. In host mode forbid final-output use and require every selected operand consumer to containx; require at least one consumer, and at most two. Allowing host mode with only one consumer is harmless. Primary exact-two constraints already bound host-mode uses by two.
- On each of58 boundary rows, operand value is the OR of selected true arguments. AND output is the conjunction of its two operand values. Final OR must match the boundary target.

This is a safe feasibility abstraction only after independent normalization review. SAT candidates must be reconstructed and checked as actual circuits. There is no gate operator choice or one-hot predecessor selection in this model.

Potential exact reconstruction/count, requiring separate review: group every duplicated AND output by its hostx. Build a shared pure singleton proxy x OR Q_x for the corresponding group of duplicated signals. For each operand, OR its remaining distinct primary/signal arguments and any applicable proxy. Build the final OR of F. With d duplicated signals, the naive unshared OR count is27-a+d:28 primary occurrences, a+d signal occurrences,2a operand OR roots and one final root. Each proxy saves exactly the number of duplicated signals in Q_x, hence total OR count27-a and total gate count27. AND operands are distinct because opposite S are disjoint and a duplicated signal would force a common host in both. This count assumes all roots are nonempty and the abstract dependency order also permits each shared proxy before both consumers. The latter follows if every signal selected for a proxy precedes both host slots.

Controls to use:

- Exact35-gate p14 circuit: flatten and verify all16384 truth rows with equality/reuse constraints disabled. It may violate primary exact-two and pure-branch assumptions.
- Exact27-gate p7 circuit: same generic semantic control, equality disabled.
- Synthetic27-gate matching circuit: verify the compact structural constraints and reconstruction, explicitly not a Fano function control.
- The two central all-points/all-lines supports with private singleton supports are a countermodel to bare slot incidence constraints; boundary semantics must exclude them.

No new solver is authorized by this note itself. The original broad27 worker remains unchanged.
