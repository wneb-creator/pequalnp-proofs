# Reduction strategy for L-meta-2592

Started 2026-11-25 around 13:49 UTC. Only root holds and renews the lease.

## Existing cuts

All three allowed reduction slots are already occupied in current main:

- `R_meta_2592_408`: normalize missing wire reads, NOT operand lists and output placement; then prove the bounded lower bound for the normalized circuit. It permits a strict size decrease when normalization erases all NOTs.
- `R_meta_2592_318`: split a circuit at its last NOT, obtaining an arbitrary fan-in-two prefix and monotone suffix; then prove a separator theorem with combined prefix/suffix budget 18.
- `R_meta_2592_271`: prove at least 15 non-NOT gates are necessary; then handle NOT counts 1 through 4.

A fourth reduction should not be submitted while `reductions_live=3` remains the desk state.

## Structural component prepared

`/tmp/oec/pequalnp-pilot-99/reduction_strategy/CutLast.lean` contains a compact candidate proof of the complete first hypothesis of `R_meta_2592_318`.

Split the gate list into `pre ++ g :: post`, with `g` a NOT and no NOT in `post`. Set prefix output to the first input of `g`, using the missing index `n + pre.length` when `g.inputs` is empty. This index reads false exactly as empty-input NOT requires. Keep the original output index for the suffix. List append evaluation then gives the exact factorization.

The source has three helpers, all in `PEqualNP.Outside.L_meta_2592_aux`: last-NOT split, wire-list length, and factorization. It uses only `PEqualNP.Defs`. It now compiles with official Lean 4.36.0 and the pinned cache, via `lake env lean`; both logs `cutlast.stdout` and `cutlast.stderr` are empty. No unproved placeholder occurs. Root was alerted immediately for independent review and early push.

## Additional compiled boundary lemmas

`/tmp/oec/pequalnp-pilot-99/reduction_strategy/MonoPrefix.lean` also compiles. It proves pointwise monotonicity of all wires of a monotone circuit, then:

- A monotone prefix followed by output NOT cannot compute any function false at the all-false input and true at the all-true input.
- If a final AND reads a complemented monotone-prefix output and the circuit is true at all-true, that prefix output must be constantly false. The final AND therefore equals its other input.
- If a final OR reads a complemented monotone-prefix output and the circuit is false at all-false, that prefix output must be constantly true. The final OR therefore equals its other input.

These boundary lemmas do not need a constant-free circuit or valid-wire assumptions. Empty inputs and missing reads are included. Logs `monoprefix.stdout` and `monoprefix.stderr` are empty. Root was alerted immediately.

## Compiled removal and connected representative

`/tmp/oec/pequalnp-pilot-99/reduction_strategy/Connected.lean` compiles and supersedes `EraseUnused.lean` by including its entire source plus two new lemmas. Empty successful logs: `connected.stdout`, `connected.stderr` (also `eraseunused.stdout`, `eraseunused.stderr` for the earlier component).

- `erase_unused_gate`: if gate j is not the output and no later gate reads its wire, remove it and renumber the suffix. The equivalent fan-in-two circuit has exactly one fewer gate. The list-erasure proof covers out-of-range reads.
- `minimal_not_preserving_representative`: choose a minimum-size equivalent circuit among fan-in-two circuits with at least one NOT or strictly smaller than the original. Every remaining gate is the output or is read by some later gate.
- `used_gates_output_last`: any nonempty circuit satisfying that usage condition outputs its last gate, in the exact form `output + 1 = n + size`.

The minimum representative uses ordinary `Nat.find`; no added axiom, executable declaration, or placeholder is present. These results supply the connectivity and output-trimming parts of the normalization reduction, but not its invalid-wire/NOT-operand normalization nor its hard lower bound.

## Other useful existing sources

- `L_meta_2826`: roughly 200 lines; normalizes arbitrary 10-input circuits to binary circuits, with `binary.size + notCount C ≤ C.size`.
- `L_meta_3400`: Petersen graph with one vertex deleted, on 9 inputs; proves at least 13 non-NOT gates.
- `L_meta_3402` and `L_meta_3404`: strengthen a related 9-input case to 14 gates when supplied particular free OR inputs, respectively for zero NOTs and one or two NOTs.
- `L_meta_5367`: its internal `Main1672.finalBound` proves the 9-input graph needs at least 15 total gates. Its main result gives `15 + count(effective readers of x0 or its supplied complement) ≤ size` for circuits supplied with a free complement of input zero.

No full lower bound or counterexample established by this strategy yet.

## Cost-relevant first-gate certificate, around 14:15 UTC

`FirstCollision.lean` compiles with empty successful logs. Its namespace and definitions exactly match `PEqualNP.Outside.L_meta_2592.Extended`, the renamed L_meta_6581 source. The helper-only append source is `FirstCollision.append.txt`; the standalone validation prefix must not be duplicated when integrating.

For distinct initial pins a,b and each signed binary operation d=0,1,2,3, `firstCollision` gives two rows on which the target differs while `bin d a b` and all initial pins except a agree. It uses 200 explicit small row pairs, with ordinary kernel checking split into ten lemmas. The generator exhaustively confirmed all ordered input pairs with the other input fixed at either Boolean value.

Consequently a live first binary step must retain a; swapping inputs and operation also forces b retained. For the three AND-shaped operations, setting the positive input to zero makes both the retained input and the new gate constant. Against the 15-binary floor for the nine-vertex graph, this should force 18 binary gates. For first OR, the corresponding restriction supplies one constant and forces 17. The lower-bound and library agents are assembling those deductions.

## Capped forward-state probe, around 14:25--14:29 UTC

`forward_probe.py 17 300 4` completed both first-OR symmetry classes through four binary steps in 208.5 seconds. Complete stdout/stderr and `forward-probe-results.json` are preserved in this scratch directory. This is computational exploration, not a Lean proof.

It starts with all ten essential pins and an OR of either an edge pair or a nonedge pair. Subsequent steps use the four normalized signed binary operations and all four source-retention choices. Pruning uses loss of target information, live-wire cardinality, and the existing 15-binary lower bound after fixing a vertex to zero, with an explicit projected-prefix construction as a supply-cost upper bound. Deduplication uses the verified stabilizer of the initial pair. The 120 automorphisms were independently rechecked, as was block projection against a direct implementation on 100 random tables.

Surviving state orbits after binary steps 2, 3, 4:

- First OR on an edge: 15, 503, 19,694.
- First OR on a nonedge: 29, 1,061, 42,928.

Depth four examined 525,868 and 1,105,244 transitions respectively. Both levels completed before the cap; neither established impossibility. Prefixes consisting only of ORs, and some OR sums guarded by a single negated input, survive these shallow checks. More depth without stronger pruning will grow rapidly.

An extra unit of contraction cost for duplicated projected roots is invalid in general with free complements: a multiplexer can use two copies of its control without an additional binary-gate cost. The existing constant-mass contraction must not be extended to aliases without an additional theorem.

A possible phase-aware refinement would track which polarities of each live normalized signal are available and charge a NOT when its opposite polarity is first needed. The surviving all-OR and single-negative-guard prefixes show that this refinement alone does not close the shallow cases. No stronger signed lower bound or NOT-premium theorem is claimed here.

## One-NOT source shapes, 14:32--14:42 UTC

This is mathematical analysis and finite enumeration, not a proved global cost theorem. The reproducible enumeration is in `source_shape_probe.py`; complete logs are `source-shape.stdout` and `source-shape.stderr`, with data in `source-orbits.json`. It revalidates all 120 automorphisms and all 170 nontrivial AND-source/input separation witnesses. Essentiality here means that neither replacing the NOT output by constant false nor by constant true preserves the function.

- If the sole NOT source is OR over a nonempty input support S, essentiality requires the complement of S to contain an edge. These supports have 27 Petersen automorphism orbits, distributed by support size 1 through 8 as 1, 2, 4, 6, 6, 5, 2, 1.
- If its source is AND over S, essentiality requires S to be independent. The five nonempty independent-set orbits have representatives {0}, {0,2}, {1,3,5}, {1,4,5}, {2,4,5,6}, with orbit sizes 10, 30, 20, 10, 5. The last two are maximal independent sets.
- For an independent support with at least two vertices and each v in S, choose a neighbor u of v. The two assignments {u} and {u,v} differ on the target but both make AND_S false. Thus the source cannot replace all information about any one of its support inputs.

For AND sources, fixing any support input v to zero kills the source and sole NOT. The desired argument is to delete at least four gates and contradict the arbitrary nine-vertex total-size floor 16 from L_meta_8367. A naive count of source, NOT, NOT consumer, and separate positive-v reader can count one consumer twice. Root correctly repaired the first-AND case: if the shared consumer is AND(v, NOTsource), it becomes constant false, cannot be the restricted output, and therefore forces a further outgoing-consumer deletion. If it is OR(v, NOTsource), it is identically true whenever source implies v, and can be simplified before restricting. Lower_bound's two-constant contraction is the formal route for this case.

For deeper pure-AND sources, source and an earlier v-reader can already provide two binary deletions, but a full statement still needs exact constant-propagation and branch accounting. Semantic equality to AND_S or OR_S does not justify replacing a source cone by a private tree: intermediate source wires may be shared with the rest of the circuit. Local identities such as v AND NOT(v AND t) = v AND NOT(t) save the source gate only when its other uses are absent.

The singleton AND/OR source is a literal NOT. L_meta_5367 gives a separate concrete route: with a free complemented input, 15 plus the number of effective readers of either polarity is at most circuit size. Four necessary effective readers would force 19 binaries plus the NOT. Three readers only reaches the unresolved 18-binary, one-NOT case. No four-reader lemma has been proved. Mere essentiality under constant replacement is weaker than minimality: reconvergent complementary branches can make both constant replacements wrong while still permitting more involved simplification.

For OR supports of size greater than one, fixing one support input to zero does not kill the NOT. Fixing it to one does, but the cofactor is OR of three neighbors together with a six-cycle edge function, much cheaper than the vertex-deleted graph, so the same gate-removal comparison is inadequate. Fixing all support inputs to zero also gives a smaller graph with insufficient available lower bounds.

No general one-NOT elimination theorem or complete cost premium follows from these observations. The first-AND restriction branch is concrete and is being formalized by lower_bound; deeper source accounting and literal/OR source cases remain open in this strategy.

The duplicated-root obstruction also holds without complements: majority of a,b,c has a four-gate computation from [a,b,b,c] using a AND b, a OR b, c AND (a OR b), and their final OR. One duplicated root therefore cannot simply add one to the established lower bound, even for monotone runs.

A more precise candidate for the deeper AND case is as follows. If a direct reader of v preceding the source gate is distinct from the source, then that reader, the semantically-zero source, the NOT, and a later NOT reader are four distinct removable gates under v=0. If the source is the first v-reader, the edge-row separation forces another v-reader outside the source. The two readers can coincide only at the overlapping consumer handled above. This is still a proof plan: a constant/alias compiler must certify the four deletions. In particular, an identically-true gate cannot simply be replaced by a free true input; its constant must be propagated through consumers until an actual size decrease is obtained.
