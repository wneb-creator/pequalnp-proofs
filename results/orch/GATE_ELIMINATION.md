# Gate elimination route

## Independently checked mathematics

For every ordered pair of distinct Petersen vertices x,y and each Boolean b, the edge function remains dependent on x after fixing y=b. There are 180 such cases. A witness for b=0 sets one neighbor z of x distinct from y to true. For b=1 and adjacent x,y, set only y to true. For b=1 and nonadjacent x,y, choose z in N(x) outside N(y) and set y,z true. Degree three and absence of four-cycles ensure such z exists.

Consequently, when the first genuine normalized signed binary gate has distinct input variables x,y, each of its operands must be retained for later use: fixing the other operand to a canalizing value erases its contribution to this first gate, but cannot erase its contribution to the target.

The existing nine-input signed lower bound is 15. Retaining an operand of the first gate and projecting it to zero gives a 17-binary-gate Petersen floor. For AND and signed-difference first gates, choose the operand whose zero value annihilates the output. Both that retained operand and the first gate output become constant, giving the stronger floor 18 through the existing live-wire mass contraction. Root and combinatorial agent are formalizing this.

## Limits of naive recursive deletion

Finite graph enumeration gives these explicit monotone upper bounds from star covers:

| Deleted vertices | Edges | Minimum vertex cover | Monotone gate upper bound |
| --- | ---: | ---: | ---: |
| none | 15 | 6 | 20 |
| one | 12 | 5 | 16 |
| two adjacent | 10 | 4 | 13 |
| two nonadjacent | 9 | 4 | 12 |

Thus repeating a generic two-gate deletion cannot prove 18 using an eight-input remainder: the remainder has an explicit circuit of at most 13 gates. The first OR case remains the obstruction to the stronger constant-propagation argument. Setting an operand to zero makes the first OR duplicate the other operand rather than become constant; the existing mass invariant counts constants, not duplicates. Charging duplicate signals for free is unsound for arbitrary signed circuits, because e.g. a selector can use a repeated variable in opposite polarities without an extra gate beyond its minimum.

## Compiled finite components

- `results/orch/lemmas/GateElimination.lean`, 32 lines: `ge_witness_checked` and `ge_depends_after_cofactor`, all 180 conditional dependencies. Lean exited 0; complete logs `/tmp/oec/pequalnp-pilot-111/gate-elimination.stdout` and `.stderr` are empty.
- `results/orch/lemmas/RetentionWitness.lean`, 44 lines: directly provides two truth-table rows for every distinct first-input pair and each of the four normalized binary operations. The target differs, the first gate does not, and all inputs except the selected operand agree. Lean exited 0; complete logs `/tmp/oec/pequalnp-pilot-111/retention-witness.stdout` and `.stderr` are empty. Uses the existing Extended variable bit order `[9,7,5,8,6,4,2,0,3,1]`. Copy declarations starting at `retentionMasks` into the existing Extended namespace; the standalone file duplicates only the minimal bitvector definitions for independent compilation.

Both are finite kernel-checked facts, not a proof of the posted circuit lower bound.

## Further search

Counterexample agent is running a 900-second SAT query for a 15-binary-gate signed circuit for the nine-vertex Petersen deletion. If such a circuit exists, attempting to strengthen the existing nine-input lower bound from 15 to 16 is impossible. If it is unsatisfiable, a checked certificate might close the general 18-binary bound when combined with the two-gate elimination.

## Alternative first-OR restriction

Candidate route, not yet proved: identify the first OR inputs by x = not y. Its output becomes constant. If the resulting nine-variable target has signed binary complexity at least 16, the existing mass projection would give an 18-binary Petersen floor. Adjacent and nonadjacent pairs form two graph-automorphism orbits.

Tiny Python enumeration of the signed DNF after substitution, consensus simplification, and absorption gives only the following upper bounds:
- x0 = not x1 (adjacent): 14 quadratic terms, signed-literal vertex-cover number 6, hence a 19-binary star-cover circuit.
- x0 = not x2 (nonadjacent): 12 quadratic terms plus the singleton x1, signed-literal vertex-cover number 5, hence a 17-binary star-cover circuit.

Earlier tentative mental estimates 18 and 16 were incorrect and have been corrected to root and the counterexample agent. These upper bounds do not establish the desired lower bound. No SAT run for these restrictions has yet been launched; root paused new long computations because existing builds/searches saturate the available CPUs.

## P9 with few negations

Correction to the earlier incomplete source audit: a checked monotone16 P9 lower bound does exist. Fresh strategy located it in `lean/PEqualNP/Outside/L_meta_9781.lean` (`mono_floor`) and in `L_meta_7567.lean`; `L_meta_9818.lean` combines that monotone16 certificate with the signed15 certificate. Thus the 16-gate monotone construction is optimal. The earlier statement that no checked monotone16 floor was known is superseded. An at-most-two-NOT encoding still permits zero NOTs, as required by normalization.

After deleting Petersen vertex0, the remaining degree2 vertices are1,4,5. The six degree3 vertices form the cycle 2-3-8-6-9-7-2. The degree2 vertices subdivide three opposite matching edges of this cycle; equivalently, P9 is K3,3 with a perfect matching subdivided. Put A=(2,8,9), B=(6,7,3), s=(1,5,4). Its edge function is the OR of Ai*Bj for i different from j, together with si*(Ai OR Bi) for each i.

A tiny exact Python census found 12 graph automorphisms and six unordered input-pair orbits. After reindexing original vertices1..9 to0..8, first-pair representatives are (0,1),(0,2),(0,3),(1,2),(1,5),(1,7), with orbit sizes6,12,3,6,3,6. The degree2 vertices are0,3,4 in that indexing. Data: `/tmp/oec/pequalnp-pilot-111/p9-pair-orbits.json`. These are computational observations, not Lean theorems. Counterexample agent received this symmetry data for later search pruning; no new heavy job was launched here.

The first-OR complementary restriction route above is now known to fail for the nonadjacent orbit: the negation agent found a 14-binary circuit (one explicit NOT) for x0 = not x2. See NEGATION.md. Do not pursue a 15 or16 lower bound for that restriction.

P9 signed15 synthesis ended UNKNOWN at the 900-second limit; no model was available for inversion-cost analysis. A monotone15 diagnostic CNF is prepared but remains idle because root allocated that worker to the main Petersen one-inversion search.

A concrete16-binary monotone P9 seed was exhaustively validated on all512 assignments and saved to `/tmp/oec/pequalnp-pilot-111/p9-monotone16-seed.json`. In original vertex labels its five star terms are 2*(7 OR3 OR1), 6*(8 OR9 OR1), 8*(3 OR5), 7*(9 OR5), and4*(9 OR3), joined by OR. Seven binary OR gates construct the neighbor sums, five AND gates form the stars, and four OR gates combine them. This is a construction, not a lower bound.
