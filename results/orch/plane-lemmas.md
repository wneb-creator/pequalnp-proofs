# L-meta-2583 reusable proof sources

Read on 2026-11-25 after new lease assignment. This is a source map and mathematical analysis, not a proof of the posted normalization.

## Exact meaning of read one

`PEqualNP.ReadK.IsReadK n C 1` quantifies over prime implicants. For each prime implicant, some complete accepting proof tree jointly reads every variable at most once. It does not say each input wire has only one circuit reader. `eachReadsAtMost` is weaker and cannot substitute for joint read vectors. PlaneStructural.lean now characterizes the prime implicants exactly as incident point-line pairs; its independent review passed.

## Best reusable construction

- `lean/PEqualNP/Outside/L_meta_7684.lean`, 1126 lines: final theorem constructs an AO2 read-one incidence circuit from any bipartite vertex cover A,B, with size at most E.card + A.card + B.card - 1. No C4-free hypothesis needed.
- Its `PEqualNP.Outside.L_meta_7684.t3692` at line555 is the typed star-cover circuit construction; helper namespace A3692 is lines6-552. It returns side-closed OR wire sets and opposite-side inputs to every AND. Its proof ends at line717.
- Its `t6579` at line1108 derives read one from that typed structure. The final theorem at line1123 is a four-line combination.
- `lean/PEqualNP/Outside/L_meta_6579.lean`, 378 lines, is a shorter independent source of the same typed-structure-to-read-one result and imports ONLY PEqualNP.Defs. Its `wire_has_read1_vec` is line288; final theorem line360. This can replace the longer B6579 component if source minimization matters.
- `L_meta_3692.lean` is the standalone typed star construction already embedded in L7684.
- On a plane, take all N points as A and B empty. Counting incidence edges gives E.card=N*(q+1), hence an explicit read-one circuit of size at most N*(q+2)-1. This construction alone does not compare with the arbitrary input circuit C.

## Checked lower bounds with extra assumptions

- `L_meta_7639.lean`, 1977 lines, final theorem line1964: for a C4-free bipartite graph with a perfect matching, E.card+N <= C.size+1. Crucially it ASSUMES `IsReadK (N+N) C 1`.
- `L_meta_4897.lean`, 1961 lines, final theorem line1929: C4-free bipartite incidence plus ReadK1 gives a vertex cover with E.card+A.card+B.card <= C.size+1.
- `L_meta_2237.lean`,1878 lines, and `L_meta_6369.lean`,1397 lines, give corresponding ReadK1 graph vertex-cover lower bounds.
- `L_meta_8569.lean`,969 lines, gives E.card+N <= C.size+1 for a least top-form circuit, but explicitly assumes `junk G C = empty`.
- `L_meta_2838.lean`,661 lines, bounds particular directly covered incidence edges by3*C.size+2*N; too weak for the exact normalization budget.
- Plane ReadK2/3 bounds L2058,L1942,L2581 have large constants and read-k premises. They cannot close this exact size-preserving goal.

## Normalizations that really are already checked

- `L_meta_4293.lean`,288 lines: one `CircuitMoves.Lift` preserves AO2, valid output, exact gate count and full function.
- `L_meta_4295.lean`,563 lines: iterate Lift to an OR-lift fixed point. At each OR, if either gate operand lies below the output then the other does too.
- `L_meta_7372.lean`,792 lines: from the fixed point (and no raw input below the output), extract a residual AO2 network whose EVERY gate is dirty. The target is the OR over a list of pairwise products of residual wires, with residual.size + 2*blocks.length <= C.size+1. This is the most precise already-checked isolation of the remaining hard step.
- `L_meta_1501.lean`,1123 lines: any least graph circuit can be changed at equal size to TopForm, preserving its number of dirty ANDs. It does not remove them.
- `L_meta_7649.lean`,956 lines: under the explicit stronger hypothesis that EVERY non-below-output gate is an OR with non-below operands, extracts a star list covering exactly E and satisfying sum(star degrees)+star count-1 <= C.size. The missing hypothesis is exactly absence of dirty ANDs.
- `L_meta_1491.lean`,2507 lines: general TopForm accounting with Ustar and junk correction terms. Dropping its correction terms is not justified.

## Existing reductions document the unresolved part

- `R_meta_4895_1.lean`,32 lines, combines an unconditional C4-free cover-budget premise with the checked star builder. This is a generic version of our goal.
- `R_meta_4895_215.lean`,126 lines, and `_628.lean`,329 lines, replace cover budget by unconditional edge-plus-matching charge and prove Konig cover duality internally. Their charge premise is not discharged.
- `R_meta_4825_1.lean`,34 lines, takes ReadK1 lower bound plus normalization as separate hypotheses; it therefore must not be mistaken for the missing lower bound.
- `R_meta_2976_418.lean`,38 lines, combines normalization, ReadK1 cover charge, and star construction to get a fully typed form. Again normalization is an assumption.

## Dirty-AND local analysis

For a wire g let S(g) be the raw variables on whose singleton input g is true. OR takes unions, AND takes intersections. An AND that contributes a repeated endpoint on an incident pair can have nonempty S(g), even though the final incidence function is false on every singleton. TopForm only forbids clean ANDs below other ANDs; it does not forbid dirty ANDs with singleton support. Replacing g by OR(S(g)) is a semantic narrowing, but constructing that OR may cost additional gates, and removing g may lose incident pairs accepted through two non-singleton children. Shared cones prevent a naive per-wire gate-count argument.

A concrete safe local pattern is g=(u OR a) AND (u OR b)=u OR(a AND b). If a AND b already implies the final target, redirect every reader of g to u, change g to AND(a,b), and add OR(output,g). The full target is preserved for any monotone downstream context: off the a AND b region the old and new g agree, while on that region the new output is true and the old target was already true. This costs one new OR. If one former operand OR becomes unused, deleting it pays exactly that cost. With both operand ORs shared this move has no proven non-increasing budget. Also C4-freeness does not itself imply the cross-term a AND b is below the target.

Checked upstream single-dirty-AND eliminators L4741,L4742,L4746,L4747 add strong routing hypotheses and assume every other AND is below the target. L4741 handles a dirty gate accepting a singleton when each sibling routing has non-neighbor witnesses in both dirty operands. L4742 handles a unique sibling vertex whose neighborhood contains one dirty operand support. L4746 treats one singleton support plus a specific routing collision. L4747 handles no-singleton dirty gates with no relevant adjacent-pair contribution. These are real transformations, but their one-dirty-gate restriction is substantial.

## Scratch indexes

- `/tmp/oec/pequalnp-pilot-100/plane-readk-files.txt`:41 source files mentioning ReadK.
- `plane-lift-junk-files.txt` and `plane-lift-junk-statements.txt`: discovered sources and full final statements for167 TopForm/Lift candidates.
- `plane-lift-selected.txt`: nine closest Lift/fixed-point final statements.

No full posted theorem or refutation has been found. Source bodies must be copied/renamed into L_meta_2583 before a final proof: imports of outside proof modules are not permitted by this step.


## Checked counterexample to an insufficient privacy hypothesis

`results/orch/lemmas/PlanePrivacy.lean` compiled with exit0 (53lines, Defs-only; logs plane-privacy-build2.out/err). Let x,a be points and b,d lines, target xb OR xd OR ab. Define A=x OR a, B=x OR b, D=b OR d, g=A AND B, h=B AND D, t=g AND h, r=A AND b, output=t OR r. All eight gates lie syntactically in the output cone; the circuit is AO2, TopForm, and an OR-lift fixed point. The target is bipartite and C4-free. Both OR operands of dirty g are shared: A feeds g,r and B feeds g,h. The incident pair xd is a prime implicant but has no joint read-one witness, so the circuit is not ReadK1. These claims are kernel checked. The circuit is NOT least: a four-gate canonical circuit computes the same target, and r is semantically redundant. Thus this example rules out deriving privacy or ReadK1 from TopForm+LiftFixedPoint+liveness+correctness alone, but does not refute a statement retaining IsLeastAO.

A useful genuine conditional sharing restriction remains: a pure point OR containing two distinct points has at most one possible raw-line clean AND partner, their unique common line. The dual holds for a pure line OR. Any remaining sharing must be with other dirty ANDs, repeated same-center use, or a clean AND whose opposite operand has extra nonsingleton behavior. No valid amortized charging argument for those cases has been found.


## Separate AND/OR count route (additional source census)

The proposed split into ORcount >= |E|-1 and ANDcount >= minimum cover is already exactly `R_meta_612_7.lean` (29lines). BOTH count bounds are hypotheses of that checked reduction, not discharged conclusions. UPDATE: its unrestricted C4-free OR premise is FALSE, witnessed by L_meta_584; see the independent verification below. A bipartite-only variant is not refuted by that example.

- `L_meta_599.lean`1267lines and `L_meta_4837.lean`1266lines prove ORcount >= |E|-1 for C4-free graphs with the additional pseudoforest condition that every induced subgraph has at most as many edges as vertices. Plane incidence violates that at the full vertex set: N(q+1)>2N for q>=2.
- `L_meta_287.lean`8237lines gives exact separate AND/OR counts for forest edge functions (plus isolated positive variables), in globally minimum circuits. Forest restriction is essential to its use.
- `L_meta_2399.lean`7384lines and `L_meta_217.lean`7353lines prove ANDcount >= minimum cover for C4-free graph functions only when the cover number is at most5. Plane cover number N>=7 does not meet that hypothesis.
- `L_meta_4187.lean`1697lines proves >=7 ANDs for the fixed Fano graph, even with one precomputed OR input and a boundary correctness promise. It is a concrete finite graph result, not a generic plane bound.
- `L_meta_1898.lean`7334lines proves >=13 ANDs for the fixed order3 plane incidence relation. Corresponding OR>=51 statements in R_meta_1896_* remain reductions.
- `L_meta_1006.lean`89lines refutes the general C4-free ANDcount/cover claim for the WEAKER maximal-independent-set boundary promise. Its11vertex graph contains triangles;6 ANDs versus cover>=7. The displayed circuit does not compute the exact graph function (e.g. edge{6,7} is rejected), so this does not refute the exact-function/bipartite count conjecture.

The AND-only model may still help: `Defs/AndCountCircuit.lean` makes OR free. `L_meta_563.lean`284lines normalizes ANY such circuit without more ANDs to one where every gate rejects every singleton and its bare-variable sides are disjoint. `L_meta_8099.lean`48lines then places every edge across the bare-variable sides of some AND; it does NOT say those entire cross products are clean graph bicliques. `L_meta_8097.lean`135lines expresses every inclusion-minimal vertex cover as a union of a disjoint choice of left/right bare sides, without a cardinality bound. This isolates the missing AND-count charge. `L_meta_6738.lean`479lines converts any Monotone2 circuit to an AND-only circuit on n+1 inputs with one forced-true extra input and no more gates than the original AND count.

Full discovered statements are saved in scratch plane-gate-count-statements.txt, plane-andcount-statements.txt, and plane-orcount-statements.txt. No unrestricted separate bound sufficient for arbitrary planes was found.


## Definitive obstruction to the generic separate-count route

Counteragent located `lean/PEqualNP/Outside/L_meta_584.lean`; independently inspected its theorem and parsed its explicit gate/edge lists. Source SHA256:8d2c28988ba3c4238d046ef61ec833063a0ef0f6089209f7ffb29aedad33749b,78lines. It is an already checked exact-function theorem, not a boundary promise. It has20binary gates,13OR and7AND, on10inputs. Every gate reads earlier wires. Its target is the15-edge Petersen graph. An independent exhaustive computation confirmed all1024inputs and verified that every pair of distinct vertices has at most one common neighbor, hence there is no4cycle. Therefore ORcount=13 <15-1=14, refuting the generic C4-free OR-count premise of R_meta_612_7. The generic count-split route is dead in that form.

The same independent computation found minimum vertex cover6, so this circuit still meets the total bound20=15+6-1: its extra AND pays for the saved OR. The graph has the odd cycle0-1-2-3-4-0 and is not bipartite. Thus this example does not refute a bipartite or plane-specific OR bound. Complete verification metadata is in `/tmp/oec/pequalnp-pilot-100/petersen-or-count-verification.json`. No unrelated PR or source modification was made.
