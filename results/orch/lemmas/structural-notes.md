# Structural route

Initial obstacle: T(C)=0 is syntactic OR-reach, not semantic singleton support. A buffer x AND x hides x from OR-reach. Consequently any direct proof replacing every OR by a monochromatic union is invalid unless buffering cost is charged.

A sufficient endpoint is a cover by k nonempty complete bipartite rectangles with |E| + k <= C.size+1. The C4-free assumption makes every rectangle a star; selecting one center gives a vertex cover of size <=k. The combinatorial helpers are written in structural-combinatorics.lean, currently awaiting toolchain availability for checking.

The difficult unproved component is extracting such a rectangle cover with a gate budget from arbitrary AO2 circuits with T(C)=0. Nested dirty AND gates and reused filtering regions are the obstacle. LowerPart/LowerPart2 and FlagCore/FlagMode only handle circuits with one dirty AND and substantial normal-form hypotheses, so they cannot be applied directly.

## Linear restriction pruning

Proposed lemma in structural-linear.lean: if monotone f AND g equals OR_A, then one operand already equals OR_A. At the maximal input avoiding A, both cannot be true. The operand false there must be false at every input avoiding A, while both are true at every input meeting A. This is a genuine useful normalization lemma; awaiting compile.

Restricting all line inputs except b to false and b to true turns the target into OR_{N(b)}. Therefore its specialized circuit can prune AND gates. Difficulty: one original OR gate can specialize differently for different b via upstream AND gates, so this alone does not give disjoint OR charges.

- Checked structural-combinatorics.lean with pinned Lean v4.36.0 and Mathlib: exit 0, no diagnostics. Logs: /tmp/oec/pequalnp-pilot-163/structural-combinatorics.stdout and .stderr.

## Pair-dirty minimum-circuit route

Parent requested testing whether every size-minimal T=0 circuit can be pair-clean. The instrumented structural-optimal.cpp searches circuits exactly at |E|+tau-1 containing an AND true on an input of support at most two where target F is false. Gate-operation tags are retained in memo canonicalization so dirty-AND history is not forgotten.

Computational evidence only:
- 2+2 split, all14 nonempty C4-free targets, through4 gates: no optimal pair-dirty circuit.
- 2+3 split, all53 targets, through5 gates: none.
- 2+4 split, all188 targets, through6 gates: none (144148856 depth6 nodes).
- 3+3 through7 running; this excludes optimal dirty circuits except the C6 optimum8 case if completed.

A valid earliest-pair-dirty observation: all earlier ANDs are false on its chosen nonedge pair; therefore each operand accepts via direct OR-reached endpoints. T=0 makes each direct OR support monochromatic. Opposite colours give a rectangle; same colours can give either singleton overlap or a distinct same-colour pair. A same-colour two-point birth cannot birth a cross-edge pair, but may participate in filtering existing edge signals.

## Checked partner uniqueness

structural-partners.lean checked with exit0 and no diagnostics. If a rectangle A×B has |A|>=2 and |B|>=3 in a C4-free graph, there is at most one point z satisfying every rectangle pair ab is an edge or zb is an edge. Consequently a gate accepting the rectangle can have at most one point z whose single-variable reader g AND x_z is globally below F. Two partners would cover B by common neighbours of the two partners and common neighbours of two distinct A-points; each set has size<=1. The symmetric statement holds with sides exchanged.

This is a local restriction only. Readers accepting several edges or containing other dirty gates do not directly reduce to one point partner.

- 3+3 through7 completed: 6,754,248,074 depth7 nodes, no optimal pair-dirty circuit. Only optimal C6 size8 remains among six-input cases. SMT search for that case is running with all64 assignments and exact T0 constraints.

## Checked clean-prefix implication

structural-pairclean-prefix.lean checked exit0, no diagnostics. Public lemma `StructuralPrefix.pair_clean_prefix_below` proves: if every AND gate j<k rejects all nonedge pairs (singletons included), then every such AND is globally BelowF. The proof inducts on wire indices. On an F-negative input, a true wire must have a true singleton witness; for an AND, two witnesses would create a true nonedge pair and contradict pair-cleanness. Supporting `wire_mono` and `prefix_support` are checked too. Basic wire evaluation lemmas were adapted from L_meta_6369, all within the owned nested namespace.

Consequently, after a T0-preserving top-form normalization, an earliest pair-dirty AND cannot have earlier AND ancestors: those would be globally below F and top form excludes them. Its operands must therefore be pure ORs of inputs. The remaining task is to turn that classification into a gate-saving or cost-charging operation.

## Checked full earliest-dirty rectangle classification

structural-top-rectangle.lean and structural-classification.lean checked exit0 with no diagnostics. In namespace TopRectangle:
- child_in_cone propagates gate ancestry through one operand.
- pure_or_wire proves a wire with no AND in its ancestry is exactly the OR of orIn on every input.
- earliest_no_and_cone uses TopForm plus pair-clean-prefix BelowF to exclude earlier AND ancestors of an earliest pair-dirty AND.
- earliest_operands_or and earliest_and_rectangle give exact all-input rectangle behavior.
- wire_orIn_one_colour proves T=0 makes orIn of every wire monochromatic.
- earliest_active_classification combines this with a genuine accepted edge: the AND either accepts a singleton, or its two OR supports have opposite colours. Same-colour disjoint supports are excluded by pairactivity.

The files include already checked foundations for standalone checking. Parent can deduplicate the namespace foundations when assembling.

## Further finite checks

- 1+5 through5: 31 targets, 1,328,692 depth5 nodes, no optimal pair-dirty circuit.
- C6 exactly8-gate T0 circuits, all64 truth assignments plus at least one pair-dirty AND: Z3 UNSAT in182.4629 seconds. Encoding independently reviewed by counterexample agent. Thus all <=6-input cases support minimum pair-clean normalization computationally; this is not a Lean proof.
- C6 plus pendant line vertex (3+4 inputs,7 edges,tau3), exactly9 gates: Z3 UNKNOWN after300 seconds. No conclusion.

A stronger prospective normalization fact is gate pivotality: in a least T0 circuit each gate must be pivotal on some positive edge assignment when forced false, since otherwise monotonicity/minterm completion and constant propagation give a strictly smaller equivalent T0 circuit. Existing semantic cut-program machinery should support this.

### Free side-OR banks, checked

`structural-bank-essential.lean` proves that if each of n raw variables has a pivotal witness preserving every auxiliary bank output, any binary circuit correct on the bank-consistent inputs has at least n-1 gates. The bank is modeled as independent extra input coordinates; the circuit need not behave correctly on inconsistent inputs.

`structural-matching-bank.lean` specializes this to r disjoint matching edges, r>=2, with OR of all point variables and OR of all line variables supplied for free. Both bank bits can remain true while toggling any chosen raw input changes the target. Consequently at least 2r-1 additional binary gates remain necessary. Both standalone files compile with empty stdout/stderr. This handles the simple matching core when both setup ORs of a dirty rectangle are lambda resources; obtaining a disjoint downstream charge decomposition remains open.

The same variable-witness argument extends informally to residual vertices with all pure lambda OR banks free: a bank containing v has a pure-star centre z different from the residual edge's other endpoint w; C4-freeness provides another vertex in the bank outside N(w), keeping that bank on without turning the target on. This gives a residual endpoint lower bound, which is insufficient by itself for dense residual graphs. Algebraic route is formalizing the broader finite-set witness.

### Same-colour and anchored-box refinements

`structural-intersection.lean` is checked: on an opposite-colour pair, conjunction of two same-colour OR supports is exactly the OR of their intersection. Replacing the gate by the intersection function decreases it pointwise, but a raw OR/input replacement may expose colour and violate T0. A singleton intersection can safely be represented by AND(v,v) at the same index and cost.

`structural-anchored-box.lean` is checked with empty logs. If A is contained in the star at line z and B in the star at point y, every residual edge in A x B avoiding a=y and b=z is in a matching. Both endpoint projections have cardinality equal to the residual edge count. If y-z itself is an edge, every edge in A x B lies on one of the two anchor stars, so no residual remains. This formally classifies a dirty rectangle whose two setup ORs are both free lambda banks.

`structural-bank-selected.lean` is checked and generalizes the free-bank support argument to an arbitrary selected set T of raw variables, obtaining |T| <= size+1. This avoids reindexing residual matching endpoints.

The strengthened pendant-C6 search `structural-pendant-normal-smt.py` enforced full truth-table correctness, T0, TopForm, edge activity, and minimum-circuit signal dominance. It returned UNKNOWN at 300 seconds, not UNSAT. Counterexample route independently reviewed the encoding. `structural-pendant-pivotal-smt.py` additionally enforces every gate's contextual pivotality on some positive edge pair; this is justified by the independently checked semantic-pivotal.lean normalization.

### Semantic colour and buffer-boundary charging

Checked `structural-clean-singletons.lean`, `structural-clean-masking.lean`, `structural-clean-reach.lean`, and `structural-semantic-mixed-paid.lean` establish a useful global accounting fact: every OR gate whose SEMANTIC singleton support contains both colours lies outside `lam`, hence is counted by `orN \\ lam`. A clean AND with a two-colour singleton support on one operand has no singleton support at all on the other. These statements need AO2 and a proper bipartition, but not T0, C4, TopForm or leastness.

Checked `structural-reader-centres.lean` adds: a gate accepting two distinct singletons can have at most one singleton partner vertex across all clean AND readers in a C4-free graph. This holds with arbitrary upstream ancestry. Zero-singleton and exactly-one-singleton dirty gates remain the difficult cases.

`structural-reader-family.py` supplies a computational obstruction to a constant bound on a last dirty gate's reader graph. A minimal-vertex-cover CNF for a subdivided star is built so that every pre-output AND is dirty at the central singleton. Point-input identity buffers enforce T0. For r=2,3,4,5 the full truth tables, T0, TopForm and contextual edge-pivotality of every gate are verified; the unique clean AND accepts 2r residual edges and needs cover size r. The constructions use 12,26,52,102 gates, so they are NOT counterexamples to the target lower bound or to a statement requiring global minimum. They show why upstream cost or minimum-circuit surgery cannot be omitted.

Checked `structural-buffer-boundary.lean` defines the compatible OR-descendant region of a buffer set B, and its boundary K. Every first incompatible OR has at most one affected predecessor, so K injects into any finite set containing those outside readers. The source also supplies exactly the region compatibility and boundary hypotheses needed by the library agent's flexible shared-DAG buffer relocation. A follow-up source is proving those readers are paid semantic-mixed ORs, separated into disjoint sets by their original raw colour.

### Checked singleton pinning normal form

`structural-buffer-lex.lean` minimizes size, then AND-ancestor-pair count, then the number of gates that are not input identity buffers. Pinning an AND with singleton acceptance and exactly that singleton's edge-pair profile to AND(a,a) preserves function, T0 and size, cannot increase andPairs, and strictly erases a nonbuffer gate from the final objective. Therefore such a gate is already an actual input buffer in the lex minimum.

`structural-buffer-normal.lean` returns the SAME constrained minimum witness with TopForm and this `ProfilePinned` property. It does not assume direct TopForm preservation after pinning; minimum andPairs supplies the TopForm argument.

`structural-intersection-profile.lean` checks that a pure OR(A) AND OR(B) with one-colour supports and A intersect B = {a} has the singleton a's exact profile on every opposite-colour pair. `structural-earliest-pin.lean` fully composes this with the earlier exact earliest-dirty rectangle theorem: under TopForm, pair-clean earlier ANDs, T0, proper bipartition, and singleton raw-side intersection, the earliest AND is an actual input buffer in a ProfilePinned circuit. All four standalone files have clean empty compile logs.

The library route independently checked and completed the global wrapper: all input identity buffers in a T0-constrained minimum number at most |orN \\ lam|. It uses `structural-buffer-paid.lean` (boundary injection and disjoint opposite-raw-colour paid sets) plus its flexible actual circuit relocation. This gives a formal charge for the earliest same-colour singleton-intersection case. The >=2 intersection and opposite-colour dirty rectangle cases, and global residual edge/cover accounting, remain unresolved.

### Final structural status and preservation scope

All structural Lean sources and computational scripts are frozen. The latest normalization artifact is `structural-earliest-pin.lean`, which compiles standalone and contains the earlier pinning, lex-minimum, TopForm and earliest-rectangle prerequisites. The latest boundary artifact is `structural-buffer-paid.lean`, which compiles standalone and gives the actual compatible-region/boundary injection and disjoint paid sets. Full successful stdout/stderr logs are retained in the task scratch directory and are empty; the parent is preserving them in the branch.

No proof or refutation of L-meta-4675 was obtained. The unresolved step is a global charge for residual edges plus their additional cover cost when dirty AND payloads interact. The checked same-colour singleton-intersection normalization and input-buffer charge do not settle opposite-colour rectangles, larger same-colour intersections, or shared downstream pair-only filtering. No partial result should be represented as the posted theorem.

The three pendant-C6 SMT runs all returned UNKNOWN at 300 seconds (plain, normalized, and contextual-pivotal/canonical-order variants). The C6 eight-gate dirty-optimum run returned UNSAT. The finite enumerator's inherited footer `Separate bounds violated: OR=0 AND=0` uses flags that were not updated in the structural instrumentation and is NOT evidence for separate OR/AND lower bounds. Its intended dirty-at-reference-optimum check remains the only claim from those enumerations. Its memoization also does not preserve lambda structure, so it supplies no exhaustive residual-accounting claim.

Independent read-only reviews completed by this agent: MaskMerge, MaskCut, MaskCutFlex, PinAnd, and algebraic-centres all passed with their explicit hypotheses. PinAnd does not directly claim preservation of TopForm; the lex-minimum argument supplies that through the minimum andPairs objective.
