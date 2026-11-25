# One-paid-NOT strategy

Status: partial. The checked17-binary-plus-NOT bound makes an eighteen-gate candidate with one paid NOT an exact seventeen-binary-gate case. Nothing here proves the full target or a NOT-elimination theorem.

## Physical meaning of the first normalized OR

The existing FirstOr checkpoint concerns a signed live derivation, not the first physical gate. With one free negative x0 rail and one paid NOT, its first normalized OR may arise from:

- an ordinary OR of two distinct positive raw inputs;
- an AND of the free negative x0 input and a negative raw xv produced by the paid NOT. Its physical value is NOT(x0 OR xv), which normalizes to x0 OR xv.

The latter must not be silently discarded. A De Morgan rewrite moves the paid NOT after an OR only if the negative xv wire has no other uses.

## Incidence pressure

In a normalized connected eighteen-gate circuit with seventeen binary gates and one unary NOT there are35 incoming gate incidences. If the paid NOT output has d reader occurrences, internal wires consume at least17+(d-1) incidences. Primary wires consume at most19-d.

If both x0 rails are used and m of the nine nonzero variables have fanout one, essentiality gives at least20-m primary incidences. Therefore m>=d+1. In particular there are at least two nonzero fanout-one variables. If the free negative rail is unused, the corresponding bound is m>=d.

Every essential nonzero variable must have a path to the output avoiding the paid NOT. Otherwise, because all remaining gates are AND/OR, the output is antitone in that variable. A variable influencing the NOT operand must therefore also have a positive bypass. Counting such bypasses separately is not yet justified: several can share the same branch point.

## Two normalized binary steps

Suppose the first step is q=a OR b. After a second step r, suppose a raw pin v is still needed and r becomes constant when v=false. Projecting the suffix to that cofactor charges two distinct constant roots, v and r. The projected q can be rebuilt using at most one OR gate. The checked signed nine-input cofactor lower bound15 therefore gives

    15 + 2 <= 1 + suffix_cost,

so suffix_cost>=16 and the whole two-step prefix requires at least18 binary gates.

The helper lemmas/TwoPrefixFloor.lean implements this generic projected-bound argument using the existing Binary17 dependency. Both its generic suffix_sixteen lemma and its concrete second_and_or_eighteen case passed Lean with exit0 and empty logs. The stable source hash is f5b9446fe3030cacb95d432411c73fa580663b61ec20210599cf998a72778cf8.

The concrete case r=v AND q, with v distinct from a,b, is particularly simple. Select a neighbor t of v outside {a,b}. On singleton t and edge {v,t}, both q and r are false and every original pin except v agrees. Thus the raw v pin must remain in the suffix bank. The preceding charge applies.

The separate checked helper lemmas/TwoPrefixAndRaw.lean covers a second AND of two raw pins. Its second_raw_and_eighteen uses the existing pivotal witness when one operand is outside {a,b}. The remaining case is r=a AND b. In that exceptional case q and r are invariant under swapping a,b. Petersen is not invariant under that transposition, so at least one of the raw a,b pins must remain. Restrict that retained pin tofalse: r and the pin become constant, while q becomes another original pin. With a zero-cost reconstruction of projected q this would give a nineteen-binary lower bound. The checked second_same_and_eighteen uses the already established one-gate reconstruction and proves the sufficient eighteen-binary bound. TwoPrefixAndRaw.lean passed Lean with exit0 and empty logs; hash5bbccfc24d022434fa96cbf75bce32a8b6897cd975ee455dd7e9a15b4301ae6c.

## Finite second-step probe

The script two_prefix_probe.py enumerates every first OR of distinct inputs and every fresh non-OR second operation on the ten pins plus q. It checks full1024-row target truth tables, but is not itself a Lean certificate.

Counts:

- 6,600 cases have an explicit single-pin pivotal witness and a constant projection.
- 45 second-AND cases use the swap-retention argument above.
- The remaining600 cases are exactly two forms:

    I.  r=(a OR b) AND NOT c, with c outside {a,b}.
    II. r=v AND NOT w, after q=v OR a, where a and w are adjacent and v,a,w are distinct.

Thus no second positive AND survives the existing seventeen-binary budget. In formII, q and r can jointly hide v precisely on assignments already containing the edge {a,w}; that is why the single-pin witness fails. For example, the free negative x0 rail can realize q=v OR a and r=v AND NOT x0 when a is adjacent to0.

Data: two_prefix_probe.json stores every explicit single-pin witness and all600 survivors. The three checked positive-AND helper cases cover all fresh second positive AND gates up to elementary operand commutation, absorption, and case assembly. The two mixed-operation survivor families and their full finite exclusion classification remain unformalized.

## A valid formula-only monotonization fact

If a monotone output is computed by an AND/OR formula in which x and NOT x each occur exactly once, the negative leaf can be replaced by a constant without changing the output. At the least common ancestor of the two occurrences, use constanttrue when that ancestor is OR and constantfalse when it is AND. For fixed other variables, monotonicity of the final output in x proves the replacement safe. Constant propagation saves a gate.

This does not apply to arbitrary circuits merely because each raw rail has one reader: downstream fanout can create several reconvergences, and there is no single formula least common ancestor. No general bounded-reader circuit monotonization lemma is claimed.

## Global projection cuts, now checked

GlobalProjectionCut.lean passed Lean with exit0 and empty logs (SHA256611940656f2d9362f02572810252eb801aa61faa27e34646a9e898d4d771d372). It proves:

- arbitrary Reach prefixes can be replayed after restriction without extra binary gates;
- a designated step having a constant projected operand can be skipped for free;
- if a newly produced wire R and raw pin v are both retained in the suffix and become constant under v=false, then the whole prefix-plus-current-step-plus-suffix costs at least18 binary gates;
- if an earlier prefix step already reads a projected constant, only the retained constant R is needed for the same18 lower bound.

Thus the global sole-use argument has checked cut lemmas for both earlier and later uses of a raw input entering a positive AND. They retain explicit Reach-prefix/Live-suffix availability and retention premises. A literal Circuit reader-count theorem still requires decomposition of the normalized derivation at the relevant cuts.

The intended consequence is: in a seventeen-binary candidate, a raw variable used as a positive factor at an AND cannot have an earlier binary use (the earlier use becomes a free projected step) or a later normalized use (the suffix retains both constants). This is stronger than the two-prefix restrictions and applies beyond an OR-only prefix.

## Genuine centers versus filtered-pass gates

A raw positive-AND reader can be false or true on its own singleton assignment. Two nonzero vertices with sole AND readers that are both false on their own singletons cannot be adjacent: order the readers, evaluate the edge pair, and the earlier reader receives baseline values in its other operand; the later reader then does too. Both outputs remain at their all-zero values, contradicting acceptance of the edge. This gives independence only for these genuine edge-generating centers.

An AND whose other operand is true at zero can pass its raw singleton. Free negative x0 or the paid NOT can supply that true baseline, so this case cannot be included in the preceding independence claim.

## Direct filtered-pass gates sharing the paid NOT

A narrower useful case is a paid NOT output Q=NOT H directly feeding two sole raw readers v AND Q and w AND Q, for distinct nonzero v,w. H is independent of v,w and is monotone when x0 is fixed. The pivotal-set argument behind SoleOrPartner applies to H: equality of OR(v,H) is equivalent to equality of v AND NOT H when other coordinates agree and H is independent of v.

For a negative input, enlarge its selected set to a maximal independent set while keeping x0 fixed. If the set omits v or w, that omitted vertex is pivotal, forcing H=false. If the set contains both, remove both using H's independence. At most two selected inputs remain, because Petersen's independence number is4. Singleton rejection and PairLocalization then show that a falsepositive H is possible only if v,w are both neighbors of0. The only remaining pair is the opposite pair associated with the third neighbor:

    v,w={1,4}: pair{7,8};
    v,w={1,5}: pair{3,9};
    v,w={4,5}: pair{2,6}.

The fixed-x0 qualification matters. At x0=false, the two alternating C6 triads are maximal in the nine-vertex cofactor but not in the full graph; they also give H=false, since either one filtered vertex is outside and pivotal, or removing both leaves a singleton. At x0=true, removing both leaves at most a pair containing0, which is never an allowed exceptional pair.

Thus if one of two directly filtered vertices is not adjacent to0, H is below the full target. Then replacing the paid NOT output by true preserves the circuit function: where H=false nothing changes, and where H=true the target is already true. Constant propagation removes the NOT and its direct filter gates. Three distinct direct filtered vertices likewise force H below the target. This direct-filter classification is a paper argument passed to lean_setup; no checked theorem is claimed here yet.

Caution: a gate false on every positive edge cannot in general be discarded from a one-NOT circuit merely by checking positive pairs. Its removal may destroy monotonicity and lose positive supersets where the NOT changes value. Such productivity pruning is valid for the zero-NOT auxiliary, not automatically for this branch.

## A thirteen-gate relaxation target for two direct filters

In the exceptional two-filter case, take the x0=false cofactor. The general cofactor16 bound and the two rail readers leave exactly sixteen gates, comprising fifteen binary gates and the paid NOT. Replacing the paid NOT output by true deletes that NOT and the two direct filter AND gates. The result has at most thirteen gates and is monotone on the nine remaining inputs.

Every edge row stays true. On every maximal negative row where H0 is false, the NOT value was already true, so the entire computation is unchanged. The shared-filter classification permits H0 to be true on only one maximal independent4-set I: the union of the two filtered neighbor vertices and the exceptional opposite pair. Thus the resulting thirteen-gate monotone circuit is true on all twelve edge rows and false on eleven of the twelve maximal-negative rows, with I unconstrained.

Example: filtered old vertices1,5 permit old pair{3,9}; their union is old{1,3,5,9}, whose nine-input mask is277. The three possible independent4-set masks are58,201,277 and are symmetric under automorphisms fixing the deleted vertex0. A thirteen-gate circuit for this relaxed23-row specification would not be a counterexample to L-meta-1884 by itself. Conversely, a lower bound14 for the relaxed specification would rule out this direct-two-filter one-NOT subcase, once its structural and restriction wrappers are assembled. Root and counterexample received this smaller auxiliary; no search result or checked relaxation lower bound is claimed here.

Refinement of the relaxation split: let d be the number of binary readers of the paid NOT that survive in the sixteen-gate cofactor. If d>=3, replacing its output by true removes the NOT and at least three binary readers, giving at most twelve monotone gates for the loose relaxation. If d=2, its only readers are the two direct filters, and the stronger thirteen-gate relaxation must additionally reject the opposite-pair mask260: with both filtered inputs zero, both AND outputs stay zero regardless of Q.

For I277 there are also two necessary negative rows in BOTH cases: masks21 and273, obtained by deleting one of the two exceptional-pair vertices from I. H0 is independent of the two filtered variables and rejects singleton assignments, so H0 is false on both rows; the paid NOT was already true there. Setting it totrue therefore leaves the output unchanged even if it has extra readers. These give sound25-row constraints for the twelve-gate loose case and26-row constraints for the thirteen-gate strong case. The stronger260 constraint is not valid without the exactly-two-reader premise.

The semantic core of SharedFilter.lean was subsequently checked by lean_setup: its unsafe_pair theorem proves that any H-accepted negative input yields an accepted nonedge pair exceptional for both filtered vertices, retaining all factorization, independence, and fiber-monotonicity assumptions. This is independent support for the negative-row scope used above; the complete circuit deletion and relaxation wrappers are still unassembled.

## Closing the strengthened relaxations from an eight-variable floor

Both strengthened row specifications force the relaxed monotone function G to equal the exact nine-variable graph function f0 whenever either exceptional-pair endpoint t is false. Every negative assignment extends a maximal independent set. If that extension is not I277, its negative row is retained. If it is I277 and t is false, the assignment lies below one of the added negative rows21,273. Every positive assignment contains one of the twelve positive edge rows.

Consequently a twelve-gate loose relaxation would yield an at-most-eleven-gate exact eight-variable cofactor by setting an essential endpoint t=false. Each endpoint is essential because an incident edge is positive and its other endpoint singleton is negative. Thus an eight-variable monotone floor12 excludes the loose relaxation.

The relevant eight-variable graph is Petersen minus the nonadjacent old vertices0,3, up to symmetry. Its old vertex4 is a leaf attached to9. Deleting4 leaves Theta(2,3,3), with paths6-9-7,6-1-2-7,6-8-5-7. The existing checked L517/L3128 floor11 applies to that seven-variable graph; L2960 even bounds its number of non-NOT gates by11. Therefore the missing eight-variable floor follows by restricting the essential leaf tofalse and deleting its first reader. The exact circuit restriction wrapper remains to be assembled by the team.

For a thirteen-gate strong relaxation, the same eight-variable floor forces each endpoint t to have exactly one reader, which must be OR: two readers disappear under t=false, while a sole AND reader becomesfalse and forces a second downstream gate to disappear. The AND cannot be the output, since G has positive edges not containing t.

Write the sole OR reader as t OR A. The partner A is independent of t. It is safe in the precise sense A<=f0<=G. The checked Defs-only helper StrongRelaxOrSafety.lean proves this semantic assertion with explicit cofactor, positive-row, monotonicity, independence, and factorization hypotheses. Its finite pivotal lemma says every independent assignment omitting t can be extended to an independent assignment where adding t creates an edge, except the single set I277 minus t. On that exceptional set, G=false but G(I277)=true; hence A must also befalse. The assumption G(I277)=true is forced in any thirteen-gate candidate: otherwise all twelve maximal negative rows are rejected and G=f0, contradicting the exact sixteen-gate cofactor floor.

The paper circuit completion uses safe OR lifting. Replace the gate t OR A everywhere by raw t, and append OR A at the output. Since A<=G, this preserves G and the gate count. If the new raw t has multiple readers, or its sole reader is AND, restriction removes at least two gates, contradicting the eight-variable floor. Otherwise repeat along the finite initial OR path from t toward the first AND. Such an AND must exist because G rejects singleton t yet depends on t. Appended output ORs cannot obstruct the original path. This excludes the strong thirteen-gate relaxation, conditional on ordinary gate-restriction and OR-lifting bookkeeping. No complete Circuit theorem or full L-meta-1884 proof is claimed here.

StrongRelaxOrSafety.lean checked on2026-11-25 at16:33 UTC with exit0 and empty logs;88lines3524bytes, SHA25685e67209ca40652a99c1cb14c4d4cfd9c4677954969ba7f2ddd08c6ed067df46. Independent review requested. SharedFilterSafety.lean was also checked by lean_setup, proving the safe two-filter and three-filter cases and the AND-filter-to-OR-factorization bridge.

## Checked reduction to the25-row auxiliary

The extra negative row260 is unnecessary in the OR-safety proof. The25-row loose specification alone has exact cofactors at either exceptional-pair endpoint set tofalse, and the same safe-partner argument applies at budget13. StrongRelaxRows.lean now checks both cofactor exactness and the statement that rejecting I277 makes the whole function equal f0. The existing generic LiftFix.main normalization supplies a closed top-OR set at no larger size, so no custom iterative lifting theorem is needed. The team is assembling the actual lower14 theorem for this25-row specification.

ElimManyCount.lean checks a generic constant-folding count: every gate reading a known constant is charged, and a designated constant-producing middle gate plus its later readers are charged as well. Forced13Compile.lean uses this to construct an actual monotone circuit of size at most13 from the forced pre/empty-AND/post circuit, under an explicit four-reader charge and an eighteen-gate budget. PairReaderCharge.lean discharges that four-reader charge from two rail-reader gates outside the NOT plus two distinct direct filters. These are dependency tests using the existing checked Helpers.Elim compiler, not final-submission files.

DirectFilterRows.lean checks that for filtered old vertices1,5 the paid-NOT operand H is false on all thirteen required negative rows. Every retained maximal negative row is pivotal for one omitted filtered vertex, except row25; rows25,21,273 reduce to singletons after erasing the two independent filtered variables. The theorem retains explicit fiber monotonicity, independence, and factorization premises.

TwoFilterAuxBridge.lean assembles those lemmas with root's SafeNotRaise replacement theorem. It constructs an actual Monotone2 circuit D with size at most13 and all twelve positive plus thirteen negative row constraints. Its premises are: the original pre/NOT/post circuit computes the full target; pre and post are AND/OR of fan-in at most2; total size at most18; there are at least two rail-reader gates outside the NOT; the post list contains canonical AND[1,Q] and AND[5,Q]; and the actual NOT operand satisfies the stated semantic hypotheses. It checked with exit0 and empty logs on2026-11-25 at16:47 UTC,82lines3883bytes, SHA256d8c78af9d397b3e9ab4618f9b046a841320790832bc196881a5e51f5ce5e1257. Root's separate DirectFilterBridge is supplying those semantic hypotheses from actual sole-reader circuit premises.

The configuration restriction remains material. This does not yet cover fewer than two direct paid-NOT filters, filtered raw inputs with additional readers, composite filter operands, or cases with fewer than two effective rail-reader gates. The full L-meta-1884 target remains open in this workspace.

## Closed canonical two-filter case

CanonicalTwoFilter.impossible checked with exit0 and empty logs on2026-11-25 at16:53 UTC. It concerns an actual circuit in this order:

    pre; NOT(ins); before; AND[1,Q]; between; AND[5,Q]; after,
    Q = old wire11 + pre.length.

Its hypotheses state that every other gate is AND/OR of fan-in at most2 and avoids raw inputs1,5; the NOT inputs avoid1,5; the output differs from raw1,5; the total gate count is at most18; at least two other gates read a rail in{0,10}; and the circuit computes the full Petersen target on ten positive inputs plus free NOT(x0). The conclusion is False. No fiber-monotonicity, independence, or factorization premise remains in this theorem: root's actual-circuit DirectFilter bridge proves all of them. The contradiction combines the actual thirteen-gate construction with lean_setup's fully checked RelaxationFloor.fourteen.

The final auxiliary lower bound uses lower_bound's checked EightExtension.eight_floor and RestrictionEight.cofactor_reader_floor, my SoleAndRestriction.and_reader_floor, and the checked least-circuit/lift-fixed-point wrappers. SoleAndRestriction treats either operand order at a raw2-AND; a later reader causes two constant-folding losses, so exactness of the eight-input cofactor forces at least14 gates.

CanonicalTwoFilter.lean is110lines5662bytes, SHA2564c68849e8a015de9b46491d38ee02dedb66a692868e89cb7b480731485abe12b. DirectFilterCore.lean and SoleReaderFreeCore.lean are compatibility modules containing only the new namespace extensions from root's already checked bundled sources, with imports of their common bases; they avoid duplicate declarations when combined with RelaxationFloor. Their hashes are b56d9b5a9fbf23b5683e2085545b51d63e912a225ab23c99263e87ca8e50c4bc and f998ffe6d2a4144650ade4a7deb1cd4810b52c9d31bf395dc0910973c0831727. Independent review of this closed case was requested. These remain dependency tests, not final-submission format.

## Safe paid-NOT operands and prefixes avoiding the negative rail

SafeOperandImpossible.impossible is now checked for an arbitrary actual pre/NOT/post circuit of size at most18, with AND/OR prefix and suffix and the correct free-negative-input target semantics. If its actual NOT operand H implies the target, replacing NOT H bytrue preserves the output, and ForcedTrueCompile constructs a monotone circuit with at least one fewer gate. The checked Unary18 theorem then contradicts size at most17. No two-filter or reader-count hypothesis is needed once H is safe.

GlobalMonoFilterSafe checks that two distinct nonzero sole-filter factorizations and global monotonicity of H imply H is safe. SharedFilter reduces any unsafe accepted negative input to an accepted nonedge pair; PairLocalization says adding0 makes H false, contradicting global monotonicity. The same file proves global monotonicity for an actual AND/OR prefix that avoids free input10, provided the effective NOT operand is not that input.

TwoFilterNoNegativePrefix.impossible removes those semantic hypotheses entirely. It concerns any two distinct nonzero raw vertices v,w with direct sole AND(v,Q),AND(w,Q) readers of the paid NOT output, given by explicit post-list decompositions. If the NOT has at most one input, its prefix avoids free input10, the circuit has at most18 gates and computes the target, the theorem concludes False. The forbidden NOT operand10 is derived internally from singleton/zero rejection. No two-rail count is assumed. It checked and exported with exit0 and empty logs on2026-11-25 at17:01 UTC;65lines3416bytes, SHA25689ceb34e045817fc00885416c46782a304d4cf6e95ae38e3a793c1292be3169c. Therefore any remaining candidate with two such filters must read the negative rail before the paid NOT.

At the confirmed17:04:43 UTC lease loss, all work stopped. TwoFilterRailUsage.both_used and TwoFilterOutsideNeighbors.impossible had also checked and exported successfully: the former proves both rail uses from actual two-filter conditions, and the latter excludes the pair when one filtered vertex is outside N(0). The final composition of rail usage with TwoFiltersRailCount was only planned, with no source created. FRESH_PROOF_PAUSE_170443.md records final hashes, preserved logs, and the exact unfinished boundary.
