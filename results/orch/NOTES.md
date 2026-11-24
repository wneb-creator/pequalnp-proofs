# L-meta-2584 orchestration notes

Held by pilot-39. Root alone manages the lease and submissions.

## Assignment

Four-cycle-free incidence: replace any AO2 circuit by a no-larger read-2 circuit. Exact statement is stored in scratch statement.txt.

## Strategies

- combinatorial_route: graph/star-cover lower bound and existing lemmas.
- circuit_route: size-preserving normalization and explicit construction.
- counterexample_search: edge cases and finite experiments.
- status_review: prior L-meta-1035 and reductions eligibility.
- toolchain_setup: recover absent pinned toolchain and Mathlib cache.


## Counterexample and finite-case route

ReadK uses one jointly bounded proof tree for each prime implicant. It does not mean bounded fanout. IsAO2 requires exactly two earlier wires but permits a missing output. Empty incidence graphs have no prime implicants, so the read-2 condition is vacuous and cause no edge-case obstruction.

A stronger statement saying the original circuit itself must be read-2 is false: compute xy, then AND with x twice; the only tree uses x three times. Replacing by the original one-gate xy circuit resolves this.

Finite experiment (not Lean checked): Exhaustively generated all fan-in-two AND/OR circuits through four gates on 5 inputs, and through five gates on 6 inputs, omitting semantically duplicate wires (eliminable in a minimum circuit). No four-cycle-free bipartite incidence function beats the candidate star-cover cost |E| + tau(G) - 1. This checks all 54 four-cycle-free labeled 2-by-3 graphs and all 189 four-cycle-free labeled 2-by-4 graphs, including empty graphs with cost zero. The six-input run enumerated 174,325,200 final-depth gate sequences.

Source: /tmp/oec/pequalnp-pilot-39/counterexample/exhaust_small.cpp. Complete logs result-2x3.txt and result-2x4.txt in that directory. The bound has not been proved in Lean. A minimum vertex cover supplies a partition into nonempty stars, giving a natural read-1 (hence read-2) circuit with |E| + tau(G) - 1 gates. This suggests separating a circuit lower bound from an elementary star construction, though the lower bound remains the genuine hard part.

## combinatorial_route 2026-11-24T18:01:18.935289+00:00

- ReadK uses joint count vectors, not separate scalar minima. IsAO2 has exactly two backward operands, but permits an absent output (constant false).
- Candidate in scratch combinatorial/Prime.lean: incident pairs are exactly prime implicants; ReadK equivalently checks each incidence pair; C4-free complete bipartite subgraphs have a singleton side. 107 lines, waiting for toolchain.
- Canonical star cover is MetaComplexity.coverCircuitB; size/function proof available for copying from Outside/L_meta_3243.lean, model/structural proof Outside/L_meta_3245.lean. Root and circuit_route notified.
- Full conjecture is stronger than known read2 lower bounds; no existing normalization result found among the ReadK-related files. The lower-bound route would require circuit cost at least star-cover cost; not established.

### circuit_route — 2026-11-24T18:03:38.450119+00:00
Constructed uncompiled FlatRead.lean in /tmp/oec/pequalnp-pilot-39/circuit-route. Generic result: AO2 circuits whose AND operands lie in OR-only wire regions are read-2. Uses checked word semantics from L_meta_2466 plus reverse capped-vector encoding and proof-word length ≤2. Added separated_isReadTwo matching the structural conclusion of L_meta_3245 for coverCircuitB. This can finish read-2 of any canonical star-cover construction. Missing full-gap step remains size-preserving flattening of arbitrary C4-free incidence circuits. No reductions:true flag for current gap; root has sole lease.

### combinatorial_route literature check 2026-11-24T18:04:34.560536+00:00

Read 2026-11-24 via built-in web only: Stasys Jukna, Notes on Boolean Read-k and Multilinear Circuits, https://web.vu.lt/mif/s.jukna/ftp/readk-rev.pdf. Abstract states: “read-2 (∨, ∧) circuits can be exponentially smaller than read-1 (∨, ∧) circuits.” Definition is the same joint monomial degree notion as ReadK. Section 9 treats higher read hierarchy as open. No quadratic or C4-free normalization result found in this text.
Local notes/note-1-edge-function-exact-size.md limits the checked exact |E|+tau−1 theorem to long-thread graphs/forests/cycles; it does not claim all C4-free graphs. Thus generic star-cover-cost lower bound remains a genuine missing argument.
Existing same-size top-form normalization is checked Outside/L_meta_1501.lean (about 1120 lines); communicated to circuit_route. Known normalization stops before resolving junk blocks.

### Extended finite evidence

Exhaustive 2-by-3 search now reached five gates (26,560,320 final-depth sequences), checking all 471 syntactically distinct irredundant circuits at the star-cover optimum across the 54 four-cycle-free graphs. Every such optimal circuit is read-2. This is evidence for the stronger all-minima-read-2 conjecture, not a proof beyond these finite graphs.

Installed a scratch-only standalone Z3 5.3.3 release obtained from GitHub. Exact circuit synthesis for C6 has returned UNSAT at six gates (7.64 seconds) and seven gates (52.93 seconds), and SAT at eight gates (4.25 seconds), with an independently checked truth table/read-1 witness. The search assumes no semantically duplicate wires and all gates live, valid for minimum circuits; it orders adjacent independent gates by truth table to reduce isomorphic orderings. A separate eight-gate search forbidding read-2 on one edge is still running. Source synth_cycle.py and full SMT2/logs under scratch counterexample directory. None of these solver results is Lean checked.

### C6 all-optima test

Z3 returned UNSAT at C6 size5 (0.99s), size6 (7.64s), size7 (52.93s), SAT at size8 (4.25s), and UNSAT at size8 under the requirement that the distinguished edge has no joint read-2 tree (111.85s). C6 is edge-transitive, so the tested stronger property holds throughout its minimum circuits under this encoding. Fewer than five gates cannot depend on all six input variables. The evidence is computational and not Lean checked.

For larger cycles, synthesis is compressed to minimal-positive inputs (edges) and maximal-negative inputs (maximal independent sets). Those inputs characterize a monotone target: any true input contains an edge, any false input lies inside a maximal independent set. Semantically distinct intermediate wires on the compressed inputs can be required for a minimum circuit, because replacing a duplicate by its earlier representative preserves the compressed output tests and hence, by monotonicity, the entire final function. The circuit itself is evaluated on all assignments to independently verify any SAT model. C8 uses 18 such assignments rather than256.

### circuit_route checked component — 2026-11-24T18:07:13.993006+00:00
CoverRead.lean compiles exit0 with no diagnostics; full logs scratch circuit-route/build-003.stdout and .stderr. 688-line component includes generic flat_isReadTwo, separated_isReadTwo, and canonical_cover_isReadTwo. All statements use only Defs/Mathlib; structural helpers adapted from L_meta_3245 and word semantics from L_meta_2466, under own L_meta_2584 namespace. Root notified immediately for merge/push.

### Lean-checked C6 witness

The explicit eight-gate C6 circuit found by SMT has now compiled in pinned Lean with kernel decide only. Scratch CycleSix.lean defines the cycle incidence relation and circuit, then checks size8, AO2, no4cycle, the exact incidence function on all64 assignments, and the full IsReadK6 circuit2 property. It imports only Mathlib and PEqualNP.Defs and uses namespace PEqualNP.Outside.L_meta_2584.CycleSix. No native evaluation or new axioms. Complete build stdout/stderr are empty and process exit0. This is an existence witness, not the general L-meta-2584 theorem or a Lean lower bound. Root notified for immediate integration/push.

## structural_route 2026-11-24T18:10:14.746961+00:00

- Lean checked `one_junk_isReadTwo`: any TopForm AO2 circuit computing a simple graph edge function and having exactly one dirty AND gate is read-2. No leastness or C4 hypothesis needed.
- Key induction: a wire whose only possible AND ancestor is g has proof words of length one, or length two plus implication g => wire. If both operands of a below-function AND have length-two words, g implies the function, contradicting dirtiness. Thus all output words have at most three leaves. Singleton rejection bounds each variable multiplicity by two.
- Standalone candidate scratch structural/OneJunk.lean (compilation build-005, exit 0; no output). Integration fragment structural/one-junk-fragment.txt uses stable circuit_route FlatRead word machinery and its short_isReadTwo lemma.
- This does not prove general normalization: circuits with two or more dirty AND gates remain open.

### combinatorial_route checked helpers 2026-11-24T18:11:36.601397+00:00

Prime.lean (Defs only) checked: incident pairs exactly prime implicants, pair/cardinality/read equivalences, C4-free complete bipartite block is a star with |A||B|=|A|+|B|−1.
Graph.lean checked: incidenceBit and incidenceGraph encoding, posted C4-free premise implies TopForm.NoFourCycle, exact graphFun equality to incidence target.
Essential.lean checked: generic Support.essential_count for any fanin≤2 circuit; singleton rejection and both incident endpoints essential; point_star_size_bound and line_star_size_bound; generic incidence_active_size_bound (#active points + #active lines ≤ gates+1). Checked with Lean4.36.0, empty stdout/stderr. Integration fragment: scratch combinatorial/essential-fragment.txt.
Next bridge: if every line belongs to at most one point, point rows are disjoint stars and canonical cover budget is exactly #active points+#active lines−1. Circuit agent packages this full special case.

- Extension 2026-11-24T18:12:01.256934+00:00: also checked `no_junk_isReadTwo` and `at_most_one_junk_isReadTwo` (junk.card ≤ 1) in structural/build-007, exit 0. Additional74-line integration fragment structural/zero-junk-fragment.txt.

### Least/top-form structural hypothesis tests

Exhaustive optimal 2-by-3 circuits: all 471 have zero dirty AND gates (an AND is dirty if true on some input rejected by the target). The stronger per-cone condition therefore holds throughout those cases. For C6, a separate exact synthesis query required eight gates, top form, and one top AND cone containing at least two dirty AND ancestors. It returned UNSAT in70.34s. Below-target tests use maximal independent sets, and cone ancestry uses actual circuit wiring. Circuit-route agent notified.

Larger searches were inconclusive: C8 size9 and size10, and theta(3,3,3) size12 with a failed read2 edge, hit240s solver timeouts. C8 size11 positive synthesis also timed out at120s despite its known canonical witness, showing the search limit is substantial; no lower-bound or counterexample claim follows from those unknown results. A separate CaDiCaL CNF run on C8size10 is underway. Complete sources, SMT2, CNF, stdout, stderr remain in scratch/counterexample.

### combinatorial_route full star-forest subcase 2026-11-24T18:14:14.646729+00:00

Checked star_forest_replacement: arbitrary P,L and incidence I with every line incident to at most one point; every exact AO2 circuit C has a no-larger read2 replacement. Proof combines all nonempty point rows as canonical owners with active-input lower bound. Double-count identity star_forest_edge_count converts row-degree sum to active-line count. Includes empty incidence and isolated vertices. Addition-only fragment: scratch combinatorial/starforest-fragment.txt. Combined candidate StarForest.lean exits0; warnings only inherited CoverCertificate deprecations.

- 2026-11-24T18:14:29.730474+00:00: checked auxiliary counterexample structural/TwoJunk.lean (two-junk-003 exit0): five inputs/eight gates, C4-free two-edge star function, AO2+TopForm+exactly two dirty ANDs+pairwise distinct gate functions, but not read-2. Also checked explicit two-gate AO2 read-2 replacement. This refutes only automatic read2 from TopForm/semantic distinctness, NOT the posted existential replacement statement.
- Finite semantic check: all C4-free bipartite graphs on 3x3,3x4,4x4 inputs having at most four maximal independent sets have each nonisolated vertex in at most two of these sets. Counts:214/728/2249 eligible graphs. This supports a separate four-clause CNF read2 lemma via concept-lattice classification; not Lean checked. Full program/logs structural/four_clauses.py and four-clauses.stdout.

### Search closure

The independent CaDiCaL run on bit-blasted C8 size10 also reached its wall-time cap without a SAT/UNSAT conclusion. No running counterexample-search process remains. Deliverables: kernel-checked CycleSix.lean; exhaustive small-case source/logs; exact SMT queries and models; C8 CNF and both solver logs. Main logical conclusion remains only finite positive evidence. The general L-meta-2584 normalization has not been proved or refuted by this route.

### circuit_route central obstruction — 2026-11-24T18:16:10.511951+00:00
Compiled TopFormCounterexample.lean: 4-input 6-gate circuit for a 3-edge path, AO2 and C4-free and TopForm, but not read2. Gates (points a,c; lines b,d): g0=a OR c; g1=b OR d; g2=g0 AND g1; g3=b OR c; g4=g3 AND g1; g5=g2 AND g4. The two dirty gates are g2,g4; edge ab necessarily reads b three times. This is not least (a four-gate star cover computes it), so it does not refute L-meta-2584. It rules out deriving read2 merely from TopForm or from two nonnested dirty gates. Counterexample_search reports all471 optimum2x3 circuits have zero dirty gates and C6 optimum8g with≥2dirty below a top is UNSAT; no general leastness proof yet.
Checked synthesis fragments: cover-fragment.txt packages exact size/function + read2 into replacement_of_star_cover; star-fragment.txt and line-star-fragment.txt specialize to P=1/L=1 from degree budget. Combinatorial_route supplied both lowerbounds and starforest generalization.

### status_review fresh route assessment 2026-11-24T18:16:45.507434+00:00

Checked prime_short_isReadTwo (one short supported witness per prime implicant, not all words). Checked CnfSix:15gate C6 prime-CNF, TopForm,3dirtyANDs, jointread2false but scalarbounds2 true onpair{0,3}; not a refutation since8gate read2replacement exists. Scratch files status-review/prime-short-fragment.txt and CnfSix.lean; full successful logs retained. Strongest useful target is per-edge joint witness, allowing(2,2); global shortword/starcover normalization is stronger. Primary-literature scope checks and exact URLs/date in results/orch/status-research-001.md. Generic single-level normalization is false, but published saturated-graph examples do not meet our bipartite C4-free premise.

- 2026-11-24T18:17:32.137743+00:00: checked stronger `one_junk_per_top_isReadTwo`: TopForm+exact graph function, and each top AND strict cone contains at most one dirty AND, imply read-2. Dirty gates may be arbitrarily numerous globally. Scratch ConeJunk.lean, cone-junk-003 exit0 (one style warning); fragment cone-junk-fragment.txt.

## Combinatorial route: circuit-side sharing restriction (2026-11-24T18:20:53+00:00)

Checked `Sharing.lean` and stable addition-only `sharing-fragment.txt`, 443 lines, imports Mathlib and Defs only. The new `Sharing.shared_or_region_center_unique` says: in AO2 C for a C4-free graph G, if two top AND operands OR-reach one gate g with at least two distinct inputs in its OR shadow, then any leaves from the opposite operands are equal (both operand orientations supported). No leastness needed. This uses the actual `OrReaches`, `orIn`, `side`, and semantic `BelowF` via `tops`, rather than an abstract rectangle premise. `shared_or_region_center_union_card` bounds the union of all such opposite leaves by one. Added `orIn_value`, `orIn_subset_of_orReaches`, `top_sides_adj`, `top_sides_disjoint`, and `top_sides_star`. Minimal OR-set/evaluation infrastructure adapted from existing L1490, copied locally because outside imports forbidden. Compile exit0 with empty stdout/stderr after deprecation cleanup. Remaining central gap is replacement/cost argument for junk AND sharing; this result permits nontrivial pure OR sharing only within a single center.

### circuit_route guarded erasure CHECKED — 2026-11-24T18:21:52.877877+00:00
Stable integration fragment: /tmp/oec/pequalnp-pilot-39/circuit-route/guarded-erase-fragment-v1.txt (namespace only; no imports). Full snapshot GuardedErase-checked-v1.lean, compilation erase-004 exit0. Main result erase_guarded_and constructs renumbered AO2 D with same function and smaller size if erased m=(u AND v) has all readers AND guarded by fixed earlier wire p implying v, and output is not m. Corollary erase_shared_factor supplies guard from an earlier p=(a AND v). least_no_shared_factor proves this pattern impossible in a least AO graph circuit. No C4 requirement, so this is a general circuit-minimality obstruction.

## Two-dirty core attempt 2026-11-24T18:24:02.513117+00:00

- CHECKED semantic classification for incomparable dirty gates: `four_clause_double_star` in structural/DoubleStar.lean (double-star-001 exit0, no diagnostics). Model has a pure point clause A, pure line clause D, and two mixed clauses B/E and C/F. A bad read2 edge has point signature1110 and line0001. Under C4-freeness and soundness on pairs plus two-point/one-line triples, every accepted block edge lies at the distinguished point or at one common line.
- Proof: distinguished point is universal to block lines. C4-freeness makes cross edges between two noncentre point/line pairs false. The two mixed-clause signatures must complement each other; then those two points with the distinguished line satisfy the block. C4-freeness forbids either target incidence, contradiction.
- Independent counterexample agent enumerated normalized4-clause blocks below C4-free targets, confirming classification on3x3,3x4,4x3.
- Remaining size issue: a double-star edge set has a read2 construction, but extracting the point-star side may require intersection of two existing OR regions. Naive reconstruction can add a gate; deleting or reusing a private guard is still necessary for no-size-increase.

## Counterexample route, second pass

C6 plus pendant line (P=3,L=4), 9 gates:
- CaDiCaL UNSAT 61.59s with TopForm, at most2 dirty ANDs, no private same-operation child deletion, and failure of read2 on any edge.
- CaDiCaL UNSAT 71.04s after removing all three extra restrictions.
- Both queries keep minimum-circuit reductions: no dead gates, no equal critical-row wire functions, ordered commutative operands, canonical adjacent-independent gate order. Critical rows are all7 positive edge assignments plus6 maximal independent sets. Results are solver evidence, not Lean proofs.
- Redundant Z3 constrained query was terminated deliberately after CaDiCaL solved that exact CNF; exit143 is not a solver verdict.

Controls: explicit9gate star witness computes target on all128 inputs, is read2, has no dead/duplicate gates, is TopForm, and passes local irreducibility detector. Prior6gate path obstruction computes its graph on all16 inputs and is correctly identified as having2 possible private-child deletions. Full models and independent verification JSON saved.

Random sampling: 1,000,000 seven-input,9gate samples yielded43,359 distinct live subcircuits at their graph's star-cover budget, across269 C4-free graphs; no read2 failure. A separate10,000,000 samples up to12 generated gates yielded302,844 such subcircuits across474 graphs, again no read2 failure. Dead gates were pruned for size accounting. These samples are not exhaustive.

Four-clause block exhaustive check: normalized forced3+1 edge signatures, complete truth tables, every C4-free target with that edge.
3x3:139,078 below-target cases, zero double-star or center-line violations.
3x4:3,330,266 cases, zero violations.
4x3:3,932,080 cases, zero violations.
Structural agent was notified and is independently formalizing the double-star statement in Lean.

No running search processes remain. No general proof or refutation is claimed.

- 2026-11-24T18:30:55.300672+00:00 circuit_route: reader-specific AND-factor erasure checked (ChoiceErase-checked-v1.lean, choice-003 exit0). Each later reader chooses either earlier operand; rewritten readers must remain below the target on false inputs, and their other operands precede the removed AND. Preserves AO2/function and saves one gate. Stable 207-line fragment choice-erase-fragment-v1.txt. least_no_choice_and wrapper also checked (ChoiceLeast.lean, choice-least-003 exit0; 29-line choice-least-fragment.txt). Full arbitrary-junk gap remains open.

## Combinatorial route: semantic sharing and pruning (2026-11-24T18:31:31+00:00)

Checked packages in `/tmp/oec/pequalnp-pilot-39/combinatorial/`: `sharing-semantic-fragment.txt` strengthens OR-shadow uniqueness to all singleton-accepted inputs, including AND regions; `sharing-more-fragment.txt` proves BelowF/output have empty OR input shadows and BelowF propagates along OR reachability; `pruning-fragment.txt` proves a monotone function below graph/incidence F that accepts every edge pair equals F. `mixed-sharing-fragment.txt` says mixed-color singleton support forces opposite top operand singleton support empty; `bipartite-mixed-fragment.txt` proves point/line have no common incidence neighbor.

Current stronger application checked together in `FactorReader.lean`, exit0 with empty factor-reader-v2 logs: `pure-pruning-fragment.txt` proves pure-OR value completeness and that AND of disjoint same-side OR shadows is false on every incidence pair; `factor-choice-fragment.txt` proves sound line×OR(A)×OR(B) must have all A or all B adjacent to line, plus chosen factor soundness; `factor-reader-fragment.txt` connects this to actual binary AND gate and direct AND reader, handling both operand orientations. Circuit agent composes this with reader-specific gate erasure. These three newest fragments use lemma, not theorem, keywords.

Spawned one child `/root/combinatorial_route/forced_semantics` (root notified for measurement), which checked forcedCircuit OR[] replacement preserves AndOrOnly, lowers all wire values, and agrees with original whenever selected original gate is false; equality needs no reads-back or gate-validity assumptions. Child also checked exact graph/incidence target preservation if selected gate is false on all edge pairs. Stable fragments under combinatorial/forced; counterexample_search owns smaller AO2 constant propagation, so no mechanism overlap.

## Checked false-gate constant propagation

FalseElim.lean compiles with pinned Lean, exit0 and empty logs. It replaces a selected gate by OR[], propagates false constants using Option Nat wire statuses, and emits only binary AND/OR gates. The invariant simultaneously gives status bounds, value preservation, and new-circuit backward references. An empty source gate necessarily emits no gate, proving strict gate-count saving.

Export FalsePropagation.eliminate_false_gate: given IsAO2 n C and j<C.gates.length, returns an AO2 circuit D with D.size+1≤C.size and exactly the function of C with gate j forced false. The forcedCircuit definition is definitionally equal to Sharing.forcedCircuit from the semantic-comparison agent. No new types/instances, no native evaluation, only Mathlib/Defs imports. Full source and empty logs in scratch/counterexample; integration fragment false-elim-fragment.txt uses relative namespace FalsePropagation for insertion inside L_meta_2584. Root notified immediately for review/push.

- 2026-11-24T18:32:53.244345+00:00: CHECKED pure-point-factor obstruction in structural/PointFactors.lean (point-factors-002 exit0). Soundness of three point OR factors times each line forces one entire factor into that line neighborhood. C4-free incidence permits each nonsingleton point factor at most one line-center. Therefore a common-point three-factor block has at most three lines, or one factor is exactly the common singleton. This is a semantic/counting subcase; global gate accounting with shared factors remains open.

### status_review absorption rotation and exact read-vector bridge
Timestamp: 2026-11-24T18:33:05.251426+00:00
- Independently Lean-checked a same-size adjacent private-OR absorption rotation: old h=OR(x,a), g=AND(h,b) becomes h=AND(a,b), g=OR(x,h), assuming all x,a,b precede h, x implies b on all prefix evaluations, the private h is not the output, and no suffix gate reads h. Full Boolean function is preserved; AO2 and gate count are preserved.
- Proved the stronger syntactic fact: every old output proof word has a new output word that is a sublist. Consequently every good joint read-two list remains good. This syntactic result does not itself require Boolean dominance; dominance is necessary when asserting the same function.
- Decoded every library read vector back to an actual proof word (AO2 circuits), with exact capped counts. Obtained exact equivalence of readsAtMost C n S 2=true and existence of a proof word supported on S with every S-coordinate count at most two. This proves generic word-sublist simulation preserves IsReadK 2 under equality of functions.
- Frozen checked fragments in /tmp/oec/pequalnp-pilot-39/status-review/: rotation-fragment.txt, rotation-words-fragment.txt, vector-decode-fragment.txt, read-word-criterion-fragment.txt, rotation-read-fragment.txt, read-list-sim-fragment.txt, rotation-list-fragment.txt. Final combined scratch RotationList.lean compiled with exit zero; full logs rotation-list-002.stdout/stderr. Parent is integrating fragments into the single target.
- The main gap is still open. No lemma establishes that every non-read-two least C4-free circuit admits a private-OR rotation or another strict witness improvement. Shared OR gates and absence of a global dominance relation are the unresolved cases. A minimality proof still needs a finite/well-founded witness potential plus a structural existence theorem; the checked rotation and preservation lemmas supply only the local transformation and preservation parts.

## Structural recovery singleton frontier bridge — 2026-11-24T18:40:43.103244+00:00

CHECKED `SingletonFrontier.lean` (frontier-001, exit0, empty stdout/stderr). If every dirty AND has nonempty singleton support, every operand of a top AND has nonempty singleton support under AO2+TopForm. Therefore a wire accepting singleton vertices with no common graph neighbor cannot OR-reach any top operand. This supplies the missing semantic frontier exclusion for the two-incomparable-dirty mixed-factor configuration, where the dirty gates accept singleton p0 and singleton l1. It does not yet provide gate deletion or the full replacement. Stable addition-only fragment: scratch structure-recovery/singleton-frontier-fragment.txt.

## Composition recovery 2026-11-24T18:42:04.876714+00:00

CHECKED minimum-pure-fragment.txt: singleton-intersection alias erasure preserves exact incidence by the monotone pair sandwich; minimum pure-point AND gates therefore have at least two common OR-shadow inputs and at least two singleton witnesses. Depends on prior AliasErase and alias-pair fragments. Full snapshot composition-recovery/MinimumPure.lean uses Mathlib/Defs only, build-002 exit0.

Child or_context checked factor choice through arbitrary OR-only contexts and exact value characterization of pure-OR opposite operands under shared-centre uniqueness. Singleton-centre information alone is insufficient for dirty opposite contexts: for points s,t,a,b; lines l,k1,k2; edges sl,sk1,tl,tk2,al,bk1,bk2, set g=(s∨t∨a)∧(s∨t∨b), h=l∨(k1∧k2). Then g∧h is below the incidence function and singleton supports are {s,t} and {l}, but replacing g by the first factor is unsound on {a,k1,k2}, and replacing it by the second is unsound on {b,l}. This semantic obstruction is not yet Lean-checked and does not refute the posted least-size replacement statement.

- 2026-11-24T18:43:07.782814+00:00 structure_recovery CHECKED unique AND frontier and actual private-reader bridge (frontier-005 exit0, empty logs). `two_dirty_mixed_unique_frontier` proves only h can have an operand OR-reaching mixed c when dirty gates are g/h, both singleton-supported, and c is not in g cone. `singleton_region_not_output` excludes output. `unique_frontier_private_reader` upgrades this to every direct reader of c equals h, assuming h has inputs [n+c,d], d does not OR-reach c, and each gate OR-reaches output or an AND operand. The latter liveness premise is assigned to composition/or_context. New stable fragments unique-frontier-fragment.txt and private-reader-fragment.txt depend on singleton-frontier-fragment.txt. No full gap proof yet.

### Composition recovery refinement 2026-11-24T18:46:22.253504+00:00

CHECKED incomparable-fragment.txt: remove any gate equal to an earlier wire; minimum pure-OR AND factors have incomparable OR shadows; together with singleton-intersection elimination, every minimum pure-point AND requires at least four distinct point inputs. Incomparable.lean, incomparable-002 exit0.

CHECKED productive dirty-opposite obstruction in DirtyOpposite.lean, dirty-003 exit0 and empty diagnostics. Replace the earlier informal h by l∨(k1∧(k2∨s)); added term sk1 is an edge, preserving block soundness. The eight-gate AO block has singleton source support {s,t}, singleton opposite support {l}, and every gate accepts some edge pair, yet either source-factor replacement is unsound. It is not claimed exact for the target or least, and does not refute L-meta-2584. Stable fragment dirty-opposite-fragment.txt.

Independent source/format review of Reorder and structure singleton/unique/private/least-privacy fragments: PASS within partial scope; saved results/orch/review-009a.txt. No claim of full theorem acceptance.

## Root replan 2026-11-24T18:53:57.543075+00:00

Known TopForm prerequisite recovered from checked L-meta-1501: least AO circuit for nonempty graph normalizes at same size and same dirty-gate count. Adaptation in scratch topform-recovery compiled, with generic exists-least-TopForm and one-dirty least-circuit replacement wrappers. This is prior checked work, not a new solution of the hard block problem.

Parallel work now targets concrete two-dirty surgeries: structure proves pair coverage for alias plus lifted star, review agent proves explicit same-size constructor, composition handles singleton-empty complementary cases, and full-gap team proves zero-overhead pure-point intersection-two replacement plus minimum-AND normal form. These remain conditional special cases. No argument yet extracts an applicable configuration from EVERY non-read2 minimum circuit with arbitrarily many dirty gates. Even complete two-dirty classification will not by itself prove the posted statement.

Actual checker rerun on checkpoint010 returned REJECTED (no-theorem), exit1. Reduction submission remains unavailable: latest public gap row has no reductions:true. No PR has been opened.

## Empty singleton support composition 2026-11-24T18:54:45.306397+00:00

CHECKED empty-operand-fragment.txt (empty-003 exit0): in TopForm with only two possible dirty ANDs g/h and singleton(g) nonempty, any top operand with empty singleton support OR-reaches h and has exactly h's Boolean function. This follows from the checked OR-frontier decomposition plus all-true evaluation. A mixed-singleton region c cannot OR-reach a clean top operand if c and h are simultaneously true on some false graph input; the opposite operand would equal h. In particular, this excludes mixed roots dominated by dirty h, and internal mixed regions with a suitable pure-line counterexample assignment.

Promising but UNPROVED circuit replacement route: for two incomparable dirty gates g=A·B,h=C·D and a bad p0/l0 edge with p0 in A∩B∩C, if a line m lies in A∩B∩D, soundness forces C pure-point with every C-point adjacent m; D is pure-line adjacent p0. Pair support of g·h is a double-star centered p0,m. Replacing g by OR[p0,m] is globally shrinking and uses the same gate count. Since g has mixed singleton support, any clean opposite top context equals h by the new checked lemma. Thus lost edge pairs should be impossible; implementing the general changed-gate comparison remains work. Then only h is dirty and the checked one-junk result applies. This is restricted to two incomparable dirty gates and does not solve arbitrary dirty count.

Other explicit same-cost local recipe: if g=A·(p0∨m), h=C·D with A,C pure-point ORs, choose E=A or C wholly adjacent m by soundness on {a,c,m}; replace the three AND gates with p0·D, m·E, and their OR. It preserves all old block edge pairs and remains below the target. Global sharing of the repurposed dirty gates still needs accounting. No single-star collapse is claimed when the clauses contain arbitrary mixed line parts.

## Structural recovery global coverage — 2026-11-24T18:56:08.699150+00:00

All following fragments are frozen and Lean-checked together in AliasCoverage.lean, alias-cover-001 exit0 (full stdout/stderr retained). `coverage-frontier-fragment.txt`: actual OR evaluation reaches an input or AND frontier; per-top critical edge through h lies at the chosen star centers. `cone-frontier-fragment.txt`: under TopForm and only incomparable dirty g/h, any h dependence of a top is an OR path to one operand. `forced-avoid-fragment.txt`: forcing an AND false preserves all wires outside its ancestor cone, preserves old OR paths, and preserves true output when a selected true top avoids it. `pair-preservation-fragment.txt`: forced-h-false output is true on graph edges outside both centers. `star-sound-fragment.txt`: a pure OR region whose leaves neighbor u gives a sound u-star and supplies edge-line adjacency. `alias-cover-fragment.txt`: any alias output f equal to C when h=input-v and dominating forced-h-false covers every edge together with u AND old d. This is the exact semantic coverage interface required by AliasSurgery.repair_private_pair.

Scope remains explicit: AO2, TopForm, exactly two possible dirty ANDs g/h, h not in g cone, singleton-supported h, selected pure cofactor d, neighboring star center u, and g*h double-star edge classification. It does not prove the full arbitrary-dirty gap or extract such a configuration from every non-read2 circuit. Orientation matters: if the noncentre line belongs only to B/E, erase G=A*B using alias p0 and lift the line-star; the graph-general coverage lemmas support swapping sides.
