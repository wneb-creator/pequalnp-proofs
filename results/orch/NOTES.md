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
