# L-meta-4970 semantic review

Read-only statement/definition review, 2026-11-25. No desk calls, proof-source edits, or new mathematical claim of a solved gap.

The exact statement asks for a vertex cover S with `E.card + S.card <= C.size + 1` for a C4-free bipartite graph. Its circuit is `TopForm.IsAO2`, computes the edge function, has `TwoColour.tCount = 0`, and contains a semantic star-OR witness for each edge.

## Definition checks

- `lean/PEqualNP/Defs/TopForm.lean`: IsAO2 means AND/OR only, strict backward reads, and exactly two inputs per gate. Repeated operands are allowed. It does not assert that the output is last, that the output exists, or that every gate reaches the output.
- `lean/PEqualNP/Defs/TwoColour.lean`: tCount counts OR gates whose OR-only reach contains both input colors. Reach stops at every AND gate. T=0 does not mean every OR computes a function of only one color: an idempotent AND gate can hide an input from OR-only reach.
- The posted star witnesses are semantic equalities on every Boolean input. A witness may have AND gates in its ancestry; equality with a pure OR is not a syntactic OR-tree assertion.
- Witness gates only have to exist. No cone, reader, centre-AND, or relevance-to-output requirement occurs in the hypothesis. Witnesses may be dead gates appended after the output.

## Concrete flaw in the supplied counting sketch

Take p=1, l=2, E={(0,0),(0,1)}, and input indices 0,1,2. Use these gates in order:

1. AND(0,1), giving wire 3.
2. AND(0,2), giving wire 4.
3. OR(3,4), giving wire 5, the output.
4. OR(1,2), giving wire 6, unused.

This computes the two-edge star, satisfies IsAO2 and T=0, and the final dead OR supplies Q={0,1} for both edges. No AND gate reads that witness: every AND precedes it. Thus the sketch's claimed correspondence between a witness star OR and a centre-AND is not a consequence of the premises. This is a direct finite semantic example, not a Lean-checked artifact and not a counterexample to the statement: its four gates exceed the required lower bound of two.

## Cases and review obligations

- E empty gives the conclusion immediately with S empty.
- An isolated single-edge component cannot satisfy the star-witness premise: each witness requires at least two distinct neighbors at one endpoint. This excludes some small graphs but does not make the full statement vacuous.
- For nonempty E, correctness rules out an input or missing output, because the edge function is false on all singleton inputs and true on an edge input.
- Any gate-count ledger must justify its charges without assuming witnesses are used, pure-OR ancestry, distinct witness gates for different edges, or a particular output position.
- C4-freeness does imply uniqueness of a star centre for a fixed neighbor set of size at least two. It does not by itself show that all ancestral gates have a unique centre, especially when AND gates reduce singleton support.

No refutation has been established. These are obligations for proposed proof routes, not evidence that the posted conclusion is false.

## Frozen partial: SupportBudget

Reviewed `gap4970/sat_encoding/SupportBudget.lean`, SHA256 `39024ed2f2f3056bff56dc112abba2d60f5c5f85e1cf378f5118a43523051752` (234 lines, 10,368 bytes). Its wire-execution helpers from `wireStep` through `wireValue_or_pair` are byte-identical to the corresponding 117-line block of L_meta_7649. The new `merge_pass_bound` is a finite union budget: labels outside the charged set are singleton-sized or contained in one earlier label; charged labels may be contained in the union of two earlier labels. Strict index descent makes pass-through steps free and each binary union costs at most one.

Both successful compile logs are empty. The actual outside guard reports only the missing posted top-level theorem. The file is approved as a partial; the required semantic connection from the circuit/star assumptions to a sufficient counting ledger is not yet proved.

## Computational archive checks

The frozen dead-star manifest's four files match their recorded hashes and sizes. Independent evaluation checked all 64 Boolean inputs, every semantic star witness, strict backward binary gates, C4-freeness, T=0, and minimum vertex-cover size 3. This six-cycle circuit with three extra dead opposite-side star ORs has 11 gates and satisfies the posted lower bound of 8. Its six available star components leave only five other gates, disproving the stronger proposed ALL-components ledger `remaining >= K + tau - 1`. This is computational evidence against that auxiliary claim, not a Lean-checked refutation of L-meta-4970.

All 40 files in `auxiliary-checks-manifest.json` and all 32 files in `completed-small-probes-manifest.json` match their hashes and sizes. Independent positive-control checks evaluated all 64/16384/256/1024 inputs for C6/Fano/C8/subdivision-K4 and verified all 826/17385/12049/28262 saved CNF clauses against the saved SAT assignments. C8 and subdivision-K4 controls also have valid semantic star witnesses, T=0, and minimum cover size 4.

The finite hiding example preserves all 64 truth rows and every renamed wire, changes size 14 to 37, hides T=3 to T=0, and appends three dead pair ORs. It validates that finite transformation example only. The C++ exhaustive search's bounds and circuit counts were inspected for three inputs through five gates and four inputs through four gates; no search was rerun. C6-and2 reports computational UNSAT (exit 20), while both Fano-and6 probes and the C8/subdivision-K4 lower probes report UNKNOWN (exit 0). None is a kernel-checked certificate or a proof/refutation of the posted statement.

## Stochastic search controls

The 51 files in `stochastic/presearch-manifest.json` and six files in `stochastic/stop-aware-manifest.json` match their frozen hashes and sizes. The original engine SHA256 is `7291c99a8027567a523e07c8858286d3611190a8dbe7605457d5fe4d6eddc328`; the stop-aware engine SHA256 is `e34df079fffeba8533eedf530ec0a76136b8daf4eb138b025e8c2c9c0709516a`. The latter changes cancellation and reporting only. STOP is polled at iteration checkpoints, with elapsed-second throttling; it is not a strict one-second response guarantee.

The engine allows dead gates and duplicate operands. T=0 uses raw OR reach with AND barriers. A gate is classified as semantic OR(Q) using its singleton support Q and its value on the complement of Q; for a monotone function these two checks characterize that equality exactly. Fitness evaluates every graph edge and maximal independent input, sufficient for correctness of a monotone edge function, and every proposed successful candidate additionally receives a full-input check. No inference of UNSAT or exhaustive coverage follows from this stochastic search.

An independent bitset evaluator checked all 15 frozen positive controls on every Boolean input: three circuits each for subdivision-K4 (1024 rows), irregular11 (2048), each Fano deletion graph (4096), and cubic16 (65536). Strict backward binary gates, exact function, T=0, every semantic star witness, C4-freeness, and minimum vertex covers were verified independently. Costs are the required lower bound, bound plus one, and bound plus two. All controls passed. Full review outputs are `/tmp/oec/pequalnp-pilot-99/review-stochastic-controls.json`, `.stdout`, and `.stderr`. No long search was rerun.

## Actual checked partial and conditional transfer

The 909-line `PostedEdgeBound.lean`, SHA256 `ae68dec66a8597198f79ee6e9b367a5df8be1fd77599520b72297fea44f493c1`, is an exact standalone composition of the independently reviewed SelfChargedBudget, Neighbourhoods, EdgeSupportCard, and PostedWitness bodies. It derives `E.card <= 2 * orWires.card` from the exact posted AO2, C4-free, and star-witness assumptions. Correctness and T=0 are not needed for this weaker conclusion. It does not establish the required cover-plus-edge gate bound.

The 1873-line `StrengthTransferStandalone.lean`, SHA256 `9c58f3b3c4d3ef48c2fcff24ebd04918790c3550c3cfce16ed73fb3842a9322e`, is an exact composition of reviewed Shield, Neighbourhoods, PairDecomposition, AppendPairs, and StrengthTransfer bodies. Its Posted definition is the exact desk statement, used as an explicit hypothesis. The resulting implication for nonempty C4-free graphs with even left degrees is `E.card + 2 * cover.card + 6 <= 12 * C.size`. This is a conditional consequence, not a proof of Posted and not an admissible reduction submission. Both standalone sources compiled; their guards reject only the absent final posted theorem.
