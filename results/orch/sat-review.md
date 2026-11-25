# Independent SAT encoding review

No gate-semantics or bit-ordering bug was found in the reviewed encoders. The current SAT searches are useful counterexample searches, but their UNSAT results concern restricted circuit classes and are not a proof of L-meta-2592. No encoder or solver was changed during this review, and no SAT or Lean run was started.

The posted statement permits at most 19 gates and requires at least one syntactic NOT gate. `FanInTwo` allows zero, one, or two inputs, repeated inputs, arbitrary wire indices, and arbitrary output indices. Missing wires evaluate to false. The search encodings instead use earlier wires, exactly two distinct operands for AND/OR, unary NOT, and usually exactly 19 useful gates with exactly one NOT. These restrictions require separate normalization arguments before any exhaustive UNSAT result can settle the posted statement. In particular, pruning an unused NOT can destroy the hypothesis that a NOT is present.

## Semantics and finite checks

The mux clauses force each selected input value to equal its source wire. The guarded operation clauses implement AND, OR, and NOT in both directions. The source-order clauses enforce `a < b` for AND/OR and `a = b` for NOT, so the redundant NOT right selector cannot make activity constraints claim an unrelated dependency.

Independent Python checks, without invoking a solver, passed:

- All 24 operation/input/output cases for the three gate truth encodings.
- All 1024 assignments for the six-core decomposition: core vertices `[0,1,3,7,8,9]`, satellites `[2,4,5,6]`, the three matching edges, and the four listed OR triples.
- All 128 assignments of the residual target. `v[9]` is the third triple, which is exactly the neighborhood of original vertex 5; this index is correct. A prose name such as “J” should not be interpreted as the fourth list entry.
- Both fixed 20-gate circuits compute the complete Petersen edge function.
- The near-19 circuit has exactly the advertised wrong rows `[138,385,521,770]`; its NOT output, wire 12, is unused.
- The listed graph has 120 automorphisms. The pair `(0,1)` has an orbit of 15 edges, while `(0,2)` has an orbit of 30 nonedges.

Inputs use little-endian masks consistently: mask bit `k` is input `k`, agreeing with the definition of `tableIndex` and with the order of `List.ofFn`.

Complete finite-check output is saved at `/tmp/oec/pequalnp-pilot-98/sat-review-checks.stdout`.

## Symmetry and activity

The lexicographic ordering of consecutive `(maximum fanin, minimum fanin)` pairs in `synth_ordered.py` is a valid symmetry reduction for the unrestricted all-active DAG class. Greedily select the ready gate with the smallest pair. A gate that becomes ready after this selection uses the newly assigned, larger wire number, so its maximum fanin cannot precede the selected pair. Previously ready gates retain their pairs. If every gate reaches the single output, the output gate is necessarily last.

This argument allows gate renumbering. It does not justify combining the ordering with arbitrary fixed gate positions, a fixed first-gate orbit representative, or a distance bound around a particular numbered seed. Those combinations remain deliberately restricted searches. The exact-synthesis agent explicitly confirmed this limitation.

Requiring every nonoutput gate to feed a later gate does ensure reachability to the final output: follow the strictly increasing indices. The corresponding multioutput clause similarly ensures reachability to some designated output. These clauses exclude a syntactically present but unused NOT, which the posted statement allows.

The fixed first-gate representatives cover AND/OR on an edge or a nonedge, plus NOT of a primary input, under the unconstrained Petersen automorphism action. This fact alone does not make their combination with canonical gate ordering exhaustive.

## NOT-count conventions

In `synth.py`, `synth_connected.py`, `synth_ordered.py`, `synth_distance.py`, `multi.py`, `multi_relaxed.py`, `multi_relaxed_orbit.py`, the star scripts, and `residual.py`, values other than 0 or 1 mean **at least one NOT**, not exactly that many. The `multi_relaxed_count.py`, `multi_tiny.py`, and `multi_pairs.py` variants implement exact positive counts greater than one. The agent confirmed that the exact-three-NOT experiment used the count variant and that `residual5anynot` intentionally uses the other convention.

The ban on a NOT at the final output is valid for a nonconstant monotone target with exactly one NOT: the preceding circuit is monotone, so its complement cannot be the target. It is not complete for two or more NOTs. The agent confirmed that connected/ordered/distance runs so far use exactly one NOT. Star-output bans are likewise justified for the current one-NOT runs by the empty assignment and an increasing singleton witness. Do not carry those bans unchanged into unrestricted multiple-NOT searches.

The distance encoding correctly enforces an upper bound on changed numbered gates: an unmarked gate must preserve all three seed fields; a marked gate may also remain unchanged. Because the near-19 seed has an unused NOT, the all-active restriction requires the repair to activate or replace that structure. This is a search-neighborhood restriction, not a truth-encoding error.

## Safe additional pruning

For exactly one NOT, every primary input on which the target has an increasing witness must have a directed path to the output avoiding NOT. Otherwise every dependence on that input passes through the unique NOT: its prefix is monotone in the input, its complemented value is antitone, and the remaining AND/OR circuit preserves antitonicity. This contradicts the increasing witness.

Encode a structural reachability bit for each primary input and wire: inputs have the corresponding unit vector, AND/OR take the union of the selected fanin vectors, and NOT resets the vector to empty. Require all ten bits at the Petersen output. For the relaxed multioutput search, require the three relevant bits at each star output and all six at the matching output; their increasing witnesses are already in the care domains. The weaker primary-NOT cut is to require another gate to consume that primary directly.

This NOT-reset rule is specific to at most one NOT. For multiple NOTs, a safe generalization tracks positive and negative path parity separately and swaps them at NOT; a positive dependency may pass through two negations.

The exact-synthesis agent proposed the stronger reachability cut during review, and the argument above independently checks its mathematical validity. It is still an ordinary mathematical review, not a kernel-checked normalization theorem.

For performance, the combinatorial at-most-distance clauses are correct but grow quickly as the distance bound rises; a sequential cardinality encoding is an option if that becomes the bottleneck. The present small count bounds are not an observed correctness problem. Fixed seed loaders should normalize commutative operands before imposing literal source selectors; the currently reviewed seed files are already normalized.

Reviewed source hashes and UTC time: `/tmp/oec/pequalnp-pilot-98/sat-review-sources.json`.

## Incremental driver addendum

Reviewed `/tmp/oec/pequalnp-pilot-98/exact/incremental.cpp`, SHA256 `8ce83a315eb17a495b3a627c5dd28b668c4a4356e88dbe139f1f62b7c391566f`. No compilation or solver run was performed.

The positive-path CNF is correct: NOT forces false; otherwise the output reachability bit is equivalent to the union of selected fanin bits. All 16 Boolean cases of these clauses were independently checked. The sample muxes and Boolean gate clauses preserve the earlier semantics. Structural selectors are frozen before solving and reused when new row variables are added. Every candidate is checked on all 1024 rows before WITNESS is written. The matching CaDiCaL header states that conflict limits apply to the next solve and reset afterward, so the repeated conflict-limited solve loop is consistent with its API.

The combined first-gate constraint `left=0`, `right∈{0,1,2}`, operation free, is sound together with canonical gate ordering in the unseeded normalized model. If a primary NOT exists, map its input to 0. Otherwise, if an input-only edge gate exists, map that edge to 01. Otherwise map an input-only nonedge gate to 02; both 01 and 12 are edges and therefore absent in this final case. Greedy canonical ordering then picks one of the five represented gate types. Fixed numbered seeds still require a separate symmetry argument.

Defensive limitations: this driver uses exact NOT counts, unlike the legacy any-NOT convention. A negative count such as -1 produces an empty clause, and sufficiently out-of-range counts or fixed-file indices can cause invalid indexing. Validate `m>0`, `0≤notcount≤m`, and trusted fixed-gate bounds before broadening its CLI use. Current supplied positive counts and fixtures are in range. The encoded-sample consistency diagnostic currently examines only the first four selected bad rows; checking the entire bad-row list before selecting four would detect any future encoding error sooner. Neither issue changes the correctness of the currently reviewed valid-argument runs.

## General signed-path cut

The proposed cut is sound for any number of NOT gates: every coordinate with an increasing output witness must have an output path containing an even number of NOTs. Track two sets per wire. An input has its own coordinate in the positive set and an empty negative set; AND/OR union each sign over their effective inputs; NOT swaps the sets of its first effective input. Require positive membership for each essential coordinate of the monotone target. This permits paths containing two or four NOTs and therefore extends the one-NOT search correctly.

For a fixed input coordinate, hold the other input values fixed and prove these two implications simultaneously in evaluation order:

1. No positive path implies that the wire value is antitone in the coordinate.
2. No negative path implies that the wire value is monotone in the coordinate.

They hold for primary inputs and constants. For AND/OR, absence of the relevant sign implies its absence in every effective child, and each Boolean operation preserves the corresponding order. For NOT, absence of positive paths means absence of negative paths at its child; the child is monotone, so its complement is antitone. The other direction is the same argument with the signs exchanged. A monotone essential target has some false-to-true coordinate change with output false-to-true; antitonicity contradicts that witness. Full global monotonicity is unnecessary when such a witness is supplied directly.

This argument also matches the library's broader gate semantics:

- Empty AND is true and empty OR is false; both have empty positive and negative sets.
- Unary AND/OR copy the signs, and repeated operands cause no issue because the combination is set union.
- NOT reads only its first argument. An empty NOT is true. A second argument, if supplied, is ignored and must not be treated as an effective dependency.
- A missing or forward-referenced wire is false at that evaluation step and has no dependencies. The recurrence follows `Circuit.wires` evaluation order rather than treating forward indices as later-resolved edges.
- A missing output is false; an output selecting a primary input uses that input's sign sets.

Do **not** require the negative output set to be empty. A monotone function can contain odd paths that cancel or are absorbed, for example `x OR (x AND NOT x) = x`. Positive-path existence is necessary; the absence of negative paths is not necessary.

Independent finite corroboration checked all 5,859 two-gate circuits on two inputs, allowing every AND/OR/NOT arity from zero through two, repeated operands, ignored second NOT operands, and missing/forward wires. Across 35,154 output choices and 70,308 coordinate checks, both induction invariants and the essential-monotone consequence held. Output: `/tmp/oec/pequalnp-pilot-98/signed-path-review.stdout`. These finite checks support the general structural argument; they are not a Lean proof or a verdict on the posted gap.

The exact-synthesis agent has been told the cut is valid, including the ignored-argument and negative-path cautions. Review of its eventual CNF implementation is separate from this mathematical validation.

Implementation review: the updated `incremental.cpp` signed-path block (lines135–153; SHA256 `a369ddc90d0e94d6a7ecdb66e6ce5a4c97ee0b88cb76e439cb8a77ad674c8ce0`) correctly muxes both signs, swaps the selected left signs at NOT, and unions corresponding signs at non-NOT gates. Only positive output membership is forced. All128 Boolean assignments of the ten guarded gate clauses agree with this recurrence. The constructor invokes this block only for NOT counts at least2, retaining the earlier one-NOT cut and allowing a final NOT in the multiple-NOT cases. Input-domain/fixed-index guards and the complete encoded-sample diagnostic requested in the earlier review are now present. No new semantic issue was found. No solver, compilation, or Lean run was performed in this review.

## Priority among first-gate orbits

The proposed strengthening is sound for any NOT count in the unseeded normalized Petersen model: prioritize a primary NOT if any exists; otherwise prioritize an input-only edge gate if any exists; otherwise use an input-only nonedge gate. These existence properties are invariant under graph automorphisms and gate renumbering. The same representative argument maps the selected primary NOT to NOT0, an edge pair to 01, or a nonedge pair to 02. Canonical ordering then puts the chosen class first.

With the existing first-gate constraints `L₀[0]` and `R₀[0] OR R₀[1] OR R₀[2]`, the proposed clauses implement this correctly. For each later gate and primary input, `¬NOTᵢ OR ¬Lᵢ[k] OR NOT₀` forces the primary-NOT case when needed. For each input edge `a<b`, `NOT₀ OR ¬Lᵢ[a] OR ¬Rᵢ[b] OR R₀[1]` enforces the edge case when the first case is absent. No operation guard is needed in the second clause because a unary NOT cannot select distinct `a<b` under the existing shape constraints. This is a symmetry reduction within the normalized search class, not an additional normalization theorem for the posted Lean statement; fixed numbered seeds still fall outside the completeness argument.

## Seven-input C6 wrapper review

Reviewed `core13_reach.py` (SHA256 `b890fae7faa5b2ddc9f5d3d5b8510cf652e4af40fb7d611152bbe99446025da3`) against `core13.py` (SHA256 `fb9187a14e7d7c8a9b9cb9ac9b40e0293fa17198c30aa96af124825fdb85c952`). The reach mux implications are bidirectional under the base one-hot selectors. The six guarded union clauses and four guarded NOT clauses exactly implement sign union for AND/OR and sign swapping of the first operand for NOT. The wrapper forces only positive membership at a selected output; it does not forbid negative reach. No valid candidate of the base search model is excluded by these sign constraints.

All15 required output/coordinate pairs have increasing witnesses in their care domains. Each OR-triple coordinate uses zero and its singleton, both outside the residual C6 edge predicate. For residual output coordinates1–6, fix one cycle neighbor true and toggle the selected coordinate; the residual output is constrained on all128 inputs. Coordinate0 is correctly not required for the residual output. Therefore partial care domains do not undermine the necessity argument. The wrapper was not executed and no solver or Lean build was run. The base model's existing normalized-circuit and fixed-first-gate limitations remain unchanged.
