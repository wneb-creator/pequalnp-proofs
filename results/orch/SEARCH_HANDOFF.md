# Counterexample-search handoff (final)

Status: no circuit below the posted125-gate bound has been found. Every target-sized artifact currently saved is explicitly INVALID. Heuristic timeouts and bounded-neighborhood UNSAT results are not proofs of the posted lower bound. Root owns the lease, final theorem, checker and submission.

## Exact targets and formal verification pipelines

|Problem|Inputs|Edges|Known baseline|Target|Lift overhead to plane|Complete raw extremal cases|
|---|---:|---:|---:|---:|---:|---:|
|Full projective plane|42|105|125|124|0|105+25,237 maximal negatives|
|Hyperoval K6 incidence|21|30|35|34|90|30+64|
|Alternative6 grouped core|19|24|29|28|96|24+64|
|Triangle9 core|27|45|53|52|72|45+512|
|Complement12 core|33|60|71|70|54|60+4096|
|K4 incidence plus private core|14|16|19 (computational)|18|106 (audited)|16+16|

The first five baselines and conditional lifts in this table have been Lean-checked separately. The K4-private baseline and lifting calculation were independently checked computationally; no Lean lift is claimed for that new core. Generic monotone finite-basis and symbolic DNF-table certificates are available. A concrete target-sized JSON gate list passing the complete scalar basis can be turned into a Lean result through those certificates; no such list is currently available.

## Search scope and completed conclusions

- General exact binary K6 size34 synthesis:1800-second cap, no verdict. Factored two-hidden-dirty plus6clean tops also timed out180seconds. Alternative6 generic/symmetry-reduced size28 searches likewise produced no target witness.
- Restricted factored K6 with1dirty+6clean AND nodes, size≤34, no shared linear OR: UNSAT1.27seconds. With2dirty+5clean nodes: UNSAT21.98seconds. These are restricted source-set models, not a complete normal form for arbitrary circuits. Sources and complete logs:search-v3/.
- Dirty C6 exact9-gate canonical/pruned model: UNSAT29.69seconds. C6 with3private leaves at12gates, including a4AND-restricted variant:60-second timeouts. Exact-size/pruning scope matters; these results do not exclude every smaller circuit. Sources/logs:search-completed-0940/.
- Alternative6 nearby seeds near-3-7,near-3-10,multi-dirty-near-1: UNSAT within6ordered-fan-in/operator edits. Multi-dirty-near-2 within8edits:180-second timeout. These exclude only the named neighborhoods; see search-completed-0940/ and nearby-search/.
- Triangle9 full404test nearby4edit neighborhood: UNSAT158.56seconds. Nearby8edit with≥2dirty heuristic:180-second timeout. Partial59test CEGIS nearby8/16edits timed out90/120seconds; no witness. See cegis-search/ and cegis-run-002/.
- Alternative6 CEGIS: initial25test models were SAT but INVALID on complete88basis (56/32/32errors in gradual run003). Refinement to31tests timed out. Fixed/adaptive/phase-transformed neighborhood trials at8/24edits also timed out; no UNSAT or target claim from these trials. Sources/logs:cegis-alternative6-completed/ and cegis-adaptive-phase/.
- Stochastic source-set searches tested latent dirty ANDs, pure/mixed OR sharing, valid mixed-cover/shared-sum/matching warm starts, and INVALID compressed biclique clusters. Best valid sizes stayed35/29/53/71/125 for the corresponding cores/plane. Complete per-run packages preserve all logs and artifacts.
- Physical fixed28gate beam repair tested single-wire changes, neutral associativity/distribution rewrites, and augmented singleton/nonedge-pair fitness. It has improved a singleton-rejecting positive-complete seed from56 to33raw negative errors; still INVALID. Reviewed whole-gate resynthesis and random two-gate moves were added; Jump013/014 produced the33error improvement from a nested clean-joint seed; all28gates are active and three dirty ANDs interact.

## Important invalid-seed caveat

The Alternative6 run008 positive-complete28gate/8error state exactly computes F OR input7 and accepts that singleton. Earlier unrestricted physical repairs reached25errors by accepting other singletons. Those are poor exact-repair seeds and are explicitly documented. Do not mistake small maximal-negative error counts for correctness or active multi-dirty structure.

Current best singleton-rejecting physical seed is scratch physical-repair-alternative6-014/improved-19.json, preserved in physical-jump-014015/:28gates,all24positive edges,33raw maximal-negative errors (43augmented fitness errors). Its complete wrong-input list is present. Minimum2diagnostic dirty gates is a heuristic beam restriction, not a formal necessary condition for arbitrary raw local circuits.

Full-plane run010 preserved two singleton-rejecting positive-complete seeds:122gates/18,863errors/2nontrivialdirty ANDs and121gates/23,464errors/5nontrivialdirty ANDs. These are in plane-run-010/ and are also INVALID. Ordinary near1–4 plane states have zero dirty ANDs and simply omit positive edges.

## Final new-core and run outcomes

The last small SAT core uses global points[2,3,8,15]: K4-incidence plus four private aggregates,14inputs,16edges,16positive+16maximal-negative tests,baseline19,target18. The baseline passed all101,640generated clauses and all16,384inputs. Twenty-four automorphisms and ten first-gate pair orbits were independently checked. The prospective106gate lift consists of4private aggregation ORs+17remainingstars×5+17output merges. These are computational checks, not a Lean target proof.

The unrestricted18gate canonical/pruned trial ended UNKNOWN at180seconds (141.48CPU). Follow-ups also ended UNKNOWN: exactly6AND180seconds/127.93CPU, exactly7AND with≥2dirty150seconds/121.79CPU, exactly8AND with≥2dirty150seconds/133.14CPU. These restrictions are explicit heuristics and exact-size/pruning scope is retained. An unpruned query was generated but not run, reserving memory for final Lean checks. Sources/data/complete logs are in k4private-search/ and k4private-counted-searches/.

Final local Nested011 completed1140.009seconds and37,085,184mutations, best29 with no28witness. Its47-entry manifest package alternative6-run-011/ contains44physical circuits (2valid≥29,42INVALID), all independently replayed on the254augmented cases, including the88complete raw cases. Constructor counters may include discarded preparation attempts and are not counts of annealing epochs.

Final global NestedLow012 completed800.231seconds and3,753,984mutations, best125 with no124witness. Its plane-run-012/ package contains21physical circuits (1valid125,20INVALID), complete raw mistakes, augmented error metadata and full stdout/stderr. All search workers stopped before12:00UTC; no further solver or stochastic worker was launched.

The best singleton-free positive-complete result from the physical trials requiring at least two nontrivial dirty ANDs remains the28gate33raw-error candidate in physical-jump-014015/physical-repair-alternative6-014/improved-19.json. Its three dirty ANDs interact, but its exact symbolic output contains24target edge pairs plus10wrong pairs. It is explicitly INVALID and cannot be used as a refutation.

All final computational packages require their recorded independent review before preservation. Root alone owns the final Lean statement, checker verdict, branch push, desk release and any submission. No accepted proof or refutation is claimed by this search handoff. Reproduction uses the frozen package sources, their explicit statement/core JSONs, Python3 and a local CaDiCaL executable; original absolute solver paths in logs are current-container-only.

Frozen 2026-11-24T12:01:05.608280+00:00.
