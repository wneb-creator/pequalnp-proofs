# Pilot 71 research report

Job: msg-9d45b31e1d52e8587cfb2214. Branch: pnp/pilot-71.

The posted L-meta-2962 inequality is not proved or refuted. The named 856-line partial compiles with `lake build PEqualNP.Outside.L_meta_2962`, but the local checker rejects it with `REJECTED (no-theorem)` because the required final theorem is absent. See [complete build output](partial-build-output.txt) and [complete checker output](checker-partial-output.txt). No proof PR has been opened. The full-proof cleanup prerequisites were not met; named-file line count remains 856 before and after.

## Checked reusable results

The named partial contains cover-extension algebra, singleton and matching special cases, and a concrete equality case. Additional standalone Lean artifacts under [lemmas](lemmas/) establish leaf-union counting, star-forest and disjoint-cone conditional bounds, an AND ancestor for each core, and a positive cyclic example. These are partial results with explicit hypotheses, not the posted theorem.

The absorption wrapper appends `(F OR x) AND F` to an exact graph-function circuit. Separate checked artifacts establish semantic and AO2 preservation, positivity of both read-vector coordinates below a graph function, the read-twice property of the wrapper, and append/cone/maximality helpers. The combined core, singleton maximal-core/full-cone, and general dominance artifacts each have their own compilation output and validation. A 43-line matching-cover certificate proves minimum cover size without enumerating all subsets. Each artifact is standalone; copied helper declarations mean they should not all be imported together without consolidation.

The [prospective two-charge reduction](lemmas/ProspectiveGateCut.lean) compiles only conditionally. Its two hypotheses remain unproved. The authoritative public gap row has no `reductions: true` flag, checked again at 07:58 UTC, so this artifact is not an eligible reduction submission.

## Main research obstruction

The lift-fixed condition applies only to the actual output cone, whereas maximal cores include dead gates. The absorption wrapper can therefore hide an arbitrary exact circuit in a dead maximal core. A reviewed informal construction, amplified through three disjoint copies, shows that the posted bound implies the unrestricted exact monotone gate lower bound `size(C) >= edges(G) + minimumCover(G) - 1` for every bipartite graph with no four-cycle. A converse compression argument was also reviewed. The whole equivalence is not Lean formalized; see [charging notes](lemmas/core-charging.md) and [counterexample notes](lemmas/core-counterexample.md).

This explains why proofs restricted to formulas, single-level circuits, bilinear circuits, or disjoint cones do not resolve the stated quantifiers. Historical literature is cited with its actual model restrictions; current status of broader literature questions is explicitly unverified.

## Computational evidence

The searches include random and guided circuit generation, exact finite SAT encodings, free-AND and free-OR relaxations, and exact-function circuit minimization. Several small cases are UNSAT and several positive controls were replayed on all inputs. Those ordinary computations are not Lean proofs of the general claim. Evaluation counts can include duplicates. Timeouts are UNKNOWN, and reconnect-killed runs are INTERRUPTED_NO_VERDICT.

The two final exact Fano26 queries completed their 900-second limits with UNKNOWN. The structural campaign records 10 SAT examples or controls, 30 finite UNSAT results, 23 timeouts, and two interrupted runs; none settles the posted claim. The first exact-function heuristic phase completed 900 seconds with no candidate, evaluating 2,236,744,869 theta and 2,236,740,000 Fano circuits including repeats. The final 300-second subgraph phase also found no candidate: 671,904,308 theta and 671,880,000 Fano evaluations, including repeats. Its 381,599,173 exact matching checks produced no strict gate-count saving. All searches are now stopped.

Complete available stdout/stderr, source, parameters, and per-run status records are preserved in [searches](searches/), the compact [free-AND evidence](lemmas/free-and-2962/), and [counterexample archive](core-counterexample-evidence.tar.gz). Hash manifests describe preserved bytes. Consult individual records for the precise scope of each finite exclusion.

## Desk and delivery history

L-meta-1035 was already not open when checked. Initial L-meta-2602 work stopped after the first renewal returned HTTP 410, despite the advertised expiry; no other pilot lease was released. The [full diagnostic response](desk-2602-renewal-error.txt) is preserved. Three null replies then preceded assignment of L-meta-2962 at 06:06:37 UTC; [desk history](desk-history.txt) preserves their exact messages. Active lease identifiers are not published.

Every independently reviewed compiled component was committed and pushed to the fork branch. All pushes are research preservation, not accepted proofs. The checkpoint lease status and elapsed time are recorded in [validation](validation.txt) and [timeline](TIMELINE.md).

Sub-agents: status_review, structural_proof, counterexample, lemma_search, single_core, combinatorial_bound.
