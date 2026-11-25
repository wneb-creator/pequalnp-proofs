# Source and evidence index

No file in this `results/` tree is the authoritative submission for L-meta-5012. The intended submission path is `lean/PEqualNP/Outside/L_meta_5012.lean`; only that file proving the exact posted statement and passing the repository checker would complete the gap. Results here are helper proofs, data, search programs, logs, and work notes.

| Files | Meaning and verification scope |
| --- | --- |
| `../lemmas/antecedent_cycle_six.lean` | Lean-compiled explicit eight-gate C6 circuit, exact function, AO2, empty junk, and graph properties. An upper bound, not minimum-size proof. |
| `../lemmas/antecedent_five_independent.lean` | Lean-compiled finite certificate lemma for every 3×3 Boolean matrix with fixed diagonal edges and no four-cycle. The 21 admissible matrices have five independent witnesses with diagonal conflicts. Kernel `decide` checks the table. |
| `../lemmas/antecedent_cycle_six_two_junk.lean` | Lean-compiled eleven-gate C6 circuit with exactly two junk gates, a clean top accepting a three-edge matching, and proof that this circuit is not least. It is not a refutation of the posted statement. |
| `../lemmas/structural_four_clause.lean`, `../lemmas/structural_matching_three.lean` | Separately compiled helper arguments: five witnesses obstruct four clauses, then a clean four-clause expression cannot accept three disjoint graph edges. Independently reviewed; hypotheses matter. |
| `../lemmas/master_surgery.lean` | Mechanical extraction of source `L_meta_5412.lean` through the completed `master_surgery_bound`, with only its namespace renamed. The bound retains leastness, lift-fixed-point, no-four-cycle, exact two-junk, and star-cover hypotheses. Build status belongs to its build log; extraction identity is not a proof of the final gap. |
| Other `../lemmas/*.lean` | Work by the other agents. Consult their exact statements and associated build logs. Presence here alone does not certify compilation or the final statement. |
| `antecedent_search.py`, `antecedent_batch.py`, `antecedent_lower_batch.py` | Original full-truth-table SMT circuit searches. Solver evidence only. Early model requests after UNSAT/UNKNOWN caused model-unavailable errors, documented in README. |
| `twojunk_critical.py` | Critical-row SMT search using edge pairs and maximal independent sets; SAT models receive a separate full truth-table post-check. Optional leastness pruning is explained in README and is not itself Lean-checked. |
| `twojunk_normalized.py`, `twojunk-normalized*`, `twojunk-control-*.json` | New exact-search variant with ancestor-bitset TopForm, at least one junk gate having a cleaner, and separate positive/negative support flags. Concrete controls pass; long runs and exact metadata/logs are computational evidence only. |
| `antecedent-graphs6.json` | Seven nonisolated 3+3 bipartite no-four-cycle graph types, modulo partition permutations and exchange. This census was independently reproduced. |
| `twojunk-five-independent-certificates.json`, `twojunk_product_matching.py` | Generator/data behind the 21 labeled matrices with a fixed diagonal matching. The corresponding Lean lemma checks the mathematical certificate; the Python program is exploratory code. This 21-case census differs from the seven-type census above. |
| `twojunk_common_filter.py`, `twojunk-common-filter-results.json` | Search that found the eleven-gate same-side two-junk C6 pattern, subsequently checked in Lean. |
| `overlap_cleaner_oracle.py`, `overlap-cleaner-oracle-results.json` | Finite tests of overlapping-arm cleaner claims on all 334 labeled 3+3 bipartite no-four-cycle graphs and all unordered pairs of arm sets. Computational evidence only; precise assumptions are recorded below. |
| `*.smt2` | Exact SMT inputs. They are not Lean proof terms or certificates accepted by the repository checker. |
| Remaining `*.json` | Search metadata, graph data, or candidate/certificate data. They are not authoritative theorem statements. |
| `*.stdout`, `*.stderr` | Complete command output snapshots. UNSAT is a solver result; UNKNOWN/timeout gives no exclusion result. An empty successful Lean log concerns the exact file version compiled at that time. |
| `../NOTES.md`, `../TIMELINE.md`, `README.md` | Human-readable progress, timestamps, scope, and limitations; not formal proof sources. |

The overlapping-arm oracle uses the exact maximal cleaner set W for g=(OR P) AND (OR Q). It confirms: overlap of size at least two implies |W|≤1; for singleton overlap r with BOTH arm sizes at least two, T=(W∩P)∪(W∩Q) has size at most one, is adjacent to r, and every guarded edge is covered by {r}∪T; a singleton arm directly covers all accepted pairs. The singleton-overlap small-T conclusion needs bipartiteness: a triangle is a counterexample without it. It also needs both arm-size hypotheses: a star with P={r} is a counterexample if that requirement is removed. Coverage alone is set-theoretic; graph assumptions bound the cover size.

- `geometric_clean_star_oracle.py` and `geometric-clean-star*`: finite counterexample search for a proposed stronger geometric dichotomy, not the posted theorem. Exact connected P4 witness is checked by `../lemmas/antecedent_star_dichotomy_counterexample.lean`, which explicitly proves its circuit is not least.

- `geometric_guarded_matching_oracle.py`, `geometric_union_cover_oracle.py`, `geometric_ustar_cover_oracle.py` and matching data/logs: finite tests of proposed geometric shortcuts, scoped in README and COUNTEREXAMPLE_SCOPE.md. None constructs or certifies a least circuit.
