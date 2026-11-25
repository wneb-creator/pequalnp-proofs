# L-meta-3566: certificate_search notes

Current task: search for a counterexample or a useful normalization argument for
the bipartite, C4-free graph-function peeling statement. No desk requests, git
writes, named-file edits, or Lean jobs are performed by this agent.

## Conditional repair route

`L_meta_8933.lean` proves the exact `|E| + |T| <= size + 1` lower bound when each
dirty AND gate is true on at most one globally reread edge. Its repair replaces
each dirty gate by a direct edge AND. Every read-once edge survives any such
replacement, and the uniqueness condition preserves the remaining edges.

The condition does not follow merely from graph geometry. The identity

`(u OR V) AND (v OR U) AND (u OR v) = uv OR uU OR vV`

computes a bipartite, C4-free double star with a dirty intermediate product and
multiple reread edges. It is one gate more expensive than the optimal star
cover. Thus global minimality must rule out amortizing this extra gate through
sharing around cycles. The existing 9,396-line `L_meta_8725.lean` proves only the
special case of exactly one dirty AND gate. I found no general normalizer.

## Structured search

`gadget_milp.py` constructs a finite function library on the complete extremal
sample: one positive row for every edge, and every maximal independent set as a
negative row. It includes linear ORs, dirty products, optional mixed operands
`dirty OR input`, and clean intersections. The MILP chooses one producer per
selected function, charges every shared gate, then covers every positive edge
by selected clean outputs, charging their final OR tree. Every returned circuit
is tested on all assignments before being reported as an improvement.

Independent audit: `../repo_review/gadget-milp-review.md` and
`../repo_review/gadget-library-audit.json`. The audited versions pass recipe
semantics, extremal-row completeness, active dependency closure, and acyclicity.
Clean nodes may refer to later nonclean node IDs; all nonclean dependencies
strictly decrease their IDs and never depend on clean nodes. Consequently the
exception remains acyclic. Recipe caps and the selected candidate layers are
incomplete search heuristics; a timeout is not a lower bound.

Completed first MILP: the 11-vertex, 14-edge graph `bip5x6_14` has cover number 5
and a known 18-gate upper bound. A 120-second search for 17 gates timed out with
no feasible witness. Data and complete diagnostics: `bip5x6-gadget.json/.log`.

Heawood's initial library has 434 clean functions and 8,380 retained candidate
recipes. The local extraction analysis found 77 ordinary stars at their cover
upper bound, 189 double-star variants one gate above that bound, and 168 other
functions four gates above it. The largest support has five edges. Files:
`heawood-library.json`, `heawood-local-analysis.json`.

The expanded 5x6 library has 541 clean functions and 10,722 retained recipes.
Its mixed operands are `dirty OR input`; local best extracted candidates still
have no cost below their cover upper bound. Files:
`bip5x6-mixed-library.json`, `bip5x6-mixed-local.json`.

`gadget_greedy.py` performs randomized, sharing-aware extraction from this
library. It can exploit a previously selected intermediate wire when adding a
new clean output. It verifies every strict improvement on all assignments.

Next expansion: common-guard factoring `Q AND (D1 OR D2 OR D3)`. Conjunctions of
at most four OR clauses cannot exactly realize an induced 6-cycle, which explains
why the earlier local clean gadgets are forests. Factored dirty sums permit
larger cyclic supports while sharing the final AND.

The factored-sum expansion produced 625 clean functions, including four cyclic
supports, and 17,999 retained recipes. The cheapest individually extracted cyclic
functions remained six gates above their cover upper bound. Independent audits
also checked the expanded library and the new `gadget_sat.py` backend. The SAT
backend recovered an 8-gate C6 circuit and exhaustively checked it in under 0.2s.

## C8 with one free linear output

New subproblem from root: inputs `b,c,d,e,Z,W,T,U` (indices 0 through 7), edges
`04,05,16,17,24,26,35,37`, and a free helper `B = x0 OR x1`. A circuit with at most
10 additional gates would give the desired graph counterexample after extension.

`formula_dp.cpp` performs exact minimum-formula DP on all 2^18 possible truth
vectors over the complete extremal sample. Initial input variables and B have
cost zero. It also searches all root OR/AND decompositions, counting shared
canonical subexpressions once. The first run examined 226,017,806 pairs in under
one second: no formula of cost at most10; first formula11; canonical-root DAG11.
This is untrusted computational evidence, not a Lean lower-bound certificate.

`helper_batch.py` tested all65 distinct one-gate extra helpers. It treats each
helper as free, searches a residual budget9, then pays for the helper. All65
cases finished in31.8s; best reconstructed circuit11, no counterexample.

`helper_sweep.py` extends this to helpers with2–4-gate minimum formulas. It merges
the helper construction and residual circuit by their sample truth vectors,
prunes unused gates, and fully checks all256 assignments before reporting any
strict improvement. There are407 cost2,1660 cost3,5339 cost4 helper functions.
All files and per-case complete diagnostics stay in this scratch directory.

Completed: all2067 cost2–3 helper functions, with every intermediate signal free,
gave best additional gate count11. The two batches are
`c8-helpers-2-3-all-results.json` and `c8-helpers-2-3-all-part2-results.json`.
An independent full-circuit reconstruction/audit of these cases and the65 first
helpers checked2130 unique256-row truth tables and found no positive private-leaf
amplification profit.

All four geometrically safe C8 input ORs are `(0,1)`, `(2,3)`, `(4,7)`, `(5,6)`.
With all four free, exact formula DP and canonical root sharing still give11.
All110 further one-gate helper functions also give best additional count11;
independent amplification audit of all110 returned maximum profit0.

The Graph11 recipe SAT was extended to give literal OR(7,10) and OR(8,9) zero
paid cost, while forcing those exact input-OR producers. Its120-second run timed
out without a witness: `graph11-free-helper-sat.json/.log/.solver.log`.

`large_helper_sweep.cpp` is a native bounded search over137233 semantic helper
functions of minimum formula cost4–7, with all four safe C8 ORs free. For a helper
of cost d it searches residual formulas of cost at most10-d with that helper as
one free wire. Any found result is reconstructed with one copy of the helper,
so it has at most10 paid gates before the independent full-truth/extension audit.
This exhausts the stated single-shared-wire formula class, not all circuits.
Counts by helper cost4,5,6,7 are10872,26140,43996,56225. A10-second benchmark checked
477 cost4 cases. The full run has a600-second cap and writes all progress to
`c8-large-helper-sweep.log`, its completion summary to
`c8-large-helper-summary.json`, and any witness immediately to
`c8-large-helper-witness.json`.

Completed native run: all137233 cases,419.036 seconds, no candidate. The exact
completion counts match10872,26140,43996,56225 for costs4,5,6,7 respectively.
Independent source review confirmed the formula recurrence and reconstruction;
this remains an untrusted bounded-class negative result, not a Lean theorem.

The randomized extractor now has `--helper-objective`, reusing the independent
`gate_elimination/reusable_helpers.py` audit. It rewards compatible safe helper
supports during selection and scores completed circuits by actual private-leaf
amplification profit. This variant is prepared but has not run yet.

## Latest completed helper-objective and observed-helper controls

Graph11 helper-objective greedy extraction completed 1347 attempts in 120.089 seconds. Best actual independent amplification score was 0, with an 18-gate standard circuit. Complete outputs are graph11-helper-objective.json and graph11-helper-objective.log.

The new observed-helper SAT mode forces compatible exact literal-OR helper outputs, keeps their OR trees selectable, charges every actual gate, then raises the raw gate budget by the sum of (support size minus one). It verifies each observed helper on every old assignment in witness decoding. Geometry checks enforce bipartiteness, no four-cycle, same-side supports, no old vertex neighboring two vertices in a support, and pairwise support intersections at most one. A valid five-vertex path control with observed OR(0,4) returned a fully checked six-gate raw circuit, paid size five (the baseline).

The prepared K3,3 incidence target has 15 inputs, 18 edges, vertex-cover size 6, and baseline 23. Its eight compatible safe triples have total helper overhead 16. The planned observed-helper query therefore seeks raw size at most 38 and paid size at most 22. This would yield a counterexample after private-leaf star amplification. The expanded graph can have 31 inputs; do not enumerate its full truth table. Verify the original 15-input circuit and exact helpers, then use symbolic amplification.

The K3,3 library does include genuinely dirty AND sharing: of its 1,489 active nodes, 128 are linear, 51 direct clean products, 1,130 dirty products, and 180 guarded clean functions. All 1,130 active dirty products have an AND recipe and accept graph-false independent rows. For example, node 249 is AND(node 15,node 31) and accepts assignment 63, which selects all six original K3,3 vertices and no edge-vertices. The 231 clean functions mentioned in generation statistics are only candidates for final OR terms, not a restriction on intermediate AND gates.

The K3,3 exact observed-helper query returned UNKNOWN at its 120-second solver cap (73,860 variables, 153,877 clauses); no witness. Its logs/result are subk33-observed-sat.*.

For a stronger absorbed-helper query, gadget_helper_library.py adds every singleton and every maximal independent set in each graph induced by deleting a helper support. These rows suffice to enforce OR(S) <= h <= OR(S) OR F for monotone h. gadget_relaxed_sat.py selects one qualifying helper per support and verifies both inequalities on all old assignments for every decoded witness. The small source gadget_absorbed_library.py additionally builds h=OR(S) OR edge for each graph edge before guard enumeration. The resulting subk33-absorbed-direct-library.json has 181 rows, 4,040 nodes, and 98 helper candidates (8 literal plus 90 absorbed). Its nonclean-to-clean dependencies go only to direct single-edge nodes, which receive no later guarded recipes because try_clean requires at least two positive edges. A P5 control with three possible helpers passed full truth verification, raw six/paid five gates.

An alternative expanded-linear generation was interrupted with SIGTERM after producing 80,327 dirty products; its complete partial log is subk33-absorbed-library-generation.log. It yielded no circuit or logical conclusion and is not used.

The reviewed K3,3 absorbed-helper SAT query also returned UNKNOWN at 120.866 seconds (77,812 variables, 162,437 clauses, 98 helper choices). It produced no witness. Exact source/library checks, inputs, full solver log, and result are preserved; this is not an UNSAT result or a general lower bound. At completion there is no worker running from certificate_search and no counterexample has been found.

A final distinct helper family consists of all 24 safe OR-pairs of the K3,3 incidence graph: six among its original vertices and eighteen among disjoint edge-vertices. It is not mixed with the observed triple family. The pair library keeps ordinary paid triple OR functions as available internal nodes, but only the 24 pair outputs receive helper credit. The independently audited library has 4,274 nodes, 6,415 retained recipes, 233 complete sample rows, and 348 qualifying helper functions. All recipes have correct signatures and the union DAG is acyclic, depth ten. Strict targets are raw size at most 46 and paid size at most 22; full amplification would have 63 inputs, 90 edges, vertex-cover size 30, and at most 118 gates versus baseline 119.
