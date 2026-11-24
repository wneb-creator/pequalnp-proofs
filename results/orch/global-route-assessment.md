# Global route assessment: L-meta-2584

Worker: global_second. Started about 19:08 UTC on 2026-11-24; one child,
witness_descent, implemented the two local lemmas. Root was informed for the
overall subagent count. Root owns all desk, Git, build, and submission actions.
This assessment is frozen for handoff. Detailed intermediate notes remain at
`/tmp/oec/pequalnp-pilot-39/global-second/NOTES.md`.

## Outcome

No complete proof or refutation was found. The two checked local purification
lemmas are useful partial results and do not establish the posted statement.
The broad normalization obstacle is mathematical, not a missing Lean API.

The exact missing ingredient is a global descent theorem: from an exact
C4-free incidence circuit which is minimum in size, then AND count, then junk
count, and which fails read-2, derive a legal circuit preserving the target
while decreasing that lexicographic measure. Current local moves only work
after extracting special structure. There is no proof that a general
non-read-2 circuit has at most two dirty gates, a private repair region, a
common-line configuration, or a gate with at most one globally critical edge.

The positive-edge projection of a gate is always pointwise below its old
function and preserves its positive edge profile. What is missing is the cost
bound for realizing that projection through shared OR circuitry. Singleton
support does not control joint-only terms already containing valid edges;
those terms make the naive opposite-center/neighbor charging invalid.

## Checked deliverables

- `EdgePurification.unique_edge_purification`: accepted-edge uniqueness.
  119 lines / 5334 bytes, SHA256
  `25ca8857a6abbe962fa34579f7307690ce5b686b41b61d9aa64067559bda5ecf`.
- `CriticalPurification.unique_critical_edge_purification`: uniqueness only
  among globally essential edges, detected by forcing the gate false.
  79 lines / 3878 bytes, SHA256
  `12325917416d062e00b48b3999fd158255c500e508d2c07d95b25354986e6333`.

Both fragments are in
`/tmp/oec/pequalnp-pilot-39/global-second/witness-descent/`.
Both preserve AO2, circuit size, AND count, and exact target functionality,
and prove new junk is contained in old junk with the selected gate erased.
Strict junk reduction additionally assumes that gate was dirty.
Both compiled successfully and were axiom-audited: only propext,
Classical.choice, and Quot.sound. Full independent reviews are
`review-edge-purification.txt` and `review-critical-purification.txt` beside
this assessment. Root must verify the integrated source.

## Additional precise observations

In a minimum circuit, a singleton-bearing gate cannot have all critical edges
incident to that singleton: aliasing it to the primary input would preserve
all positive pairs by the forced-false lower bound, globally decrease the
circuit, and permit deletion. Thus indispensable joint-only edge terms are a
real obstruction to singleton aliasing.

If g accepts singleton point set S and g AND h is below the target, every
independent assignment accepted by h contains a neighboring line for each
member of S. When S shares line l and that assignment excludes l, C4-freeness
forces at least |S| distinct lines in the assignment. A gate-budget deduction
from this large witness remains unproved because internal circuitry may be
shared with the positive edge terms that must be retained.

The critical-set viewpoint can combine with an all-frontier alias rule only
after finding a frontier whose replacement is pointwise below the old gate
and still accepts every globally critical edge. For arbitrary dirty chains,
the indispensable joint-only edge terms can lie outside the singleton
frontier, so the present invariants do not establish that coverage. A proof
for a pure two-dirty region would be valuable but cannot be iterated over an
arbitrary circuit without proving the required region exists and that
rewiring preserves the other shared contexts.

Critical edges do not have to form a star under C4-freeness and TopForm alone.
The three-edge matching has an exact prime CNF with eight clauses, choosing
one endpoint from each edge in each clause. Every proper conjunction is
dirty; every conjunction gate is critical for all three disjoint edges;
every edge's output parse repeats each endpoint four times. A direct binary
implementation uses 23 gates versus a 5-gate DNF. This is only an obstruction
to a local lemma without minimum-size hypotheses, not a counterexample to
the posted statement.

## Research checked

Read 2026-11-24: Jukna,
[Disproving the single level conjecture](https://web.vu.lt/mif/s.jukna/ftp/single1.pdf)
and [Graphs and circuits: some further remarks](https://web.vu.lt/mif/s.jukna/ftp/dagstuhl2006.pdf).
The former's separation uses saturated non-bipartite extensions. The latter's
small CNF constructions only represent graphs on pairs. Neither supplies the
needed exact C4-free normalization. The former's historical Problem 8.2
also emphasizes the gap between formula lower bounds and unrestricted circuit
lower bounds for quadratic functions; no present-day open-status claim is
made here.
