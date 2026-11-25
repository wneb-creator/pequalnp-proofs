# L-meta-2448 finite checks and semantic analysis

## Semantics

`Owns` permits an intermediate AND gate to own graph edges while accepting nonedges or singleton inputs, provided those false positives are removed downstream. Therefore girth assumptions do not immediately imply the profile for an arbitrary circuit. The existential minimum-circuit exchange is the actual mathematical obstacle.

## Four vertices

Exhaustive semantic-signal-set breadth-first search over normalized binary AND/OR circuits covered all 38 labeled triangle/C4-free graphs on four vertices. Minimum sizes: 1 graph at size 0; 6 at size 1; 12 at size 2; 7 at size 3; 12 at size 4. Every retained minimum witness had HasStarProfile. Every minimum agreed with |E| + vertex cover number - 1 (except empty graph, size 0). States by depth: 12, 114, 988, 8291.

## Five and six vertices

CaDiCaL 2-input AND/OR synthesis, evaluated on all Boolean assignments, found UNSAT at one gate below the star-cover bound for all 11 isomorphism classes on five vertices and all 23 on six vertices. Empty/single-edge cases are trivial and skipped by SAT. C5: lower6 UNSAT; size7 SAT with both unconstrained gates and every AND required false on all singleton/nonedge inputs. Both witnesses have star profile. C6 and C5 with one attached leaf: lower7 UNSAT, star-cover bound8.

These are computational checks only, not Lean-checked results. The solver encoding uses one-hot choices of operation and distinct earlier operands; every nonfinal gate must be read later. Nonconstant minimal monotone circuits can be normalized to this form by removing constants, unary gates, equal-operand gates, and unused gates. Exact k synthesis also covers smaller positive gate counts: append the output with one operand of its final gate under the same operation, preserving the function.

## Reproducibility

Scripts and complete diagnostics are under /tmp/oec/pequalnp-pilot-74:
- star-small.py; star-small-results.json; star-small.stdout; star-small.stderr
- star-sat.py; star-sat-n5-results.json; star-sat-n6-results.json
- star-sat-n5.stdout; star-sat-n6.stdout; corresponding stderr and per-query CNF/solver logs

No counterexample has been found.

## Seven vertices

Generated all 48 isomorphism classes by adding one vertex to each six-vertex class and checking triangle/C4 constraints, then canonicalizing by degree classes. Of 46 nontrivial classes queried one below the cover bound, 38 were UNSAT within 20 seconds and 8 reached the time limit. No SAT counterexample.

## Stronger least-circuit cleanliness tests

P4 at its minimum of four gates and C5 at its minimum of seven gates have no normalized circuit with an AND gate accepting a singleton or nonedge pair (UNSAT). C6 at minimum eight gates remains unanswered after several 30/60-second bounded searches. Exact nonstar-owning-AND encoding also returns UNSAT for minimum C5.

## Checked finite witness

`results/orch/lemmas/StarCounterexample.lean` compiled with the pinned Lean toolchain (exit 0; empty stdout/stderr). It verifies an explicit seven-gate C5 circuit, its Monotone2 property, exact function, HasStarProfile, size, and both graph hypotheses. It does not prove minimality or the universal gap statement. The explicit circuit is independently derived from SAT and all declared properties are proved with ordinary `simp` or `decide`; no external certificate is trusted by Lean.

## Additional precise ownership checks

A separate SAT encoding computes each gate cone exactly from its selected predecessors and asks for an AND owning two vertex-disjoint graph edges. C5 at seven gates is UNSAT (2.1 s); C6 at eight gates is UNSAT (29.9 s); C7 at ten gates is UNKNOWN (60 s).

All 17 six-vertex classes with 3–5 edges queried at their proven minimum size are UNSAT when required to contain a dirty AND. This includes the relevant forests and C5 plus an isolated vertex.

## Free-OR AND-budget probes

The compressed model represents each AND operand as an arbitrary OR of primary variables and earlier AND outputs; final output is an OR of selected AND outputs. This covers monotone circuits with the specified AND budget regardless of OR gate count. C11 at AND budget5 and Petersen at AND budget5 both reached 60-second limits (UNKNOWN, not UNSAT). Positive controls C4/budget1 and C5/budget3 were SAT and independently truth-table checked. C5/budget2 and C6/budget2 were UNSAT.

Search scripts, summary results, full batch stdout/stderr, and SHA256 sums are copied to results/orch/search for preservation. Individual CNF and solver logs remain in task scratch and are reproducible from the scripts. These SAT results remain unverified by Lean.

C6 dirty-at-minimum query subsequently returned UNSAT in 49.393 seconds on a longer 300-second-cap run. Earlier timeouts are superseded for that exact query. All AND gates in any normalized eight-gate C6 circuit reject singleton/nonedge inputs. This is a SAT result only.

Final bounded follow-up: the seven-vertex theta graph with path lengths3,3,2 (8edges, star-cover upper bound11) at ten gates remained UNKNOWN after300 seconds. No witness or refutation was obtained. All searches have now stopped normally.

## Checked limitation of pivotal-star restriction

PivotalStarLimitation.lean compiled successfully with empty logs. It gives a seven-gate circuit computing C5 with global HasStarProfile, but gate5 is pivotal on edges01,12,23, which have no common vertex. The gate owns only edges12,23 (center2). Thus star ownership does not imply the pivotal-star hypothesis of CriticalRestriction. Its left operand x1 OR x3 rejects singleton2; its right operand x2 OR (x0 AND x1) accepts singleton2, illustrating the necessary operand orientation. Minimum size7 is supported by the earlier exhaustive SAT query, but is not established by this Lean helper.

For a monotone prefix, the universal input-to-operand implication hleft is equivalent to acceptance of singleton input c. No counterexample was found to existence of a suitable operand when the pivotal-star hypothesis itself holds in a minimum circuit.

Root follow-up2026-11-25 07:56–08:02 UTC: retried the first three previously UNKNOWN seven-vertex graphs with120seconds per query. All three remain UNKNOWN, no SAT witness and no UNSAT certificate. Paused normally before full-checker trial. Full driver, results and stdout/stderr preserved in search/retry-seven.* and search/star-seven-retry-results.json.
