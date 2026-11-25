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
