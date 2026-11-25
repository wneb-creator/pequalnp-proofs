# Focused two-output synthesis target

2026-11-25 UTC. Constructive, coordinating with circuit_search. No SAT run or Lean build was started by constructive for this target.

Let F0 be the Heawood edge function with vertex 13 deleted, and let A = x1 OR x2 OR x4. A network of at most 24 gates that provides both F0 and a wire W satisfying

`A <= W <= A OR F0`

gives a 26-gate Heawood circuit by appending `x13 AND W`, then ORing that result with F0. The weaker W condition is exact: on F0=false assignments W must equal A, while on F0=true assignments its value is absorbed. The earlier suggestion of 23 gates for F0 with A internally available was unnecessarily strong; that would actually give 25 gates by this direct extension.

F0 and W must be independently selectable output wires. In particular, W may depend on F0 and occur later. Liveness must refer to the union of both output cones. Assuming F0 is the last gate would restrict the relaxed search without justification.

## Complete monotone boundary constraints

The focused network has 13 inputs, retaining the original indices 0 through 12.

* F0 is true on its 18 edge pairs and false on its 30 maximal independent sets.
* W is true on the three singleton assignments at vertices 1, 2, and 4.
* W is false on the 12 maximal independent sets of the induced graph H outside those three vertices, with all three A variables zero.

H is the incidence graph between four K4 vertices and their six pairs. Its maximal independent sets need not be maximal independent sets of F0, so using only F0's negative boundary would not enforce the full W condition. The union of all four boundary families has 58 assignments. Extra forced output values on already-present rows are included in the JSON; W is unconstrained on F0-positive rows without an A vertex.

The prototype independently checked coverage of every one of the 8,192 assignments: every F0-positive input contains an edge row; every F0-negative input is contained in an F0 negative row; every A-positive input contains one of the W singleton rows; and every A/F0-negative input is contained in a W negative row. Thus the constraints are sufficient for arbitrary monotone candidate outputs.

## Near-seeds and prefix correction

Four 24-gate seeds compute W=A exactly and F0 with one missing edge. Two omit a residual-H edge and have 34 false negatives; two omit an A-incident edge and have 47 false negatives. They have no other F0 errors, as checked on all 8,192 assignments.

The A-first seeds omit (0,7) or (1,7); their W output is wire 14 and F0 output wire 36. The independent-prefix seeds omit (0,10) or (1,9); their W output is wire 16 and F0 output wire 36. Internal wire indices start at 13 because these networks have 13 inputs. To extend to 14 inputs, shift every internal index by one, then append the two final gates.

Correction to an earlier message: the posted gap does NOT require the particular first gates OR(0,1), OR(0,2). It existentially chooses the first two gates and minimizes their pair score under graph automorphisms; the second gate may use the first. This was confirmed by rereading the full statement in assignment.json after circuit_search flagged the error. Both seed prefix families are legitimate sufficient strategies, subject to the separately checked prefix normalization. The independent-prefix family is diversity, not a format requirement.

## Stable artifacts

Under `/tmp/oec/pequalnp-pilot-70/constructive/`:

* `cooutput_rows.py`
* `cooutput24-boundary-rows.json`
* `cooutput24-seed-missing-0-7.json`
* `cooutput24-seed-missing-1-7.json`
* `cooutput24-seed-missing-0-10.json`
* `cooutput24-seed-missing-1-9.json`

Reproduce with `python3 cooutput_rows.py --output-dir <the scratch directory>`. The script uses only the Python standard library and runs in under one second in the current environment. The seeds are incomplete candidates, not proofs, and no 24-gate network meeting every co-output constraint is known.
