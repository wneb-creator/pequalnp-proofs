# Two-dirty-AND successor preparation

The 63-gate target is not solved. The source adds an exact count of at least two AND gates that are true on some complete maximal-false row. The independently compiled TwoDirtyNecessary2056 theorem makes this necessary after the existing no-larger AO2 normalizations; the mapping review records each hypothesis. The earlier singleton-false hypothesis is no longer needed.

The actual 69-gate positive control has two dirty ANDs and passes all 756 boundary rows. Its last three gates are syntactically free; the native solver returned the warm control. The fixed 67-gate one-dirty control is rejected. This rejection is a control result, not a lower bound for arbitrary circuits.

The target phase has three positive-row failures and one new dirty-count-unit failure, with no other failed clauses. Final actual-artifact independent review passed for source, exact normal-form mapping, target prefix/delta, native positive model, and fixed negative rejection. No long successor has launched. Existing long search remains unchanged.

Large DIMACS files remain in scratch and are reproducible from the frozen source, input data, row list, warm circuit and recorded parameters. Complete native and wrapper stdout/stderr and the actual positive model are retained here. No external UNSAT result is treated as a Lean proof.
