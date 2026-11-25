# What nonempty star ownership currently implies

This is a conceptual report, not a Lean proof of the full posted gap. The general canonical bound remains unproved.

## Proven mathematical consequences

For a monotone AND/OR circuit computing the edge function, every graph edge has an owning AND. On its pair input, some AND must be true: otherwise OR-only tracing of the true output would give a true singleton input, contradicting the loopless graph function. Choose the earliest true AND; every earlier AND, hence every AND in its strict cone, is false on that pair.

Consequently **star profile implies AND-count ≥ minimum vertex-cover size τ(G)**. Choose one center for each nonempty owned-edge star. These centers cover every graph edge, and their number is at most the number of AND gates. The argument does not need the triangle/four-cycle hypotheses or nonempty ownership at every gate; empty-owned ANDs can be ignored.

If every AND owns a graph edge, **no AND gate directly reads an earlier AND gate's wire**. Any pair accepted by the parent makes that child true, contradicting ownership of the pair by the parent. This refers to valid earlier reads; invalid forward reads cannot supply a true operand. On an ownership witness, each operand instead has an OR-only trace to an input, with all AND ancestors false on that witness.

## What is missing

The preceding facts do not supply OR-count ≥ |E|−1, or the weaker combined gate bound |E|+τ(G)−1. OR-only traces are witness-dependent; their full singleton supports can include nonneighbors and can be shared by different dirty gates. Several owners can also have the same star center. It is not justified to regard these traces as separate exact linear neighborhood outputs.

The linear-output lower bound requires an actual output, or a suitable charged subnetwork, that is false on the assignment turning on every variable outside its prescribed support. A dirty contour may be true on that assignment. Graph correctness is restored downstream, and no disjoint charging argument for those downstream gates has been established.

TopForm prevents a globally sound AND from being an ancestor of another AND. Thus the earliest dirty AND in TopForm has no AND ancestors: all earlier ANDs are sound and hence excluded from that cone. In the strict binary model, its two operands are OR-only, but the resulting rectangle may still contain nonedges. Ownership controls only its intersection with the graph. Cleaning a shared OR support to the actual neighbors may require extra gates. Moreover, the known transformation to TopForm has not been proved to preserve star profile: removing an ancestor can make later gates own additional graph edges.

## Concrete limitation of TopForm plus ownership

Let G be the connected forest with edges 02,03,04,05,15 on six inputs. Consider the seven gates

    A = x0 OR x1
    B = x2 OR x3
    D = A AND B
    H = D OR x4
    K = x0 AND H
    S = x5 AND A
    output = K OR S

The output is exactly x0 AND (x2 OR x3 OR x4), OR x5 AND (x0 OR x1). D owns precisely graph edges02 and03; K owns04; S owns05 and15. Thus every AND has a nonempty star of owned graph edges. D is dirty: it accepts nonedges12 and13. K and S are globally sound and neither is an ancestor of another AND, so TopForm holds. The OR wire A is shared between the dirty cone and S. All64 assignments, the raw ancestor ownership sets, and an essential graph-edge witness for every gate were enumerated by the report-generation script.

This circuit is not minimum: it has seven gates versus the six-gate construction `x0 AND (x2 OR x3 OR x4), OR x5 AND (x0 OR x1)`. It therefore does not refute the posted statement, the proposed canonical bound, or any additional consequence that genuinely uses minimality. It does refute the shortcut that nonempty star ownership plus TopForm, even with every gate essential on some graph edge, makes every AND globally sound.

## Consequence for counterexample searches

A circuit smaller than |E|+τ(G)−1 would refute a canonical-size conjecture. It would not by itself refute the posted existential star-ownership statement. That further conclusion needs either the missing profile-conditioned size lower bound or a direct proof that every minimum circuit lacks the required ownership property. No such bridge is currently proved or located in the checked repository.
