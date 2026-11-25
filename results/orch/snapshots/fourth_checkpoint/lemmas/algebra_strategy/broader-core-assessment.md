# Broader cores with sound full-plane extensions

## Seven rows

Add original point9 to rows0,1,2,3,6,7. The full-degree core has20 inputs and28 edges, baseline34 gates, target33. Appending the other six full stars costs30 gates, so an exact33-gate core suffices for63. This geometry is the union of two intersecting4-point lines and is already represented by circuit_search/subsets/k7_p0.json (same degree profile0,2,9,0,2; its representative rows are0,1,2,3,4,9,10).

Removing point9's private lines17,18 leaves18 inputs and26 edges, baseline32. An exact31-gate circuit is necessary for the33-gate seven-row route by essential-leaf gate elimination. It is not automatically sufficient: restoring both private terms costs three gates by ORing the two new lines, ANDing point9, and ORing the old output, giving34 and then64 overall.

Two-gate restoration is sufficient under an additional structural condition: an existing AND gate reads the bare point9 input and another wire, and has an OR-only path to the output. Insert two OR gates to add the private lines to that gate's other parent. The OR path ensures both new star terms reach the output; any effects through additional downstream paths are absorbed by those new star terms. This condition is not guaranteed for an arbitrary31-gate circuit.

## Nine rows, complement of a four-point arc

Chosen rows:0,1,2,3,5,6,7,9,11. Omitted arc:4,8,10,12. Every full line meets the omitted arc in at most two points, so every line has at least two remaining incidences. There are22 essential inputs and36 edges, with six lines of degree2, four of degree3, and three of degree4.

The exact target is43 gates versus the44-gate star baseline. Appending the four omitted full stars costs20 gates, giving63 without a tap or leaf-restoration assumption. reduction_analysis independently compiled the exact completion bridge in NineRowCompletion.lean.

k9_arc_4_8_10_12.json gives canonical input mapping,36 positive-edge tests and228 maximal-negative tests, and the verified44-gate baseline. The raw43-gate approximation k9_arc_4_8_10_12_approx.json lifts the17-error six-row seed by appending rows5,9,11. It misses no positive edges and accepts67 maximal negatives. The shared stochastic agent independently checked all4,194,304 assignments:0 false negatives and1463 false positives. It remains an approximation, not a43-gate proof.

Among the nine arcs disjoint from the original six rows, the chosen arc ties for the best maximal-negative count for this lifted approximation (67; other choices68-73). No separate nine-row SAT lane was started by this generator.

## Smaller affine variant, assessed only

Omitting all four points of full line17 yields nine rows with21 essential inputs and36 edges; the omitted line is unused, and each of the other twelve lines has degree3. It retains the old six rows and adds4,8,11. There are233 boundary tests (36positive+197negative). The lifted approximation has70 false maximal negatives and823 false assignments among2,097,152 total. Exact43 still extends to63 by appending the four omitted stars. The line18 version is symmetric. No pack or search lane was generated for this alternative; the running arc-complement case keeps priority.
