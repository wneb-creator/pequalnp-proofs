# L-meta-2602: focused decomposition and checked small cases

## Existing cuts

The repository contains two checked reductions of this step. The desk says three live reductions, so no fourth reduction should be attempted.

- `R_meta_2602_415` splits off an elementary monotone wire guard and a finite-assignment cone obstruction. The guard is already proved in `L_meta_5174`; the difficult child is `L-meta-5176`.
- `R_meta_2602_2` splits into a lower bound of 56 gates on the face where the fixed point and line inputs are false (`L-meta-5985`) and a fresh-column/path theorem (`L-meta-5987`). Both difficult children remain open in the downloaded feed.
- The parent cut `R_meta_1482_3` assumes the full lower bound 64, removal of all unclean AND gates in least circuits, and elimination of nested AND gates. Those assumptions remain substantial; the last two amount to the normal-form route.

## Most focused potential route

Let the distinguished edge be `(u,v)=(0,13)`. Remove its two endpoints. The remaining incidence graph has 45 edges and a perfect matching of size 12, namely the diagonal incidences numbered 1 through 12. Its expected AND/OR circuit cost is therefore `45 + 12 - 1 = 56`.

The useful local claim would be:

> For a C4-free bipartite edge function, a proper binary circuit with both formal first derivatives zero at an edge uv has a circuit for the face u=v=false using at least deg(u)+deg(v)+1 fewer gates.

At the plane, the number removed is at least 9. A circuit of at most 64 gates would then leave a circuit of at most 55 gates, contradicting the face lower bound 56.

The ordinary star circuit loses exactly eight gates on this restriction. The double-zero condition must supply one extra deletion. This is a more local target than a normal form for every least circuit. However, both the face lower bound and the local removal theorem still need real arguments; neither is established here.

The main obstruction to proving the removal theorem is sharing: gates that serve the double-star neighbourhood may also serve the punctured face. C4-freeness rules out an outside vertex adjacent to two neighbours on the same side, but turning that fact into a count of unshareable circuit gates still has to handle unclean AND gates and absorbed terms. This closely matches the existing fresh-column/path obligation.

## Small exact search evidence

The counterexample agent ran exact truth-table/formal-derivative state enumeration. I read the full output in `/tmp/oec/pequalnp-pilot-60/small-double-extra.log`.

| Graph and distinguished edge | Minimum double-zero size | Face minimum + endpoint degree sum + 1 |
| --- | ---: | ---: |
| Two disjoint edges | 4 | 1 + 2 + 1 = 4 |
| Four-vertex path, end edge | 5 | 1 + 3 + 1 = 5 |
| Four-vertex path, middle edge | 6 | 0 + 4 + 1 = 5 |
| Four-cycle | 5 | 1 + 4 + 1 = 6 |

These are computational observations, not Lean-checked lower bounds. The four-cycle shows that the proposed local removal bound needs its C4-free hypothesis.

## Invalid shortcuts

Double-zero derivatives do not imply at least two distinct nested-AND pairs. The circuit

```
g = x AND y
a = g OR z
b = g OR w
out = a AND b
```

computes `xy OR zw`, and both formal derivatives at `xy` vanish. Its only nested AND pair is `(g,out)`. It uses four gates; the direct circuit uses three. Thus the needed theorem concerns redundant cost, not merely a count of nested AND pairs.

No new reduction file is proposed because capacity is exhausted and the remaining hypotheses would not yet carry a newly proved substantive part of the lower bound.

## Lean geometry component

`lemmas/Geometry.lean` compiled successfully with the pinned Lean4.36.0 toolchain and `PEqualNP.Defs` only. Complete validation log: `/tmp/oec/pequalnp-pilot-60/geometry-build-2.log` (empty stdout/stderr, exit0). The file proves all finite geometry counts and arbitrary vertex-cover bounds stated above. It does not prove the circuit lowerbound56 or the9-gate deletion theorem.
