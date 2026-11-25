# Checked star-profile existence component

The119-line StarExistence module is checked and cached. It depends on the checked Existence module while developing; final assembly can include both bodies under the single permitted PEqualNP.Defs dependency.

and_reads_input proves that any AND gate reading a raw input can be true only when that raw input is true. Consequently raw_ands_star gives HasStarProfile whenever every AND gate reads some raw input. The explicit graph-DNF construction has this property, so graph_star_exists provides an exact star-profile witness for every finite graph.

star_minimal_exists minimizes only among circuits with HasStarProfile. Its comparator explicitly requires that property. This does not prove the posted assertion that one global minimum has HasStarProfile. The unchecked remaining work is a size-preserving normalization or an equivalent global lower bound.
