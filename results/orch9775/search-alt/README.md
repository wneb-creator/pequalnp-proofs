# L-meta-9775 alternate circuit search

The exact target is the 14-input monotone edge function in `data.json`.
Inputs are wires 0 through 13; gate `i` produces wire `14+i`.
Operation 0 is binary AND, and operation 1 is binary OR. No constants,
negations, forward references, or non-binary gates are used.

`make_data.py` independently computes the 19 positive edge assignments and
36 maximal independent negative assignments. These 55 rows characterize
the target among monotone functions; exhaustive coverage and the 25-gate
star baseline are independently verified on all 16,384 assignments.

`search.cpp` has two modes. Fixed mode uses 24 gate slots and minimizes
four times false positives plus false negatives. Elastic mode uses 29
slots, preserves exact correctness, and minimizes the number of gates in
the output cone. Dead slots support local resubstitution and topological
reordering. Every reported witness is trimmed and checked on the entire
Boolean cube before it is printed. `validate.py` is a separate Python
truth-table implementation for archived best states and witnesses.

`search_nonlinear.cpp` is a distinct elastic variant. Its objective is
32 times the live gate count minus the number of target edges without a
squarefree monomial derivation. The latter is computed using singleton
and two-variable monomial propagation: OR takes unions; AND can form a
squarefree edge only from two distinct singleton terms. This rewards a
necessary feature of any 24-gate candidate under the checked read-1 lower
bound. It is a search bias, not a completeness claim or a proof of the
target. `validate_nonlinear.py` independently recomputes the score using
sets of monomials and checks the full truth table. Its initial bounded
diagnostic passed; no 24-gate witness was found.

`automorphisms.py` exhausts both bipartition orientations and every
permutation of one seven-vertex side. The graph is connected, and the
other side has distinct neighborhoods, so the opposite side is forced.
It finds exactly four automorphisms, including two side swaps, and 31
unordered pair orbits. All edges, all 91 pairs, and group closure are
checked. This census is useful for reducing duplicated synthesis cases.

Full diagnostics are preserved alongside their sources. `status.json`
records active process details. A near-correct circuit is not a result
for the posted statement, and unsuccessful bounded search establishes
no circuit lower bound.

`simplify.py` independently removes gates whose signatures agree on all
55 extremal rows, selects an equivalent output, and trims dead gates.
It then checks the reduced circuit on all 16,384 assignments. The
monotone extremal criterion is needed here: intermediate functions need
not agree off those rows, but the complete reduced circuit still computes
the exact target. Archived examples reduce to 25 or 26 gates, not 24.

Two further variants are prepared and have only bounded diagnostics:
`search_reduced.cpp` periodically applies this signature collapse;
`search_pivotal.cpp` additionally replaces a gate by a star of its pivotal
positive edges, using up to two earlier dead slots. Such a replacement
is below the original monotone gate and preserves every positive edge
that depends on it. It is accepted only after the exact 55-row check.
The first pivotal diagnostic correctly rejected an edge-order/index
mismatch and exited 2 (`pivotal-diagnostic.stderr`). The rejected source
is retained as `search_pivotal_rejected_row_order.cpp`; it must not be
used. The corrected source explicitly maps each edge mask to its sorted
positive-row index. Its second diagnostic passed independent full-cube
validation. Neither prepared variant has run a long phase yet.

`classify.py` independently computes singleton support, actual live-gate
readers, `Bplus`, `Bzero`, and the ineligible-input mask. It checks the
support recurrence against fourteen scalar executions and verifies the
surplus identity for strict live circuits. `search_architecture.cpp`
targets `Bzero = 1` with a pure-side ineligible mask, using the collapse
and pivotal rewrites. Its five-second diagnostic found a correct
26-gate example with `Bplus = 12`, `Bzero = 1`, and mask 16256. No long
architecture run started.

At root's request, constructive searches stopped at 17:37 UTC to focus
on independent review of the lower-bound certificates. Elastic search
completed 24,594,000 updates, best 25 live gates, exit 0 after SIGINT.
Nonlinear search completed its 600-second cap naturally, 2,888,000
updates, best objective 800 (25 gates and zero squarefree deficiency),
exit 0. Both complete streams passed independent final validation.
No 24-gate witness was found, and no owned search process remains.
