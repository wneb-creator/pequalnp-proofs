# L-meta-2582 mathematical handoff

Status: partial only, with helper theorems and conditional normalizers. No proof or refutation is established.

## The requested statement

For a projective-plane incidence relation I of order q ≥ 2, with N = q² + q + 1,
every fan-in-two AND/OR circuit C computing the point-line incidence function should admit
an equivalent fan-in-two AND/OR circuit D with D.size ≤ C.size that is READ2.
There is no tCount assumption. The posted plane hypotheses give q + 1 points on every line
and a unique common line for every pair of distinct points.

READ2 requires one proof tree per prime implicant with both endpoint counts at most two;
minimizing those counts in separate trees is insufficient.

## Checked construction and threshold case

`Canonical.lean` copies the checked star-cover construction into the new helper namespace.
For a bipartite graph E and a vertex cover consisting of point set P and line set L,
`canonical_cover` constructs a READ1 circuit with at most |E| + |P| + |L| − 1 gates.
It proves the full Boolean function and the fan-in-two AND/OR requirements.

`canonical_plane_read_one` chooses all N lines as the cover. From only the per-line
cardinality hypothesis, it obtains an incidence circuit with size at most N(q + 2) − 1.
This bounds a new circuit, not an arbitrary supplied C from below.

`ReadMono.lean` proves generic READ monotonicity: IsReadK n C k implies IsReadK n C l
when k ≤ l, without assumptions on the circuit or its function. The proof lifts lower-cap
count vectors to higher-cap vectors whose entrywise truncation is the original vector.

`PlaneWrappers.txt` gives `plane_read_two_if_large`, assuming N(q + 2) − 1 ≤ C.size; smaller circuits remain open.

## Checked clean-circuit case

`CleanReuse.lean` is the earlier checked reuse argument with only its namespace changed.
For a C4-free bipartite graph, an exact AO2 circuit, and the additional assumption that
every AND gate implies the final output function on every input, `clean_bound` produces
a vertex cover S satisfying |E| + |S| ≤ C.size + 1.

`split_vertex_cover` separates S into point and line covers with the same total cardinality.
`clean_read_two_normalize` combines this bound, the canonical construction, and READ monotonicity
to obtain the full same-size READ2 conclusion under this clean-AND assumption.
The construction actually supplies READ1 before weakening the conclusion to READ2.

Root's `plane_clean_read_two` derives C4-freeness from unique common lines and specializes
this conditional result to the posted incidence relation. The all-AND-clean hypothesis remains
explicit; it has not been derived for an arbitrary source circuit. No regularity assumption
is needed for the general clean-case theorem.

## Checked local rewrites and previously known normal form

`LocalRewriteExplicit.lean` proves that a gate equivalent to an earlier wire can be deleted,
preserving the function and AO2 while decreasing size by one. Repeated-input gates are a special case.
It also proves the explicit clean-wire hoist: remove an OR reader, redirect to its other input,
and append an output OR with the clean wire. Total size and the full function are preserved.
Backward-read and output-validity premises are explicit in these local lemmas.

Repository theorem `L_meta_4543` already gives a no-larger least AO circuit in TopForm
for a nonempty graph, with a secondary minimum. `L_meta_2393` controls nonoutput clean-gate readers.
Re-proving this extraction does not resolve the dirty-block problem.

## Checked obstructions to insufficient local strategies

`ReadTwoLocalObstruction.lean` gives a seven-gate P4 incidence circuit that is not READ2,
although all eleven wire functions are distinct. A four-gate READ2 equivalent is checked.
Thus eliminating semantically duplicate wires alone does not establish READ2.

The original `MatchingLocalObstruction.lean` is also Lean checked: a nineteen-gate circuit
for a three-edge matching is not READ2, has distinct wire functions, and every replacement
of a gate by either operand changes the output. A five-gate READ1 equivalent is checked.
All 285 gate-to-earlier-wire replacements are now Lean checked in `MatchingBypassCertificate.lean`,
using explicit witnesses. The final named-file build passed at 18:54:28 UTC. The earlier raw
existential attempt exited 137; its complete diagnostics are preserved and its failure cause is unconfirmed.
Neither example is a projective plane or a size minimizer. Neither refutes L-meta-2582.
The finite C6 search timed out, so it supplies no infeasibility or minimality conclusion.

## Remaining mathematical gap

The remaining case is a source below the canonical threshold containing dirty AND gates.
TopForm allows nonstar dirty blocks to share internal wires. Per-block costs cannot simply be added:
shared subcircuits would be charged repeatedly, and copying a shared cofactor can increase size.
A global READ2 normalization with a valid shared-gate cost argument is still missing.
Star-cover normalization would suffice but is stronger than the requested READ2 conclusion.

## Unformalized Fano embedding of the local obstruction

Choose Fano points 100, 010, 001 and lines {100,011,111}, {010,101,111}, {001,110,111}.
Their induced incidence graph is a three-edge matching. Use the nineteen-gate matching CNF
for these edges and OR in the other eighteen edge monomials: 19 + 18 AND + 18 OR = 55 gates.
The bad pair remains non-READ2; core bypass witnesses extend with every other input false.
This construction has not been Lean checked. It has no minimality implication: the canonical
Fano READ1 circuit has 27 gates. It only explains why plane incidence alone cannot justify local cleanup.
