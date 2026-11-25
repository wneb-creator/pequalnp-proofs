# L-meta-2583 reduction-strategy notes

The held statement asks for a size-nonincreasing READ-1 replacement of every
AO2 circuit computing a finite-projective-plane incidence function. Reductions
are closed for this lease. None of the results below proves or refutes that
statement.

## Checked dirty-block obstruction

`lemmas/PlaneDirtyBlock.lean` proves a small obstruction to the tempting claim
that TopForm automatically implies READ-1, even for bipartite graphs with no
four-cycle.

Let the target be `xy OR xv OR uy`, the three-edge path on four vertices. The
five gates are:

1. `A = x OR u`.
2. `B = y OR v`.
3. `H = A AND B`.
4. `J = x OR y`.
5. `F = H AND J`.

The circuit computes the target exactly, is AO2 and satisfies TopForm. Its only
junk AND is gate 2 (zero based), its only top is the centreless gate 4, and its
set of top cross edges is empty. The edge `{x,y}` is a prime implicant, but every
accepting proof tree for that edge repeats x or y. Hence this circuit is not
READ-1.

There is a four-gate READ-1 circuit for the same target:
`x AND (y OR v)`, `u AND y`, and their OR. The file verifies both circuits and
all these properties by ordinary kernel-checked finite decision procedures.
This is not a counterexample to size-nonincreasing replacement: the clean
replacement saves one gate. A general proof must account for that cost saving
and for the possibility that the dirty circuit shares its three OR gates with
other blocks.

Build 2026-11-25: `lean-env.sh lake env lean
../results/orch/lemmas/PlaneDirtyBlock.lean`, exit 0. Full stdout/stderr are
`/tmp/oec/pequalnp-pilot-100/plane-dirty-build-04.out` and `.err`, both empty.

## Independent Fano witness-encoding review

Reviewed the counterexample agent's `plane/gen-fano.py` and `decode-fano.py`.
Independently recomputed all 16,384 inputs for binary-dot-product Fano incidence:
21 edges, three points per line, and exactly one line through every distinct
point pair. Its complete monotone boundary has 21 minimal true rows and 37
maximal false rows. The CNF contains all 21,308 required pairwise one-hot
clauses, 503,709 clauses total. The 58-row compression has no variable-index
collisions. The decoder checks backward AO2 wiring, removes only unreachable
gates, verifies the entire truth table, and computes joint capped proof-tree
multiplicities for READ-1. The mock 26-gate seed correctly reports 47 full-table
errors and no refutation. An UNSAT result with extra normalization or symmetry
constraints would still require a separate completeness theorem.

Allowed-host web searches for existing projective-plane monotone-circuit
bounds did not locate a useful primary source. No external bound was adopted.

## OR-count route and lease interruption

The proposed unrestricted bound OR-count >= |E|-1 for arbitrary C4-free graphs
is false. Existing checked `Outside/L_meta_584.lean` gives the Petersen graph's
15-edge function with 13 OR and 7 AND gates. Both counterexample_search and
lemma_routes independently checked its full 1,024-row truth table and the
no-four-cycle condition. Petersen is not bipartite, so this does not settle a
plane-specific OR bound.

Before that obstruction was found, a bounded census tested C5 (at most 3 OR,
8 total gates; solver UNSAT in 4 seconds), two triangles sharing a vertex
(4 OR, 10 total; UNKNOWN after 90 seconds), and C6 (4 OR, 10 total; UNKNOWN
after 90 seconds). These are solver outcomes, not unrestricted Lean theorems.

The new `or-count/free-and.py` removes the total-AND restriction: contract each
AND-only region to a nonempty conjunction of primary inputs and earlier OR
nodes. Each OR has two such operands; the final output is another such
conjunction. Selectors and all semantic values are encoded exactly. A control
instance for P4 with two OR nodes was SAT and reconstructed the correct
four-gate circuit, verified on all sixteen inputs.

The Fano instance with nineteen OR nodes and unrestricted AND gates has 25,209
variables and 112,895 clauses over the complete 58-row monotone boundary.
counterexample_search independently reviewed the encoder and decoder PASS.
It was NOT LAUNCHED: the root's renewal returned HTTP 410 at 15:07:34 UTC.
There were no remaining auxiliary solver processes. Sources, full outputs,
inputs, compressed CNFs and checksummed manifest are preserved in
`results/orch/or-count/`. A future SAT witness must be fully decoded and
verified; fewer than twenty OR gates alone would not refute L-meta-2583 unless
the total reconstructed circuit size is at most twenty-six.
