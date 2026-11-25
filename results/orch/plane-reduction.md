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
