# Prefix clean-wire dominance: proof and implementation review

Verdict: PASS for the specified 17-clean-prefix encoding. This is a
mathematical normalization and source review, not a Lean formalization.
The predicate is not asserted for arbitrary suffix wires after junk begins.

## The elimination rule

Let g be a prefix AND and B an earlier prefix wire with empty singleton
support. Both g and B are false on every independent input, including the
empty input. Suppose that on each of the sixteen minimal positive edge rows,

    g(e) = true implies B(e) = true.

Replace g in its existing slot by OR(B,B). On independent inputs, its value
stays false and every later wire value is unchanged. All singleton supports,
prefix cleanliness conditions, and suffix junk flags therefore stay unchanged.

On every edge row, the replacement is at least the old value. Every later
gate is monotone in its operands, so its value on that row cannot decrease.
The output remains true on all sixteen edge rows and false on all maximal
independent rows. Since the modified circuit is still monotone, those boundary
values imply exactly the full graph edge function on all 2048 inputs.

No pointwise comparison of intermediate functions on other positive inputs
is needed or claimed. Some such values can decrease. This does not undermine
correctness because every positive input contains a minimal positive edge row.

## Termination and compatibility with the existing restrictions

Each replacement removes one prefix AND and inserts one OR. Pruning unused
prefix nodes can only decrease the number of ANDs further; restoring length
17 by an OR-copy chain creates no ANDs. Thus at most seventeen elimination
steps are possible, even when dominance is rechecked after pruning, padding,
and prefix sorting. The normalized prefix satisfies the desired cut for every
remaining AND and every earlier clean prefix wire.

The productive-prefix normalization also only replaces ANDs by ORs, preserving
singleton supports. It can be interleaved with dominance elimination. The
distinct-description normalization copies an earlier identical wire in place;
it preserves wire functions, creates no ANDs, and preserves liveness. Prefix
lexicographic sorting preserves all wire functions. If either normalization
or the new order exposes a further dominance violation, eliminate it and repeat.
The decreasing prefix-AND count still gives termination; when a pass causes
no elimination, all restrictions can hold simultaneously.

The four fixed tail gates are unchanged, apart from renumbering their leaf
references or inserting a prefix OR-copy chain on a leaf edge. Consequently
all seven fixed-tail families remain complete overapproximations. Repeated
operands are essential to the OR copies and remain allowed.

## Exact CNF condition

For each pair of prefix gates h < g, let B be wire 13+h. Introduce sixteen
witness variables w[e] and add

    NOT w[e] OR g[e]
    NOT w[e] OR NOT B[e]

for each edge row. Then add the single guard clause

    NOT op[g] OR support[B][0] OR ... OR support[B][10]
              OR w[0] OR ... OR w[15].

Here a true op variable denotes AND. When g is AND and B has empty support,
some witness must be true, forcing an edge on which g is true and B is false.
Conversely, such an edge permits its witness to be true. If the guard is off,
all witnesses can be false. Reverse witness implications are unnecessary for
the exact existential projection of this cut.

There are 17*16/2 = 136 earlier-gate pairs. Thus the delta is exactly
136*16 = 2176 variables and 136*(2*16+1) = 4488 clauses. The implementation
does not compare against input wires or the free constants; this is a weaker
but still sound cut. Productive prefix ANDs already have a true edge row, so
comparison with free FALSE would add nothing here.

## Implementation and likely search effect

The implementation exposes the first thirty singleton-support and edge-value
tables from the existing build. Index 13+g is the output of prefix gate g.
add_prefix_dominance uses precisely those tables, h < g, sixteen row witnesses,
the two one-way clauses above, and the correctly signed guard. It appends to
the unchanged base clauses, updates counts, and runs before DIMACS writing
and lex-flag allocation. The lex flags therefore allocate beyond the new
witness variables. The optional distinct-prefix clauses refer to the updated
flag IDs. The separate generated cases use that optional flag.

The cut excludes semantic edge-coverage redundancy beyond mere duplicate gate
descriptions and nonempty operand supports. For example, the clean prefix

    u = x9 OR x10
    B = x0 AND u
    v = x0 OR B
    g = x9 AND v

is already ordered by increasing maximum operand and has distinct gate
descriptions and productive AND operands. Yet g covers only edge (0,9), while
B covers both (0,9) and (0,10), so the new cut removes g's AND realization.

The extra constraints may reduce this redundancy, but the witness variables
also enlarge the search. No runtime improvement is claimed without a solver
comparison. Domination by a union of two earlier clean wires is a possible
strictly stronger normalization (replace g by OR(B,C)); it is not implemented
or included in this review's CNF scope.

See prefix-dominance-review.json for the reviewed source hash, projected-clause
checks, and generated-CNF integration audit. No solver was launched or running
input modified during this review.
