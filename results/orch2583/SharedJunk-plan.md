# Shared junk-wire direction — paused before implementation

Root paused all proof/research/build work immediately after assigning this direction because the desk renewal reported no live lease. No SharedJunk Lean file was started and no build/search is running for this agent.

Already-derived plan, not a checked theorem:

Let H = OR(P) AND OR(L), with P point inputs, L line inputs, and |P|,|L| at least two. For a C4-free incidence relation I, define point centers as points p in P incident to every line in L, and line centers as lines l in L incident to every point in P. Each center set has cardinality at most one, since two centers and two opposite-side vertices would form a rectangle.

For a family of pure OR filters W_i, the accepted pair core of H AND W_i is

    ((P intersection Wp_i) product L)
      union (P product (L intersection Wl_i)).

If every such pair core is contained in I, all selected point centers lie in the common point-center set, and all selected line centers lie in the common line-center set. The union over all filters is therefore a single common double-star. When both selected center sets are nonempty, its two stars overlap in their center edge. This should yield

    |merged edges| + |chosen point centers| + |chosen line centers|
      <= |P| + |L| + 1.

The existing star-cover constructor then gives a read1 circuit of size at most |P|+|L|. The shared H costs at least |P|+|L|-1 gates including its two OR supports and root AND; one genuine filtered use contributes another AND. This suggests replacing all filtered uses together without increasing size, amortizing the additional filters.

Still required: formal finite-family union/center/count proofs; a circuit-side hypothesis ensuring all relevant uses of H are these filters and lie in the output OR region; deletion/splice accounting; handling other uses, mixed-side H, and added OR branches. This is not a proof of the posted gap.
