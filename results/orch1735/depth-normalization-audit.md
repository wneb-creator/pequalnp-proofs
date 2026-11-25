# Global minimality and depth normalization audit

No bounded-depth or constant-factor normalization theorem was obtained. The
identities below are ordinary Boolean identities and circuit-cost calculations;
they have not been formalized as IsAO2 circuit transformations in Lean.

## A valid contextual simplification in the finite archive

The archived nine-gate C5 witness is locally nonredundant: every gate has
incomparable fanin functions. Nevertheless its dirty tail is

    ((a OR c) AND (b OR c)) AND b AND a = a AND b.

Replacing the three AND gates by the one gate a AND b saves two gates. The two
OR gates can remain for their other users. Thus local fanin incomparability is
strictly weaker than the global minimality needed for the task. This is the
tail of `finite/c5-reduced-nested9.witness.json`, with a=x0, b=x1, c=x3.

## Clause reuse can preserve girth five

The identity

    (a OR b)(c OR d)(a OR d)(b OR c) = ac OR bd

gives a clean top with two dirty AND children. Let the four displayed OR
clauses also feed stars with new centers z,y,w,u, respectively. The full graph
has edges

    ac, bd, za, zb, yc, yd, wa, wd, ub, uc.

It is K4 with the four edges outside the matching ac,bd subdivided. Its girth
is five. Therefore the tempting assertion that dirty clauses cannot be reused
by distinct clean stars in a girth-five graph is false. The evident circuit
has 15 gates while a standard four-center star circuit has 13, so this is not
a least-circuit obstruction. The finite-search agent has the graph for a
bounded synthesis query. No solver result or leastness claim is recorded here.

## Arbitrarily deep TopForm circuits within an additive 2n cost

Let G be a nonempty graph on n vertices, F its edge function, C any binary
AND/OR circuit computing F, and S a maximal independent set. Put

    g = AND over s in S of x_s,
    H = OR over v outside S of x_v.

Both S and its complement are nonempty. Replace each input x_i of C by
`x_i OR g`, obtaining a copied circuit with output F OR g: if g is true all
its input wires are true; otherwise the inputs are unchanged. Since S is
independent, F implies H. Since S is maximal independent, every vertex outside
S has a neighbor in S, so g AND H implies F. Therefore

    (F OR g) AND H = F.

On the assignment that is true exactly on S, every copied gate is true while
F is false. All copied AND gates, and all gates used to build g, are dirty.
The final AND is clean and is the only clean AND, so the resulting circuit is
TopForm. The output of the original graph circuit has no path consisting only
of OR gates to an input: otherwise it would accept a singleton. Hence the
first raw OR side of the final AND is empty and Ustar is the entire edge set.

The added gate count is

    (|S|-1) + n + (n-|S|-1) + 1 = 2n-1.

Choosing a chain for g gives arbitrarily large dirty AND depth. For graphs
without isolated vertices, support lower bounds give n <= minimum_size+1,
so this construction is within a constant factor of a minimum circuit. It
does not make the result least, and cannot refute the posted statement. It
shows that TopForm plus coarse near-optimality cannot supply the uniform
AND-depth cap needed by the fixed-depth theorem. Exact leastness must support
a genuine saving argument.

## Remaining proof obligation

Dropping a gate or an OR operand and preserving all positive edge pairs
preserves the entire graph function, because the new circuit is monotone and
pointwise below the old one. A least circuit therefore has a positive edge
pair whose final output is lost for every such cost-reducing deletion. These
are contextual critical pairs, not merely pairs accepted by an internal gate.
No bounded charge for contextual critical pairs along nested dirty gates was
derived in this audit.
