# Status review and local irreducibility diagnostic

No proof or refutation of L-meta-1735 is claimed here. The mathematical
essentiality arguments below are informal; the finite diagnostic is checked by
ordinary Python enumeration, not by Lean.

## Fresh public status

`status-2026-11-25.json` records the public snapshot generated at
2026-11-25T04:53:57.597Z and the relevant GitHub evidence. L-meta-1735 remains a
conjecture with the same statement hash. The public detail does not expose a
live-reduction-slot count. The three reductions in PRs3949,4098,4142 remain
merged; later PR7588 received `REJECTED (reduce-extra)`. No evidence of a free
slot was found. The complete search returned21 matches, with no incomplete
results, and no open PR directly submitting L-meta-1735.

GitHub metadata redirects the old public repository name to
`open-goat/pequalnp-proofs`; this was used only for read-only status queries.
No git remotes were changed, and this agent made no desk calls.

## Informal least-circuit invariants

For a nonempty graph function, every gate of a least AO2 circuit must be
essential on some minimal positive input (the two endpoints of an edge):
replacing the gate by false must change the final output on that edge. Otherwise
set it to false, propagate constants, remove the gate and any resulting aliases,
and obtain a smaller AO2 circuit. The output only decreases, so no false positive
is introduced. If every edge remains accepted, monotonicity preserves acceptance
on every positive input. The surviving final output cannot be constant false
because the graph has an edge. Constant propagation needs no constant gates:
AND with false becomes a false marker; OR with false aliases its other operand.

Similarly, replacing an OR gate by either child decreases the output. Global
leastness therefore supplies a graph edge lost by each bypass. On that edge the
two fanin values must be01 or10 respectively. These two edges are distinct.
Replacing an AND gate by either child increases the output instead; leastness
then supplies an independent-set false positive for each bypass. It can be
extended to a maximal independent set by monotonicity.

These invariants give witnesses, not a bounded-load charging map. Different
gates may have the same critical edge. No linear edge count follows here.

## Concrete obstruction to local surgery alone

The twelve-gate circuit in `c5-context-essential12.json` computes C5. Its five
clauses are the complements of the five maximal independent sets, with shared
two-variable ORs. The final AND is the only clean AND; the other three ANDs are
nested junk. It is TopForm and all five graph edges lie in Ustar.

For every gate and every earlier wire, replacing that gate by that wire changes
the full Boolean function. Thus even this strong one-gate substitution criterion
does not eliminate nested junk. The circuit is still globally nonleast: the
verifier supplies an explicit seven-gate star circuit for the same function.

Run `python3 results/orch1735/status-review/verify_c5_context.py`. It checks all32
assignments, all126 gate/earlier-wire replacements, TopForm, Ustar, and the
seven-gate comparison circuit. This is a small diagnostic, not a search result
or a minimum-size lower bound.
