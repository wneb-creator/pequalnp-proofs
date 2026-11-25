# Signed sample domination in a globally minimum circuit

Status: independently reviewed mathematical search constraint, not Lean checked.
Reviewer: `/root/algebraic_witness`.

Assume the sampled positive inputs are all graph-edge pairs and the sampled
negative inputs are all maximal independent sets. Let j be a gate and w an
earlier wire. If w is at least j on every positive sample and at most j on
every negative sample, aliasing j to w and deleting j preserves the exact graph
function:

- On a positive sample, the replacement only raises the changed wire. The
  monotone suffix still accepts the input.
- On a negative sample, it only lowers the changed wire. The suffix still
  rejects the input.
- The replacement circuit is monotone. Acceptance of every edge pair and
  rejection of every maximal independent set determine the graph function on
  all inputs.

The earlier wire is unaffected by the deletion. Wire indices and invalid false
reads must be remapped correctly. The circuit has one fewer gate, contradicting
global minimality. No global pointwise comparison of the two wire functions is
required.

Thus, for every earlier w and later gate j, a globally minimum circuit has at
least one witness of either form:

    positive sample: j = true, w = false
    negative sample: j = false, w = true.

Equal full sample signatures are the simplest forbidden case. Applying the
same argument only to the two operands of a gate gives cheaper constraints:

- Every OR gate needs both operand-exclusivity patterns on positive samples.
- Every AND gate needs both operand-exclusivity patterns on negative samples.

This constraint concerns globally minimum exact circuits. It does not preserve
ownership, so it cannot be assumed for a minimum chosen only within a nonstar
subclass. A fixed-size search also needs care: restricting the exact-k search
to minimum-like candidates does not, by itself, prove that no smaller circuit
exists. SAT witnesses remain valid; an UNSAT result retains that model caveat
unless the sizes or padding argument are handled separately.
