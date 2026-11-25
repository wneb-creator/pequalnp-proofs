# Fixed-bank one-NOT obstruction

Status: **computed; not Lean-checked**. This does not prove L-meta-2592.

The free Boolean bank contains inputs `x0,x2,x3,x5,x6,x9`, false, the pair
ORs `(2,5),(9,3),(6,0),(3,6)`, and the triple ORs
`(2,5,9),(9,3,0),(6,0,2),(3,6,5)`. These are exactly the six retained
inputs and eight OR wires from the K4 near-witness. The target is
`(x0 AND x5) OR (x2 AND x3) OR (x6 AND x9)`.

`one-not-residual.py` exhaustively enumerates formula truth tables on all
64 assignments, with at most three binary AND/OR gates and at most one
NOT. Its result contains no witness. At three binary gates it enumerates
3,767 monotone and 49,660 one-NOT truth functions. The original full stdout
and stderr are retained. The archived script differs only by writing its
JSON result next to the script, so it can be rerun from another checkout.

The separate `one-not-three-bank.py` checks all 575 subsets of one, two,
or three bank functions. None determines the target: every subset admits
two assignments with the same bank values and opposite target values.

This also handles internal sharing in a circuit with the same gate budget.
After pruning unused gates, four used gates consisting of three binary
gates and one NOT have seven input slots. Every nonoutput gate has at
least one internal outgoing edge. If a computed gate is used more than
once, there are at least four internal edges, leaving at most three
external bank occurrences. Such a circuit would make the target a
function of at most three bank wires, which the second enumeration
excludes. With no internal sharing the circuit is a formula, covered by
the first enumeration. Smaller circuits satisfy the corresponding
stronger input-slot bound or are already covered as formulas.

This finite obstruction applies only to that fixed free bank and gate
budget. It does not exclude circuits that change the shared OR bank,
mix the four other Petersen inputs into intermediate gates, or use a
different factorization.

Theoretical conditional simplifications, also not formalized here:
write a one-NOT computation as `F(x)=H(x,NOT g(x))` with the suffix
monotone in its last input. If `g <= F` pointwise, then `H(x,true)=F(x)`.
If `F <= g` pointwise, then `H(x,false)=F(x)`. Circuit gate savings still
require constant propagation and an applicable lower bound; no generic
same-size negation-elimination principle is assumed.
