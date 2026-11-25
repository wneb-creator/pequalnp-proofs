# Two useful exact pencils in a 38-OR promise separator

Status: mathematical observation awaiting independent review; not Lean checked.

This concerns the thirteen-output, thirteen-line-input promise model. Each
output accepts the four singleton lines of its target pencil and rejects all
four-caps outside that pencil. It does not concern the unrestricted global
twenty-six-input separator directly.

Let U contain the OR gates that are false on at least one four-cap. Keep their
singleton supports. Every output/cap separation witness lies in U: an output
is a free conjunction of input and OR wires, and an input wire cannot contain
all four positive target singletons.

Let e count the distinct pencils appearing exactly as singleton supports of
gates in U. The checked local guard-charging argument gives at least
3(13-e) useful guards for the remaining active targets. An exact-pencil gate
cannot be one of these guards because distinct pencils intersect in one line.
Thus e distinct exact-pencil representatives are disjoint from those guards.

Choose the first OR gate in U whose singleton support contains any whole
pencil. Such a gate exists by separation. It is false on a four-cap and accepts
the four pencil singletons. Apply the checked false-baseline sensitivity count
to the circuit prefix ending at that gate: at least three OR gates are false
on that same cap and merge its four singleton inputs. At most one is the last
gate, so two are earlier. Neither earlier gate can have a singleton support
containing any whole pencil, by the choice of the first gate. They are thus
disjoint from the active guards and from all exact-pencil representatives.

Consequently the total OR count k satisfies

    k >= 3(13-e) + e + 2 = 41 - 2e.

For k <= 38, this forces e >= 2. Singer translation may normalize one useful
exact pencil to P0; the second remains any distinct pencil. Fixing a second
specific pencil would require a separate joint symmetry argument.

The new unformalized step is prefix use of the existing sensitivity count and
the ensuing disjoint-cardinality aggregation. The local guard count and the
ordinary sensitivity theorem themselves are already checked.
