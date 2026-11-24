# Simultaneous paid-source clamping for four exceptional outputs

This is a mathematical reduction, not yet a Lean proof or a complete
39-gate lower bound.

Assume a correct circuit has s at most 38 gates, exactly four exceptional
outputs, and nine globally exact line-OR outputs. First apply output-sink
normalization, preserving all band outputs and the nine globally exact
outputs. Let P be the union of the nine ordinary charge families. Then
|P| is at least 27, every exceptional output gate lies outside P, and
there are at most eleven unpaid gates.

Fix an exceptional line L. Since the other three exceptional outputs are
sinks, they can be excluded from its cut computation. Equivalently add
their indices to the cut set; their free coordinates are unused. Its cut
function F_L therefore has at most eight unpaid gates and at most nine
essential source coordinates E_L. Clamp9 then forces its four raw L
variables to be essential. There are at most five remaining coordinates.
Each remaining source has a positive singleton witness outside L, whether
it is a raw outside input or an ordinary paid gate.

Set the raw L variables to zero and all remaining essential coordinates
to one. F_L is false at this abstract valuation: choose one outside
singleton witness per remaining coordinate (at most five points), extend
their union to eight true points outside L, and use monotonicity. All
foreign source values are one at this negative band input, while the four
raw L values are zero. Correctness gives false.

Now clamp ALL paid sources to one simultaneously, while retaining every
raw input as a variable. Call the resulting output H_L(x). The preceding
false valuation gives H_L(x) <= OR_L(x) on the whole cube. On a band input,
the clamp only increases the original paid source values, so H_L(x) is at
least the original output OR_L(x). Hence H_L is still band-correct.
This argument applies simultaneously to all four exceptional outputs.

Physically implement this clamp only in the reduced four-output problem:
delete paid gates, replace their uses by symbolic constant one, and
propagate constants through unpaid gates. A nonconstant gate either keeps
its operation or becomes a unary copy of an existing wire; a constant
gate can be deleted. Forward/invalid references retain their original
constant-zero meaning. Thus no new gates are needed. Retain a unary copy
at each exceptional output if simplification would otherwise identify it
with an earlier wire; the four original unpaid output slots pay for these
copies and remain sinks. The resulting raw-input circuit has at most
s-|P| <= 11 gates and four distinct output sinks, all globally below their
line OR and correct on the band.

If desired, rebuild the nine ordinary outputs independently with 27 OR
gates. The resulting full circuit uses at most s-|P|+27 <= s gates and
preserves all thirteen band outputs. It does not attempt to preserve
intermediate paid-gate functions, which is what avoids the unpaid-to-paid
feedback obstruction.

If any of the four reduced outputs is globally exact, the rebuilt full
circuit has at most three exceptional outputs and is excluded by the
existing three-exception theorem. Therefore a remaining four-exception
counterexample reduces to a raw-input circuit with at most eleven gates,
four output sinks, and four globally bounded but nonexact outputs. Each
such output depends on at least eight raw inputs. There are at most seven
internal gates. Proving this final reduced configuration impossible is
still open in this note.

Before clamping, the four essential source sets are connected through the
raw intersection point of every pair of target lines. The cut component
bound gives at most twelve essential sources in their union. Four distinct
projective lines contain at least ten raw points, leaving at most two paid
essential sources in that union. This is an additional possible constraint
on the reduced configuration, not needed for the clamping argument.
