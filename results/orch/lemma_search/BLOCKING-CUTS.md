# Checked single-reader constraints

Use `../lemmas/BlockingAll.lean`, SHA256
`68527669db4674208e15e8768ae5abf788ff79cb35273142b3efdec9c6d3cc6a`.
It includes all preceding blocking files under its own namespace. Lean exited0
and independent review passed. The complete build log is `blocking-all-build.log`;
the sixteen diagnostics are inherited deprecated-tactic-name warnings.

These are necessary local conditions for a circuit computing the exact19-edge
target. Arbitrary NOT gates elsewhere are allowed. They do not establish a new
global size bound or a bound on the number of NOT gates.

Assume primary p has exactly one reader gate r and the circuit output is not the
primary p. In a normal synthesis encoding with output the last gate, this output
condition holds automatically. A reader means membership in the actual gate
input list; NOT has one actual input.

| Other input of r | Necessary condition |
|---|---|
| Distinct primary q | r is neither AND nor OR |
| Earlier NOT(q), q distinct from p | r is neither AND nor OR |
| AND gate reading distinct primary q | r cannot be AND |
| Earlier OR gate reading distinct primary q | r cannot be OR |
| Earlier OR(a,b), a,b primary, and p has degree3 | r cannot be AND |
| Earlier AND(a,b), a,b primary, and p has degree3 | If r is OR, then {a,b} is a target edge |

The degree-three vertices are `{2,3,4,5,6,8,10,11,12,13}`.
For the last two rows, a or b equal to p is automatically impossible by the sole
reader and earlier-child conditions; the theorem derives this fact.

The first row means that any AND/OR gate on two distinct primary inputs must
give each primary another reader elsewhere. Counting an unused NOT selector
slot as a reader only weakens this cut, but does not implement the exact predicate.

The semantic argument is robust dependence: after fixing any distinct input q to
either Boolean value, the target still depends on p. A sole reader cannot be
disabled by that assignment. The degree-three refinements use singleton and
independent-pair witnesses, checked by the Lean kernel.

The constraints deliberately do not claim that read-once inputs form an
independent set in arbitrary circuits. Shared dirty masks can create adjacent
read-once inputs, even in monotone circuits; any such global argument needs an
additional minimality or gate-cost analysis.
