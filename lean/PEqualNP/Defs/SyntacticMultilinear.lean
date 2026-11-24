import Mathlib.Data.Finset.Disjoint
import PEqualNP.Defs.EdgeOwnership

/-!
# The support of a wire, and syntactically multilinear AND/OR circuits

The setting. A circuit of the root model (`PEqualNP.Defs.CircuitLowerBounds`) on the inputs
`Fin n`: wire `i < n` is the input `x_i`, gate number `j` is wire `n + j`, and a gate reads the
wires named in its input list (a wire that does not exist yet reads `false`).

The objects (a notion of the fleet, founders' point 0i).
* The SUPPORT of a wire is the set of input indices from which it can be reached: the support of
  input `i` is `{i}`, the support of a gate is the union of the supports of the wires it reads.
* The circuit is SYNTACTICALLY MULTILINEAR when every AND gate reads operands with pairwise
  disjoint supports. For an AND gate of fan-in two, `x AND y`, this is exactly: the supports of
  `x` and `y` are disjoint.

Names.
* `supports n C`: the list of the supports of all wires of `C`, inputs first, then one per
  gate, computed by one forward pass in gate order.
* `support n C w : Finset (Fin n)`: the support of wire `w` (empty past the last wire).
* `operandSupport n C j w`: the support of wire `w` AS READ BY gate number `j`: the support of
  `w` if `w < n + j` (the wire exists when gate `j` is evaluated), empty otherwise.
* `AndOperandsDisjoint n C j`: the operands of gate `j` have pairwise disjoint supports (read
  position by position, so a wire read twice is compared with itself).
* `IsSyntMultilinear n C`: every AND gate of `C` satisfies `AndOperandsDisjoint`. Decidable.

Caveats a statement must respect.
* MISSING WIRES. A wire index at or past the gate's own wire `n + j` reads `false` in the root
  model; it is given EMPTY support, both in the forward pass (`supports` looks such a wire up in
  the list built so far, which does not reach it) and in the condition (`operandSupport`). This
  agrees with `InCone` of `PEqualNP.Defs.EdgeOwnership`, which ignores such reads. A wire of
  empty support (a missing wire, or a gate with no inputs, a constant) is disjoint from every
  support, itself included: an AND reading it twice is allowed.
* FAN-IN. The condition is PAIRWISE over the operand positions (`List.Pairwise` on the input
  list). Fan-in two: the two supports are disjoint. Fan-in zero or one: no condition. Fan-in
  `k > 2`: every two of the `k` positions carry disjoint supports. A wire read at two positions
  is compared with itself, so an AND reading the same non-constant wire twice (`AND(y, y)`) is
  NOT multilinear.
* OTHER GATES. Only AND gates are constrained. OR, NOT, MOD and MAJORITY gates carry no
  condition, and their support is still the union of their operands' supports. The thinker's
  notion is for AND/OR circuits: state `AndOrOnly C` (edge ownership module) and fan-in two
  (`PEqualNP.MetaComplexity.FanInTwo C`) as hypotheses. With NOT gates the notion is defined
  (a NOT gate passes its operands' support through) but is not the thinker's.
* SYNTACTIC, NOT SEMANTIC. The support counts every input a wire can reach, whether or not the
  wire's function depends on it (`x0 OR (x0 AND x1)` has support `{0, 1}`). The condition reads
  all gates, including gates no output depends on.
* Inputs have length exactly `n`: the number of inputs `n` is an argument and must be the `n`
  of the circuit's input list.
-/

namespace PEqualNP.SyntacticMultilinear

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

attribute [local instance] gateOpDecEq

/-- One step of the forward pass: given the supports `s` of the wires so far (the next gate is
wire `s.length`), the support of gate `g` is the union of the supports of the wires it reads; a
wire not yet in `s` contributes nothing. -/
def supportStep {n : ℕ} (s : List (Finset (Fin n))) (g : Gate) : List (Finset (Fin n)) :=
  s ++ [g.inputs.foldr (fun w acc => s.getD w ∅ ∪ acc) ∅]

/-- The supports of all wires of `C` on `n` inputs: input `i` has support `{i}`, then one support
per gate, in gate order. -/
def supports (n : ℕ) (C : Circuit) : List (Finset (Fin n)) :=
  C.gates.foldl supportStep (List.ofFn fun i : Fin n => ({i} : Finset (Fin n)))

/-- The SUPPORT of wire `w` of `C` on `n` inputs: the input indices from which `w` can be
reached. Empty for a wire past the last one. -/
def support (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  (supports n C).getD w ∅

/-- The support of wire `w` as read by gate number `j` (wire `n + j`): the support of `w` if it
is an earlier wire, empty otherwise (a wire at or past `n + j` reads `false`). -/
def operandSupport (n : ℕ) (C : Circuit) (j w : ℕ) : Finset (Fin n) :=
  if w < n + j then support n C w else ∅

/-- The operands of gate number `j` of `C` have pairwise disjoint supports, position by
position. -/
def AndOperandsDisjoint (n : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  (gateAt C j).inputs.Pairwise fun a b => Disjoint (operandSupport n C j a) (operandSupport n C j b)

instance (n : ℕ) (C : Circuit) (j : ℕ) : Decidable (AndOperandsDisjoint n C j) := by
  unfold AndOperandsDisjoint; infer_instance

/-- `C` is SYNTACTICALLY MULTILINEAR on `n` inputs: every AND gate reads operands with pairwise
disjoint supports. -/
def IsSyntMultilinear (n : ℕ) (C : Circuit) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → AndOperandsDisjoint n C j

instance (n : ℕ) (C : Circuit) : Decidable (IsSyntMultilinear n C) := by
  unfold IsSyntMultilinear; infer_instance

end PEqualNP.SyntacticMultilinear
