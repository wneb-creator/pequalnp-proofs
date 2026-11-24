import PEqualNP.Defs.EdgeOwnership

/-!
# Dirty gates and cleaned non-edges of an AND/OR circuit on a graph

The setting. A circuit of the root model (`PEqualNP.Defs.CircuitLowerBounds`) on the inputs
`Fin n`: wire `i < n` is the input `x_i`, gate number `j` is wire `n + j`, and a gate reads the
wires named in its input list (a wire that does not exist yet reads `false`). The inputs are the
vertices of a graph `G` on `Fin n`; `f_G = graphFun G ∅` (nested cover module) is the edge
function of `G`: true exactly when both ends of some edge are true. The circuit is meant to
compute `f_G` or to stay below it.

The object (a notion of the fleet, founders' point 0i). A gate is DIRTY when it is not
pointwise below `f_G`. For a non-edge `{u, v}` the CLEANERS of `u, v` are the vertices of
`N(u) ∪ N(v)`. A gate `g` and a non-edge `{u, v}` form a CLEANED NON-EDGE when
(a) `g ≤ f_G ∨ (x_u ∧ x_v)` pointwise (the only dirt `g` can carry is `x_u x_v`), and
(b) every AND gate that reads `g` has its other side pointwise below `OR_{w ∈ N(u) ∪ N(v)} x_w`.
The thinker's reason for the name: `x_u x_v x_w` with `w` a cleaner contains an edge, so the
dirt of `g` is cleaned at every AND that reads it.

READING THROUGH ORs. In the thinker's model a side of an AND is an OR of variables and earlier
gates; in the root model (fan-in two) that side is a tree of OR gates. So "an AND gate reads `g`"
is taken here THROUGH OR GATES: the AND gate has an input wire whose OR CLOSURE contains `g`,
where the OR closure of the wire of gate `k` is `{k}` if `k` is not an OR gate, and `{k}` with
the OR closures of its (earlier) gate inputs if `k` is an OR gate. Input wires have empty OR
closure. With the literal reading (the AND's input wire is `g`'s own wire) a fan-in-two circuit
built from the thinker's sides would satisfy (b) vacuously.

* `wireVal n C w x`: the value of wire `w` at the input `x` (`false` if the wire does not exist).
* `readVal n C a w x`: the value gate `a` reads from wire `w`: `wireVal` if `w < n + a`, else
  `false` (a wire not yet computed when gate `a` is evaluated reads `false`, as in the root model).
* `IsDirty n G C j`: gate `j` exists and is true at some input where `f_G` is false.
* `IsDirtyAnd n G C j`: gate `j` is an AND gate and is dirty (see the caveat on OR gates).
* `cleaners G u v`: the finset `N(u) ∪ N(v)`.
* `cleanerOr G u v x`: the OR of `x_w` over the cleaners.
* `orStep`, `orSets n C`: gate by gate, the OR closure of each gate's wire (as a list).
* `OrReaches n C w g`: gate `g` lies in the OR closure of wire `w`.
* `ReadsAt n C a p g`: gate `a` is an AND gate, `p` is a position of its input list, the wire
  at position `p` was computed before `a` and gate `g` lies in its OR closure.
* `otherSide n C a p x`: the AND of the values gate `a` reads at every position other than `p`.
* `IsCleanedNonEdge n G C j u v`: the definition above, conditions (a) and (b), with `u ≠ v`,
  `¬ G.Adj u v` and `j < C.gates.length`. Decidable when `G.Adj` is.
* `OrToOutput n C j`: gate `j` lies in the OR closure of the output wire (its dirt can reach the
  output through ORs alone, where (b) does not look).

Caveats a statement must respect.
* DIRTINESS IS NOT REQUIRED in `IsCleanedNonEdge`. A gate below `f_G` meets (a) for every
  non-edge, so a clean gate is a cleaned non-edge with every non-edge whose cleaners dominate
  its readers' other sides. Requiring dirtiness would make the notion non-monotone under
  "cleaning" a gate and would hide that (b) is a condition on the READERS, not on the gate;
  state `IsDirty n G C j` as a separate conjunct when the dirty case is meant.
* OR GATES ARE DIRTY. In the root model a side `x_a + x_b` of an AND is its own OR gate, and it
  is dirty (true at `1_a`, where `f_G` is false). So `IsDirty` holds for most OR gates of any
  circuit; the thinker's "dirty gate" (a product not below `f_G`) is `IsDirtyAnd`.
* Gate index vs wire: `j` and `a` are gate indices (wire `n + j`); `w` and the entries of an
  input list are wire indices. `n` must be the number of inputs of the circuit.
* FAN-IN. The other side at position `p` is the AND of ALL the other positions (for fan-in two:
  the remaining entry). An AND of fan-in one reading `g` has other side `true`, which is never
  below the cleaners (at the all-false input), so it violates (b): it passes the dirt on. An
  AND that reads `g` at two positions is checked at each position separately, and its other
  side then includes the other read of `g`: such a gate meets (b) only if that side really is
  below the cleaners. Duplicate positions are distinguished by position, not by wire.
* Only AND and OR gates are meant (`AndOrOnly C` as a hypothesis). A NOT, MOD or MAJ gate reading
  `g` is not a reader in (b), and does not pass the OR closure on.
* (b) sees ANDs only. A dirty gate in the OR closure of the output wire (`OrToOutput`), or a
  dirty gate that is itself the output, is not excluded by `IsCleanedNonEdge`; any statement
  that the circuit stays below `f_G` must exclude it separately.
* Missing wires read `false`: a gate index at or past `C.gates.length` is never dirty and is
  never a cleaned non-edge (the conjunct `j < C.gates.length`).
* The pointwise orders quantify over all `2^n` inputs `Fin n → Bool`.
-/

namespace PEqualNP.CleanedNonEdge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership

attribute [local instance] gateOpDecEq

/-- The value of wire `w` of `C` at the input `x` on `n` inputs (`false` if it does not exist). -/
def wireVal (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

/-- The value gate `a` reads from wire `w` at the input `x`: the wire's value if it was computed
before gate `a` (`w < n + a`), else `false`. -/
def readVal (n : ℕ) (C : Circuit) (a w : ℕ) (x : Fin n → Bool) : Bool :=
  if w < n + a then wireVal n C w x else false

/-- Gate `j` of `C` is DIRTY for `G`: it exists and is true at some input where the edge
function of `G` is false. -/
def IsDirty (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) :
    Prop :=
  j < C.gates.length ∧ ∃ x : Fin n → Bool, gateVal n C j x = true ∧ graphFun G ∅ x = false

instance (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) :
    Decidable (IsDirty n G C j) := by
  unfold IsDirty; infer_instance

/-- Gate `j` of `C` is a DIRTY AND gate for `G`: an AND gate that is dirty. (In the root model
the sides of an AND are OR gates, and an OR of variables is always dirty; the thinker's "dirty
gate" is a dirty product, which is this.) -/
def IsDirtyAnd (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) :
    Prop :=
  (gateAt C j).op = GateOp.and ∧ IsDirty n G C j

instance (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) :
    Decidable (IsDirtyAnd n G C j) := by
  unfold IsDirtyAnd; infer_instance

/-- The CLEANERS of `u, v`: the vertices adjacent to `u` or to `v`. -/
def cleaners {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun w => G.Adj u w ∨ G.Adj v w

/-- The OR of `x_w` over the cleaners of `u, v`. -/
def cleanerOr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n)
    (x : Fin n → Bool) : Bool :=
  decide (∃ w ∈ cleaners G u v, x w = true)

/-- One step of the OR closure computation: given the OR closures `cs` of the gates so far
(gate `cs.length` is the next one), the OR closure of gate `g` is `[cs.length]` if `g` is not an
OR gate, and `cs.length` followed by the OR closures of its earlier gate inputs if it is. -/
def orStep (n : ℕ) (cs : List (List ℕ)) (g : Gate) : List (List ℕ) :=
  cs ++ [cs.length :: (if g.op = GateOp.or then
    (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => cs.getD (w - n) [])
    else [])]

/-- The OR closures of all gates of `C` on `n` inputs, in gate order. -/
def orSets (n : ℕ) (C : Circuit) : List (List ℕ) :=
  C.gates.foldl (orStep n) []

/-- Gate `g` lies in the OR closure of wire `w`: `w` is the wire of gate `g`, or of an OR gate
one of whose earlier gate inputs has `g` in its OR closure. Input wires reach no gate. -/
def OrReaches (n : ℕ) (C : Circuit) (w g : ℕ) : Prop :=
  n ≤ w ∧ g ∈ (orSets n C).getD (w - n) []

instance (n : ℕ) (C : Circuit) (w g : ℕ) : Decidable (OrReaches n C w g) := by
  unfold OrReaches; infer_instance

/-- Gate `a` is an AND gate of `C` that reads gate `g` (through OR gates) at position `p` of its
input list, the wire at that position having been computed before `a`. -/
def ReadsAt (n : ℕ) (C : Circuit) (a p g : ℕ) : Prop :=
  a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ p < (gateAt C a).inputs.length ∧
    (gateAt C a).inputs.getD p 0 < n + a ∧ OrReaches n C ((gateAt C a).inputs.getD p 0) g

instance (n : ℕ) (C : Circuit) (a p g : ℕ) : Decidable (ReadsAt n C a p g) := by
  unfold ReadsAt; infer_instance

/-- The OTHER SIDE of gate `a` at position `p`: the AND of the values `a` reads at every
position of its input list other than `p`. -/
def otherSide (n : ℕ) (C : Circuit) (a p : ℕ) (x : Fin n → Bool) : Bool :=
  ((gateAt C a).inputs.eraseIdx p).all fun w => readVal n C a w x

/-- Gate `j` of `C` and the non-edge `{u, v}` of `G` form a CLEANED NON-EDGE:
(a) gate `j` is pointwise below `f_G ∨ (x_u ∧ x_v)`, and (b) every AND gate reading gate `j`
(through OR gates) has its other side pointwise below the OR of the cleaners of `u, v`. -/
def IsCleanedNonEdge (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : ℕ) (u v : Fin n) : Prop :=
  j < C.gates.length ∧ u ≠ v ∧ ¬ G.Adj u v ∧
    (∀ x : Fin n → Bool, gateVal n C j x = true →
      graphFun G ∅ x = true ∨ (x u = true ∧ x v = true)) ∧
    (∀ a < C.gates.length, ∀ p < (gateAt C a).inputs.length, ReadsAt n C a p j →
      ∀ x : Fin n → Bool, otherSide n C a p x = true → cleanerOr G u v x = true)

instance (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ)
    (u v : Fin n) : Decidable (IsCleanedNonEdge n G C j u v) := by
  unfold IsCleanedNonEdge; infer_instance

/-- Gate `j` lies in the OR closure of the output wire of `C`: its value reaches the output
through OR gates alone. -/
def OrToOutput (n : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  OrReaches n C C.output j

instance (n : ℕ) (C : Circuit) (j : ℕ) : Decidable (OrToOutput n C j) := by
  unfold OrToOutput; infer_instance

end PEqualNP.CleanedNonEdge
