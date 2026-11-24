import PEqualNP.Defs.CleanedNonEdge
import PEqualNP.Defs.MetaComplexityMinimal

/-!
# Top form, junk AND gates, operand input sets, star edges and Lambda

The setting is the one of `PEqualNP.Defs.EdgeOwnership` and `PEqualNP.Defs.CleanedNonEdge`: a
circuit of the root model (`PEqualNP.Defs.CircuitLowerBounds`) on the inputs `Fin n`; wire `i < n`
is the input `x_i`, gate number `j` is wire `n + j`, a gate reads the wires named in its input
list, and a wire that does not exist yet when a gate is evaluated reads `false`. The inputs are the
vertices of a graph `G` on `Fin n`; `F = f_G = graphFun G ∅` is the edge function of `G` (true
exactly when both ends of some edge are true). Later statements apply these definitions by these
names and in this argument order.

THE MODEL. `IsAO2 n C`: every gate is an AND or an OR gate, every gate reads only earlier wires,
and every gate reads EXACTLY two wires (repetitions allowed). There are no constant gates and no NOT
gates; every gate is counted, inputs are free. This is not the public `Monotone2` class (which
allows fan-in at most two); `IsLeastAO` is least size within this model only.

* `NoFourCycle G`: two distinct vertices have at most one common neighbour.
* `IsAO2 n C`: the model above.
* `BelowF G C j`: gate `j` is BELOW `F`: wherever it is true, `F` is true.
* `IsLeastAO G C`: `C` is in the model, computes `F`, and no circuit of the model computing `F` is
  smaller.
* `TopForm G C`: no AND gate below `F` lies strictly inside the cone (`InCone`) of an AND gate.
* `andPairs n C`: the number of ordered pairs of AND gates `(i, j)` with `i` strictly inside the
  cone of `j`.
* `gatesWhere C P`: the gate indices `j < C.gates.length` with `P j`.
* `junk G C`: the JUNK AND gates: AND gates not below `F` (`IsDirtyAnd`).
* `tops G C`: the TOPS: AND gates below `F`.
* `orT G C`, `orN G C`: the OR gates below `F`, and the OR gates not below `F`.
* `readers n C j`: the gates whose input list contains the wire `n + j` of gate `j`.
* `opnd C a b`: operand `b` (`0` or `1`) of gate `a`: the wire at position `b` of its input list.
* `orIn n C w`: `S_in(w)`, the inputs reached from wire `w` through OR gates: `w` itself if it is
  an input, and every input read by an OR gate in the OR closure of `w` (`OrReaches`, which stops
  at non-OR gates).
* `side C a b`: `orIn` of operand `b` of gate `a`.
* `centreless G C`: the tops with a side reaching no input.
* `starEdges G C`: the cross pairs `{u, v}`, `u` in side 0 and `v` in side 1, over all tops.
* `Ustar G C`: `U*`, the edges of `G` that are no top's cross pair.
* `lam G C`: Lambda: the OR gates not below `F` whose two operands both reach an input, lying in
  the OR closure of an operand of a top whose OTHER side reaches exactly one input.
* `mixing G C`: the OR gates not below `F` exactly one of whose operands reaches no input.
* `gammaE G C g`: the edges `uv` of `G` with gate `g` true at the input `1_uv`.
* `wmax G C g`: `Wmax(g)`, the vertices `w` with `g AND x_w` below `F`.

Caveats a statement must respect.
* `opnd` reads position `b` of the input list with default `0`: for a gate with fewer than
  `b + 1` inputs, or an index past the last gate (`gateAt` gives an OR gate with no input), it
  returns `0`, the wire of the input `x_0`. Only under `IsAO2` (exactly two inputs) and for a real
  gate does `opnd` name a real operand.
* `junk` uses `IsDirtyAnd` of `CleanedNonEdge`: an AND gate true at some input where `F` is
  false. For a real AND gate this is exactly "not `BelowF`".
* `lam` takes ALL OR gates (not below `F`, both operands reaching an input) in the OR closure of the
  leaf operand, with no order among them; this only enlarges Lambda.
* `orIn` and `side` stop at AND gates, because `OrReaches` does; an input wire reaches only
  itself; a wire past the last gate reaches nothing.
* Missing wires read `false`: `gateVal` of an index past the last gate is `false`, so such an index
  is `BelowF`; the finsets above only range over `j < C.gates.length`.
* `BelowF`, `wmax` and the decidability instances quantify over all `2^n` inputs.
* `side C a b` has `n` implicit and `C` does not carry it: where nothing else fixes `n` (for
  instance `(side C a b).card` alone) write `side C a b`.
-/

namespace PEqualNP.TopForm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

attribute [local instance] gateOpDecEq

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

/-- `G` has no 4-cycle: two distinct vertices have at most one common neighbour. -/
def NoFourCycle : Prop :=
  ∀ a b : Fin n, a ≠ b → (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card ≤ 1

instance : Decidable (NoFourCycle G) := by unfold NoFourCycle; infer_instance

/-- The model: AND and OR gates only, each reading earlier wires, each reading exactly two wires.
No constants, no NOT; not the public `Monotone2` (fan-in at most two). -/
def IsAO2 (n : ℕ) (C : Circuit) : Prop :=
  AndOrOnly C ∧ ReadsBack n C ∧ ∀ g ∈ C.gates, g.inputs.length = 2

instance (n : ℕ) (C : Circuit) : Decidable (IsAO2 n C) := by unfold IsAO2; infer_instance

/-- Gate `j` is below `F = graphFun G ∅`: wherever it is true, `F` is true. -/
def BelowF (j : ℕ) : Prop := ∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true

instance (j : ℕ) : Decidable (BelowF G C j) := by unfold BelowF; infer_instance

/-- `C` is a least circuit for `F` in the no-constant, fan-in-exactly-two AND/OR model `IsAO2`
(not the public `Monotone2`): it is in the model, computes `F`, and every circuit of the model
computing `F` has at least as many gates. -/
def IsLeastAO : Prop := IsAO2 n C ∧ circuitFun n C = graphFun G ∅ ∧
  ∀ C' : Circuit, IsAO2 n C' → circuitFun n C' = graphFun G ∅ → C.size ≤ C'.size

/-- Top form: no AND gate below `F` lies strictly inside the cone of an AND gate. -/
def TopForm : Prop := ∀ i < C.gates.length, ∀ j < C.gates.length,
  (gateAt C i).op = GateOp.and → BelowF G C i → (gateAt C j).op = GateOp.and → ¬ InCone n C i j

instance : Decidable (TopForm G C) := by
  unfold TopForm
  have : ∀ i : ℕ, Decidable (∀ j < C.gates.length, (gateAt C i).op = GateOp.and → BelowF G C i →
      (gateAt C j).op = GateOp.and → ¬ InCone n C i j) := fun _ => inferInstance
  infer_instance

/-- The number of ordered pairs of AND gates `(i, j)` with `i` strictly inside the cone of `j`. -/
def andPairs (n : ℕ) (C : Circuit) : ℕ :=
  ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter fun p =>
    (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2).card

/-- The gate indices `j < C.gates.length` with `P j`. -/
def gatesWhere (P : ℕ → Prop) [DecidablePred P] : Finset ℕ := (Finset.range C.gates.length).filter P

/-- The junk AND gates: AND gates not below `F` (`IsDirtyAnd`). -/
def junk  := gatesWhere C fun j => IsDirtyAnd n G C j
/-- The tops: AND gates below `F`. -/
def tops  := gatesWhere C fun j => (gateAt C j).op = GateOp.and ∧ BelowF G C j
/-- The OR gates below `F`. -/
def orT   := gatesWhere C fun j => (gateAt C j).op = GateOp.or ∧ BelowF G C j
/-- The OR gates not below `F`. -/
def orN   := gatesWhere C fun j => (gateAt C j).op = GateOp.or ∧ ¬ BelowF G C j

/-- The gates whose input list contains the wire `n + j` of gate `j`. -/
def readers (n : ℕ) (C : Circuit) (j : ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun k => n + j ∈ (gateAt C k).inputs

/-- Operand `b` of gate `a`: the wire at position `b` of its input list (default `0`). -/
def opnd (C : Circuit) (a : ℕ) (b : Fin 2) : ℕ := (gateAt C a).inputs.getD b 0

/-- S_in: the inputs reached from wire `w` through OR gates. -/
def orIn (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => (i : ℕ) = w ∨ ∃ k < C.gates.length,
    OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs

/-- The inputs reached through OR gates from operand `b` of gate `a`. -/
def side (a : ℕ) (b : Fin 2) : Finset (Fin n) := orIn n C (opnd C a b)

/-- The tops with a side reaching no input. -/
def centreless := (tops G C).filter fun a => side (n := n) C a 0 = ∅ ∨ side (n := n) C a 1 = ∅

/-- The cross pairs of the tops. -/
def starEdges : Finset (Sym2 (Fin n)) :=
  (tops G C).biUnion fun a => (side C a 0 ×ˢ side C a 1).image fun p => s(p.1, p.2)

/-- U*: the edges of `G` that are no top's cross pair. -/
def Ustar := G.edgeFinset \ starEdges G C

/-- Lambda: OR gates outside T with both children reaching inputs, inside the leaf operand of a top
whose other operand reaches exactly one input. -/
def lam := (orN G C).filter fun h => (orIn n C (opnd C h 0)).Nonempty ∧ (orIn n C (opnd C h 1)).Nonempty ∧
  ∃ a ∈ tops G C, ∃ b : Fin 2, (side (n := n) C a (1 - b)).card = 1 ∧ OrReaches n C (opnd C a b) h

/-- The mixing gates: OR gates not below `F` exactly one of whose operands reaches no input. -/
def mixing := (orN G C).filter fun m =>
  (orIn n C (opnd C m 0) = ∅) ≠ (orIn n C (opnd C m 1) = ∅)

/-- The edges `uv` of `G` with gate `g` true at the input `1_uv`. -/
def gammaE (g : ℕ) : Finset (Sym2 (Fin n)) :=
  G.edgeFinset.filter fun e => ∃ u v, e = s(u, v) ∧ gateVal n C g (pairInput u v) = true

/-- Wmax(g): the vertices `w` with `g AND x_w` below `F`. -/
def wmax (g : ℕ) : Finset (Fin n) := Finset.univ.filter fun w =>
  ∀ x : Fin n → Bool, gateVal n C g x = true → x w = true → graphFun G ∅ x = true

end PEqualNP.TopForm
