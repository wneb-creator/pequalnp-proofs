import PEqualNP.Defs.TopForm

/-!
# Names for the one-junk steps: FORM-u vertices, FORM-z vertices, the penalty set, the cone gates

The setting is the one of `PEqualNP.Defs.TopForm` (read its header first): a circuit `C` of the
root model on the inputs `Fin n`, a graph `G` on `Fin n`, `F = graphFun G ∅`, and a gate index `g`
(in the steps, the one junk AND gate: `junk G C = {g}`). These four names are the ones Steps 10
and 11 of the formula-bound steps write, with the same binders and the
same argument order (`G`, then `C`, then `g`, then `K` for `pen`).

* `formU G C g`: the vertices `u` that are a one-input side of some top: a top `a` and a position
  `b` with `side C a b = {u}`, the operand at `b` reaching gate `g` through OR gates (`OrReaches`,
  which counts the operand's own gate, so an operand that IS the wire of `g` reaches `g`).
* `formZ G C g`: the vertices `w` that are the one-input side of a top whose OTHER operand reaches
  `g` through OR gates and reaches two or more inputs: a top `a` and a position `b` with
  `2 ≤ (side C a b).card`, the operand at `b` reaching `g`, and `side C a (1 - b) = {w}`.
* `pen G C g K`: the penalised vertices for a set `K`: the `u` in `formU G C g` with a neighbour
  `v` such that the edge `uv` is not in `Ustar G C` (so it is some top's cross pair), `v` is not in
  `wmax G C g` and `v` is not in `K`.
* `coneGates G C g`: the OR gates not below `F`, outside `lam G C` and not mixing, that lie in the
  OR closure of an operand of `g`, or in the OR closure of the filter operand `1 - b` of a
  centreless top that reads the wire `n + g` at position `b`.

Caveats a statement must respect.
* Everything inherits the caveats of `TopForm`: `opnd` defaults to wire `0` (the input `x_0`) past
  the input list or past the last gate, so `opnd C g 0` and `opnd C g 1` name the operands of `g`
  only when `g` is a real gate with exactly two inputs (under `IsAO2`). `side` and `orIn` stop at
  AND gates; an input wire reaches only itself; a wire past the last gate reaches nothing.
* `OrReaches n C w g` is false when `w` is an input wire (`w < n`): an operand that is an input
  reaches no gate, so a top whose operand at `b` is an input never puts a vertex in `formU` or
  `formZ` through that operand.
* `formZ` uses `(side (n := n) C a b).card`, since nothing else fixes `n` there. `1 - b` is
  subtraction in `Fin 2`, the other position.
* `pen` reads `s(u, v) ∉ Ustar G C` and `G.Adj u v`; it does not require `uv` to be a star edge
  directly, though for an edge of `G` the two say the same (`Ustar` is `E` minus the star edges).
  `wmax` quantifies over all `2^n` inputs.
* `coneGates` is a set of gate indices below `C.gates.length` (a subset of `orN G C`); the clause
  for centreless tops quantifies over the position `b` at which the top reads `n + g`.
* Nothing here asserts that `g` is junk, that `C` is least, or that `C` is in top form: those are
  hypotheses of the steps, not of the names.
-/

namespace PEqualNP.TopForm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

attribute [local instance] gateOpDecEq

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

/-- FORM-u: the vertices `u` that are a one-input side of a top whose operand on that side reaches
gate `g` through OR gates. -/
def formU (g : ℕ) : Finset (Fin n) := Finset.univ.filter fun u =>
  ∃ a ∈ tops G C, ∃ b : Fin 2, side C a b = {u} ∧ OrReaches n C (opnd C a b) g

/-- FORM-z: the vertices `w` that are the one-input side of a top whose other operand reaches gate
`g` through OR gates and reaches two or more inputs. -/
def formZ (g : ℕ) : Finset (Fin n) := Finset.univ.filter fun w =>
  ∃ a ∈ tops G C, ∃ b : Fin 2, 2 ≤ (side (n := n) C a b).card ∧ OrReaches n C (opnd C a b) g ∧
    side C a (1 - b) = {w}

/-- The penalised vertices for `K`: the FORM-u vertices `u` with a neighbour `v` such that `uv` is
a star edge (not in `U*`), `v` is not in `Wmax(g)` and `v` is not in `K`. -/
def pen (g : ℕ) (K : Finset (Fin n)) : Finset (Fin n) := (formU G C g).filter fun u =>
  ∃ v, G.Adj u v ∧ s(u, v) ∉ Ustar G C ∧ v ∉ wmax G C g ∧ v ∉ K

/-- The cone gates: OR gates not below `F`, outside Lambda and not mixing, in the OR closure of an
operand of `g` or of the filter operand of a centreless top reading `g`. -/
def coneGates (g : ℕ) : Finset ℕ := ((orN G C \ lam G C) \ mixing G C).filter fun h =>
  OrReaches n C (opnd C g 0) h ∨ OrReaches n C (opnd C g 1) h ∨
  ∃ a ∈ centreless G C, ∃ b : Fin 2, opnd C a b = n + g ∧ OrReaches n C (opnd C a (1 - b)) h

end PEqualNP.TopForm
