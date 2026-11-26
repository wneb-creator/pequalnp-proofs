import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17844_aux

open PEqualNP.CircuitLowerBounds

theorem len_foldl (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length
      = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

theorem key (x3 : Circuit) (W0 : List Bool) (hW0 : W0.length = 11) (a b : ℕ) :
    (x3.wires W0 ++ [GateOp.or.eval ([a, b].map fun i => (x3.wires W0).getD i false)]).getD
      (11 + x3.gates.length) false = ((x3.wires W0).getD a false || (x3.wires W0).getD b false) := by
  have hl : (x3.wires W0).length = 11 + x3.gates.length := by
    rw [Circuit.wires, len_foldl, hW0]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hl, GateOp.eval]

theorem split (g1 g3 : Gate) (x3 : Circuit) (x : List Bool) (o : ℕ) :
    Circuit.wires { gates := [g1] ++ x3.gates ++ [g3], output := o } x
      = x3.wires (Circuit.wires { gates := [g1], output := 0 } x) ++
        [g3.op.eval (g3.inputs.map fun i =>
          (x3.wires (Circuit.wires { gates := [g1], output := 0 } x)).getD i false)] := by
  simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]

end PEqualNP.Outside.L_meta_17844_aux

theorem PEqualNP.Outside.L_meta_17844 : ∀ (x1 x2 : Fin (10 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Fin (18 : ℕ)) (x6 : Fin (10 : ℕ) → Bool), { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate }] ++ x3.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(10 : ℕ) + ↑x4, (10 : ℕ) + ↑x5] : PEqualNP.CircuitLowerBounds.Gate }], output := (11 : ℕ) + x3.gates.length : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x6) = ((x3.wires ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate }], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x6))).getD ((10 : ℕ) + ↑x4) Bool.false || (x3.wires ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate }], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x6))).getD ((10 : ℕ) + ↑x5) Bool.false) := by
  intro x1 x2 x3 x4 x5 x6
  rw [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.Outside.L_meta_17844_aux.split]
  exact PEqualNP.Outside.L_meta_17844_aux.key x3 _
    (by simp [PEqualNP.CircuitLowerBounds.Circuit.wires]) _ _
