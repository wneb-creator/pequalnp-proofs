import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18189_aux

open PEqualNP.CircuitLowerBounds

theorem getD_tb (W : List ℕ) (i k : ℕ) :
    (W.map (fun x => x.testBit k)).getD i false = (W.getD i 0).testBit k := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> simp

theorem inv (k : ℕ) (gs : List Gate)
    (h : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b])
    (W : List ℕ) :
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (W.map (fun x => x.testBit k))
      = (gs.foldl (fun W g => let u := W.getD (g.inputs.getD 0 0) 0; let v := W.getD (g.inputs.getD 1 0) 0;
          W ++ [bif g.op.eval [false, true] then u ||| v else u &&& v]) W).map (fun x => x.testBit k) := by
  induction gs generalizing W with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [← ih (fun g' hg' => h g' (by simp [hg']))]
    congr 1
    obtain ⟨hop, a, b, hab⟩ := h g (by simp)
    rw [List.map_append, hab]
    simp only [List.map_cons, List.map_nil, getD_tb, List.getD_cons_zero, List.getD_cons_succ]
    rcases hop with hop | hop <;> simp [hop, GateOp.eval, Nat.testBit_land, Nat.testBit_lor]

end PEqualNP.Outside.L_meta_18189_aux

theorem PEqualNP.Outside.L_meta_18189 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x2 ∈ x1.gates, (x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x4 : ℕ) (x5 : ℕ), x2.inputs = [x4, x5]) →     ∀ (x3 : List ℕ) (x4 : ℕ),       x1.eval (List.map (fun (x5 : ℕ) => x5.testBit x4) x3) =         ((List.foldl                   (fun (x5 : List ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) =>                     have x7 : ℕ := x5.getD (x6.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);                     have x8 : ℕ := x5.getD (x6.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);                     x5 ++ [bif x6.op.eval [Bool.false, Bool.true] then x7 ||| x8 else x7 &&& x8])                   x3 x1.gates).getD               x1.output (0 : ℕ)).testBit           x4 := by
  intro C h L k
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
  rw [PEqualNP.Outside.L_meta_18189_aux.inv k C.gates h L, PEqualNP.Outside.L_meta_18189_aux.getD_tb]
