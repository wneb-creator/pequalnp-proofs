import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_670.Seed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def seedCircuit {n : ℕ} (D : Circuit) (k : GateOp) (a b : Fin n) : Circuit :=
  ⟨⟨k, [a.val, b.val]⟩ :: D.gates, D.output⟩

lemma seed_fanin {n : ℕ} (D : Circuit) (k : GateOp) (a b : Fin n)
    (hk : k = .and ∨ k = .or ∨ k = .not) (hD : FanInTwo D) :
    FanInTwo (seedCircuit D k a b) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact ⟨hk, by simp⟩
  · exact hD g hg

lemma seed_size {n : ℕ} (D : Circuit) (k : GateOp) (a b : Fin n) :
    (seedCircuit D k a b).size = D.size + 1 := rfl

lemma seed_wires {n : ℕ} (D : Circuit) (k : GateOp) (a b : Fin n)
    (x : Fin n → Bool) :
    (seedCircuit D k a b).wires (List.ofFn x) =
      D.wires (List.ofFn x ++ [k.eval [x a, x b]]) := by
  simp [seedCircuit, Circuit.wires]

lemma seed_eval {n : ℕ} (D : Circuit) (k : GateOp) (a b : Fin n)
    (x : Fin n → Bool) :
    (seedCircuit D k a b).eval (List.ofFn x) =
      D.eval (List.ofFn x ++ [k.eval [x a, x b]]) := by
  unfold Circuit.eval
  rw [seed_wires]
  rfl

lemma fold_keeps_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) w).getD i false =
      w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma seed_first {n : ℕ} (D : Circuit) (k : GateOp) (a b : Fin n)
    (x : Fin n → Bool) :
    ((seedCircuit D k a b).wires (List.ofFn x)).getD n false = k.eval [x a, x b] := by
  rw [seed_wires]
  unfold Circuit.wires
  rw [fold_keeps_input _ _ _ (by simp)]
  simpa only [List.length_ofFn] using
    (show (List.ofFn x ++ [k.eval [x a, x b]]).getD (List.ofFn x).length false =
      k.eval [x a, x b] from by simp)

end PEqualNP.Outside.L_meta_670.Seed
