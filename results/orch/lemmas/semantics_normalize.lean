import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def capGate (bound : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun i => min i bound)⟩

def capCircuit (n : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (capGate (n + C.size)), min C.output (n + C.size)⟩

lemma getD_cap (w : List Bool) (bound i : ℕ) (h : w.length ≤ bound) :
    w.getD (min i bound) false = w.getD i false := by
  by_cases hi : i ≤ bound
  · rw [Nat.min_eq_left hi]
  · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ h,
      List.getD_eq_default _ _ (by omega)]

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp
      omega

lemma fold_cap (gs : List Gate) (w : List Bool) (bound : ℕ)
    (h : w.length + gs.length ≤ bound) :
    ((gs.map (capGate bound)).foldl
      (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w) =
    (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons, capGate, List.map_map, Function.comp_def]
      have he : g.inputs.map (fun i => w.getD (min i bound) false) =
          g.inputs.map (fun i => w.getD i false) := by
        apply List.map_congr_left
        intro i hi
        exact getD_cap w bound i (by simp at h; omega)
      rw [he]
      apply ih
      simp at h ⊢
      omega

lemma capCircuit_size (n : ℕ) (C : Circuit) :
    (capCircuit n C).size = C.size := by
  simp [capCircuit, Circuit.size]

lemma capCircuit_wires (n : ℕ) (C : Circuit) (w : List Bool) (h : w.length = n) :
    (capCircuit n C).wires w = C.wires w := by
  apply fold_cap
  simp [Circuit.size, h]

lemma capCircuit_eval (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (capCircuit n C).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  unfold Circuit.eval
  rw [capCircuit_wires n C _ (by simp)]
  apply getD_cap
  unfold Circuit.wires
  rw [fold_length]
  simp [Circuit.size]

lemma capCircuit_fanInTwo (n : ℕ) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (capCircuit n C) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  simpa [capGate] using h g' hg'

lemma capCircuit_not (n : ℕ) (C : Circuit) :
    (∃ g ∈ (capCircuit n C).gates, g.op = GateOp.not) ↔
      ∃ g ∈ C.gates, g.op = GateOp.not := by
  constructor
  · rintro ⟨g, hg, hn⟩
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact ⟨g', hg', hn⟩
  · rintro ⟨g, hg, hn⟩
    exact ⟨capGate (n + C.size) g, List.mem_map.mpr ⟨g, hg, rfl⟩, hn⟩

lemma capCircuit_inputs (n : ℕ) (C : Circuit) :
    ∀ g ∈ (capCircuit n C).gates, ∀ i ∈ g.inputs, i ≤ n + C.size := by
  intro g hg i hi
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
  exact Nat.min_le_right _ _

lemma capCircuit_output (n : ℕ) (C : Circuit) :
    (capCircuit n C).output ≤ n + C.size := Nat.min_le_right _ _

lemma finite_normalization (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hnot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
      (∃ g ∈ D.gates, g.op = GateOp.not) ∧
      (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ n + C.size) ∧
      D.output ≤ n + C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  exact ⟨capCircuit n C, capCircuit_fanInTwo n C hfan, capCircuit_size n C,
    (capCircuit_not n C).2 hnot, capCircuit_inputs n C, capCircuit_output n C,
    capCircuit_eval n C⟩

end PEqualNP.Outside.L_meta_2592_aux
