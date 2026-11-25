import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def capGate (bound : Nat) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun i => min i bound)⟩

def capCircuit (bound : Nat) (C : Circuit) : Circuit :=
  ⟨C.gates.map (capGate bound), min C.output bound⟩

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

lemma getD_cap (w : List Bool) (bound i : Nat) (h : w.length ≤ bound) :
    w.getD (min i bound) false = w.getD i false := by
  by_cases hi : i ≤ bound
  · rw [Nat.min_eq_left hi]
  · rw [Nat.min_eq_right (by omega : bound ≤ i)]
    rw [List.getD_eq_default _ _ h,
      List.getD_eq_default _ _ (by omega : w.length ≤ i)]

lemma gateStep_cap (w : List Bool) (bound : Nat) (g : Gate)
    (h : w.length ≤ bound) : gateStep w (capGate bound g) = gateStep w g := by
  change w ++ [g.op.eval ((g.inputs.map (fun i => min i bound)).map
    (fun i => w.getD i false))] = w ++ [g.op.eval (g.inputs.map
    (fun i => w.getD i false))]
  rw [List.map_map]
  have hm : g.inputs.map ((fun i => w.getD i false) ∘ (fun i => min i bound)) =
      g.inputs.map (fun i => w.getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact getD_cap w bound i h
  rw [hm]

lemma fold_cap (gs : List Gate) (w : List Bool) (bound : Nat)
    (h : w.length + gs.length ≤ bound) :
    (gs.map (capGate bound)).foldl gateStep w = gs.foldl gateStep w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, List.foldl_cons, List.foldl_cons,
      gateStep_cap w bound g (by simp only [List.length_cons] at h; omega)]
    apply ih
    simp only [gateStep, List.length_append, List.length_singleton]
    simp only [List.length_cons] at h
    omega

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl gateStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [gateStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma capCircuit_eval (C : Circuit) (w : List Bool) (bound : Nat)
    (h : w.length + C.size ≤ bound) : (capCircuit bound C).eval w = C.eval w := by
  change ((C.gates.map (capGate bound)).foldl gateStep w).getD
    (min C.output bound) false = (C.gates.foldl gateStep w).getD C.output false
  rw [fold_cap C.gates w bound h]
  exact getD_cap _ bound C.output (by rw [fold_length]; exact h)

lemma capCircuit_size (C : Circuit) (bound : Nat) :
    (capCircuit bound C).size = C.size := by
  simp only [capCircuit, Circuit.size, List.length_map]

lemma capCircuit_fan (C : Circuit) (bound : Nat) (h : FanInTwo C) :
    FanInTwo (capCircuit bound C) := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  have hx := h a ha
  exact ⟨hx.1, by simpa only [capGate, List.length_map] using hx.2⟩

lemma capCircuit_inputs (C : Circuit) (bound : Nat) :
    ∀ g ∈ (capCircuit bound C).gates, ∀ i ∈ g.inputs, i ≤ bound := by
  intro g hg i hi
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  exact Nat.min_le_right j bound

lemma bounded_sources (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 18) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ D.output ≤ 29 ∧
      (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 29) ∧
      ∀ w : List Bool, w.length = 11 → D.eval w = C.eval w := by
  refine ⟨capCircuit 29 C, capCircuit_fan C 29 hfan, capCircuit_size C 29,
    Nat.min_le_right _ _, capCircuit_inputs C 29, ?_⟩
  intro w hw
  exact capCircuit_eval C w 29 (by rw [hw]; omega)

end PEqualNP.Outside.L_meta_1884
