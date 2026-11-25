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

lemma fold_getD_input (gs : List Gate) (w : List Bool) (i : Nat)
    (hi : i < w.length) : (gs.foldl gateStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (gateStep w g) (by simp only [gateStep,
      List.length_append, List.length_singleton]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma eval_input (C : Circuit) (w : List Bool) (hi : C.output < w.length) :
    C.eval w = w.getD C.output false := by
  exact fold_getD_input C.gates w C.output hi

lemma output_internal (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (f : (Fin 10 → Bool) → Bool)
    (separates : ∀ q : Fin 10, ∃ x y : Fin 10 → Bool,
      x q = y q ∧ x 0 = y 0 ∧ f x ≠ f y)
    (computes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = f x) :
    11 ≤ C.output ∧ C.output < 11 + C.size := by
  constructor
  · by_contra low
    have lower : C.output < 11 := by omega
    by_cases ten : C.output < 10
    · obtain ⟨x, y, same, _, different⟩ := separates (σ ⟨C.output, ten⟩)
      apply different
      rw [← computes x, ← computes y,
        eval_input C _ (by simpa using lower),
        eval_input C _ (by simpa using lower)]
      rw [List.getD_append _ _ _ _ (by simpa using ten),
        List.getD_append _ _ _ _ (by simpa using ten),
        List.getD_eq_getElem _ _ (by simpa using ten),
        List.getD_eq_getElem _ _ (by simpa using ten)]
      simpa only [List.getElem_ofFn, Function.comp_apply] using same
    · have eqten : C.output = 10 := by omega
      obtain ⟨x, y, _, same, different⟩ := separates 0
      apply different
      rw [← computes x, ← computes y,
        eval_input C _ (by simpa using lower),
        eval_input C _ (by simpa using lower), eqten]
      exact congrArg u same
  · by_contra high
    have high' : 11 + C.size ≤ C.output := by omega
    have always_false (x : Fin 10 → Bool) : f x = false := by
      rw [← computes x]
      change (C.gates.foldl gateStep _).getD C.output false = false
      apply List.getD_eq_default
      rw [fold_length]
      simpa only [List.length_append, List.length_ofFn, List.length_singleton,
        Circuit.size] using high'
    obtain ⟨x, y, _, _, different⟩ := separates 0
    exact different ((always_false x).trans (always_false y).symm)

end PEqualNP.Outside.L_meta_1884
