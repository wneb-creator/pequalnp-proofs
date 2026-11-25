import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.RailComparison

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

def comparable (w z : List Bool) : Prop :=
  w.length = z.length ∧ 11 ≤ w.length ∧
    ∀ i, i ≠ 0 → i ≠ 10 → w.getD i false ≤ z.getD i false

lemma eval_mono (g : Gate) (hg : g.op = .and ∨ g.op = .or)
    (w z : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false ≤ z.getD i false) :
    g.op.eval (g.inputs.map (fun i => w.getD i false)) ≤
      g.op.eval (g.inputs.map (fun i => z.getD i false)) := by
  apply Bool.le_iff_imp.mpr
  intro hw
  rcases hg with hg | hg
  · rw [hg] at hw ⊢
    change (g.inputs.map (fun i => z.getD i false)).all id = true
    apply List.all_eq_true.mpr
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    apply Bool.le_iff_imp.mp (h i hi)
    exact List.all_eq_true.mp hw _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · rw [hg] at hw ⊢
    obtain ⟨b, hb, ht⟩ := List.any_eq_true.mp hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    apply List.any_eq_true.mpr
    exact ⟨z.getD i false, List.mem_map.mpr ⟨i, hi, rfl⟩,
      Bool.le_iff_imp.mp (h i hi) ht⟩

lemma step_comparable (g : Gate) {w z : List Bool} (h : comparable w z)
    (hg : g.op.eval (g.inputs.map (fun i => w.getD i false)) ≤
      g.op.eval (g.inputs.map (fun i => z.getD i false))) :
    comparable (step w g) (step z g) := by
  have hw : 11 ≤ w.length := h.2.1
  refine ⟨by simp [step, h.1], by simp [step]; omega, ?_⟩
  intro i hi0 hi10
  by_cases hi : i < w.length
  · simp only [step]
    rw [List.getD_append _ _ _ _ hi,
      List.getD_append _ _ _ _ (h.1 ▸ hi)]
    exact h.2.2 i hi0 hi10
  · by_cases he : i = w.length
    · subst i
      simpa [step, List.getD_eq_getElem?_getD, h.1] using hg
    · rw [List.getD_eq_default _ _ (by simp [step]; omega),
        List.getD_eq_default _ _ (by simp [step, ← h.1]; omega)]

lemma run_comparable (gs : List Gate) (w z : List Bool)
    (h : comparable w z)
    (allowed : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (special : ∀ (pre post : List Gate) (g : Gate), gs = pre ++ g :: post →
      (0 ∈ g.inputs ∨ 10 ∈ g.inputs) →
      g.op.eval (g.inputs.map (fun i => (run pre w).getD i false)) ≤
        g.op.eval (g.inputs.map (fun i => (run pre z).getD i false))) :
    comparable (run gs w) (run gs z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    have hg : g.op.eval (g.inputs.map (fun i => w.getD i false)) ≤
        g.op.eval (g.inputs.map (fun i => z.getD i false)) := by
      by_cases hr : 0 ∈ g.inputs ∨ 10 ∈ g.inputs
      · exact special [] gs g rfl hr
      · apply eval_mono g (allowed g (by simp)) w z
        intro i hi
        exact h.2.2 i (fun he => hr (Or.inl (he ▸ hi)))
          (fun he => hr (Or.inr (he ▸ hi)))
    change comparable (run gs (step w g)) (run gs (step z g))
    apply ih (step w g) (step z g) (step_comparable g h hg)
      (fun g' hg' => allowed g' (by simp [hg']))
    intro pre post g' he hr
    have hh : g :: gs = (g :: pre) ++ g' :: post := by simp [he]
    simpa [run, List.foldl_cons] using special (g :: pre) post g' hh hr

lemma circuit_comparison (C : Circuit) (w z : List Bool)
    (h : comparable w z)
    (allowed : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    (special : ∀ (pre post : List Gate) (g : Gate),
      C.gates = pre ++ g :: post → (0 ∈ g.inputs ∨ 10 ∈ g.inputs) →
      g.op.eval (g.inputs.map (fun i => (run pre w).getD i false)) ≤
        g.op.eval (g.inputs.map (fun i => (run pre z).getD i false)))
    (out0 : C.output ≠ 0) (out10 : C.output ≠ 10) :
    C.eval w ≤ C.eval z := by
  exact (run_comparable C.gates w z h allowed special).2.2 C.output out0 out10

lemma run_input (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = w.getD i false
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma and_false (g : Gate) (w : List Bool) (hg : g.op = .and)
    (hi : 10 ∈ g.inputs) (hw : w.getD 10 false = false) :
    g.op.eval (g.inputs.map (fun i => w.getD i false)) = false := by
  generalize hv : g.op.eval (g.inputs.map (fun i => w.getD i false)) = v
  cases v with
  | false => rfl
  | true =>
    rw [hg] at hv
    have hh := List.all_eq_true.mp hv (w.getD 10 false)
      (List.mem_map.mpr ⟨10, hi, rfl⟩)
    rw [hw] at hh
    cases hh

lemma reader_comparison (C : Circuit) (w z : List Bool)
    (h : comparable w z) (hw : w.getD 10 false = false)
    (allowed : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    (negative_reader : ∀ g ∈ C.gates, 10 ∈ g.inputs → g.op = .and)
    (positive_reader : ∀ (pre post : List Gate) (g : Gate),
      C.gates = pre ++ g :: post → 0 ∈ g.inputs →
      g.op.eval (g.inputs.map (fun i => (run pre z).getD i false)) = true)
    (out0 : C.output ≠ 0) (out10 : C.output ≠ 10) :
    C.eval w ≤ C.eval z := by
  apply circuit_comparison C w z h allowed _ out0 out10
  intro pre post g he hr
  by_cases hp : 0 ∈ g.inputs
  · rw [positive_reader pre post g he hp]
    exact Bool.le_true _
  · have hn : 10 ∈ g.inputs := hr.resolve_left hp
    have hmem : g ∈ C.gates := by rw [he]; simp
    have hwlen : 11 ≤ w.length := h.2.1
    have hneg : (run pre w).getD 10 false = false :=
      (run_input pre w 10 (by omega)).trans hw
    rw [and_false g (run pre w) (negative_reader g hmem hn) hn hneg]
    exact Bool.false_le _

end PEqualNP.Outside.L_meta_1884.RailComparison
