import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17832_aux

open PEqualNP.CircuitLowerBounds

theorem getD_app (w : List Bool) (a : Bool) (m : ℕ) :
    (w ++ [a]).getD m false = if m < w.length then w.getD m false else if m = w.length then a else false := by
  simp only [List.getD_eq_getElem?_getD]
  rcases lt_trichotomy m w.length with h | h | h
  · simp [h, List.getElem?_append_left h]
  · subst h; simp
  · rw [if_neg (by omega), if_neg (by omega), List.getElem?_eq_none (by simp; omega)]
    rfl

theorem fold_inv (r : ℕ → ℕ) (n : ℕ) (hr1 : ∀ m, n ≤ m → r m = m) (hr2 : ∀ m, m < n → r m < n)
    (gs : List Gate) : ∀ (wD wC : List Bool), wD.length = wC.length → n ≤ wC.length →
    (∀ m, wD.getD (r m) false = wC.getD m false) →
    (∀ m, ((gs.map (fun g => (⟨g.op, g.inputs.map r⟩ : Gate))).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wD).getD (r m) false =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wC).getD m false) := by
  induction gs with
  | nil => intro wD wC _ _ h; simpa using h
  | cons g gs ih =>
    intro wD wC hl hn h
    simp only [List.map_cons, List.foldl_cons]
    have he : (g.inputs.map r).map (fun i => wD.getD i false) = g.inputs.map (fun i => wC.getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => h i)
    apply ih
    · simp [hl]
    · simp; omega
    · intro m
      rw [he, getD_app, getD_app]
      by_cases hm : m < n
      · have := hr2 m hm
        rw [if_pos (by omega), if_pos (by omega)]
        exact h m
      · rw [hr1 m (by omega)]
        have := h m
        rw [hr1 m (by omega)] at this
        rw [hl]
        split_ifs <;> simp_all

end PEqualNP.Outside.L_meta_17832_aux

open PEqualNP.Outside.L_meta_17832_aux in
theorem PEqualNP.Outside.L_meta_17832 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x3.size ∧ ∀ (x6 : Fin x1 → Bool) (x7 : Bool) (x8 : ℕ), (x5.wires (List.ofFn x6 ++ [x7])).getD (x1 + x8) Bool.false = (x3.wires (List.ofFn (x6 ∘ x2) ++ [x7])).getD (x1 + x8) Bool.false := by
  intro n σ C hC
  let r : ℕ → ℕ := fun i => if h : i < n then (σ ⟨i, h⟩ : ℕ) else i
  have hr1 : ∀ m, n ≤ m → r m = m := fun m hm => by simp [r, dif_neg (show ¬ m < n by omega)]
  have hr2 : ∀ m, m < n → r m < n := fun m hm => by simp [r, dif_pos hm]
  refine ⟨⟨C.gates.map (fun g => (⟨g.op, g.inputs.map r⟩ : PEqualNP.CircuitLowerBounds.Gate)), C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := hC g0 hg0
    simpa using this
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x b k
    have key := fold_inv r n hr1 hr2 C.gates (List.ofFn x ++ [b]) (List.ofFn (x ∘ σ) ++ [b]) (by simp) (by simp) (by
      intro m
      rw [getD_app, getD_app]
      by_cases hm : m < n
      · have h2 := hr2 m hm
        simp only [List.length_ofFn, if_pos h2, if_pos hm, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp [r, hm, List.ofFnNthVal, Function.comp]
      · rw [hr1 m (by omega)]
        simp only [List.length_ofFn, if_neg hm])
    have := key (n + k)
    rw [hr1 _ (by omega)] at this
    exact this
