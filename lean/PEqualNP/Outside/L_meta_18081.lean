import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18081_aux

open PEqualNP.CircuitLowerBounds

def R (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

theorem step (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (a b : List Bool)
    (h : R a b) :
    R (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)])
      (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]) := by
  obtain ⟨hl, hv⟩ := h
  have hev : g.op.eval (g.inputs.map fun i => a.getD i false) = true →
      g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
    rcases hg with hg | hg <;> rw [hg] <;> simp [GateOp.eval]
    · intro H j hj; exact hv _ (H j hj)
    · intro j hj H; exact ⟨j, hj, hv _ H⟩
  refine ⟨by simp [hl], fun i hi => ?_⟩
  rcases lt_trichotomy i a.length with h1 | h1 | h1
  · rw [List.getD_append _ _ _ _ h1] at hi
    rw [List.getD_append _ _ _ _ (hl ▸ h1)]
    exact hv _ hi
  · subst h1
    rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
    rw [hl, List.getD_append_right _ _ _ _ (le_refl _)]
    simp at hi ⊢
    exact hev hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    simp at hi

theorem fold (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, R a b →
      R (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b) := by
  induction gs with
  | nil => intro a b h; exact h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hg g' (by simp [hg'])) _ _ (step g (hg g (by simp)) a b h)

theorem mono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (L : List (Fin 26))
    (f g : Fin 26 → Bool) (hfg : ∀ a, f a = true → g a = true)
    (h : C.eval (L.map f) = true) : C.eval (L.map g) = true := by
  have hg : ∀ x ∈ C.gates, x.op = GateOp.and ∨ x.op = GateOp.or := by
    intro x hx
    have := (hC x hx).1
    simpa using this
  have hR : R (L.map f) (L.map g) := by
    refine ⟨by simp, fun i hi => ?_⟩
    rw [List.getD_eq_getElem?_getD] at hi ⊢
    rw [List.getElem?_map] at hi ⊢
    cases hL : L[i]? with
    | none => simp [hL] at hi
    | some a => simp [hL] at hi ⊢; exact hfg a hi
  exact (fold C.gates hg _ _ hR).2 C.output h

end PEqualNP.Outside.L_meta_18081_aux

open PEqualNP.Outside.L_meta_18081_aux in
theorem PEqualNP.Outside.L_meta_18081 : ∀ (x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool) (x2 : List (Fin (26 : ℕ))) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x3 →     have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x5 x6 : Finset (Fin (13 : ℕ))) => List.map (fun (x7 : Fin (26 : ℕ)) => if ↑x7 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x7 ∈ x5) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x7 ∈ x6)) x2;     (∀ (x6 x7 : Fin (13 : ℕ)), x1 x6 x7 = Bool.true → x3.eval (x5 {x6} {x7}) = Bool.true) → (∀ (x7 : Finset (Fin (13 : ℕ))), x3.eval (x5 x7 {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, x1 x9 x8 = Bool.false}) = Bool.false) → ∀ (x8 x9 : Finset (Fin (13 : ℕ))), x3.eval (x5 x8 x9) = Bool.true ↔ ∃ x10 ∈ x8, ∃ x11 ∈ x9, x1 x10 x11 = Bool.true := by
  intro r L C hC
  simp only []
  intro h1 h2 S T
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    have := h2 S
    rw [mono C hC L _ _ ?_ h] at this
    · exact absurd this (by simp)
    · intro a ha
      split_ifs at ha ⊢ with hc
      · exact ha
      · simp only [decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        intro p hp
        have := hn p hp _ ha
        simpa using this
  · rintro ⟨p, hp, l, hl, hr⟩
    refine mono C hC L _ _ ?_ (h1 p l hr)
    intro a ha
    split_ifs at ha ⊢ with hc
    · simp only [decide_eq_true_eq, Finset.mem_singleton] at ha ⊢
      rw [ha]; exact hp
    · simp only [decide_eq_true_eq, Finset.mem_singleton] at ha ⊢
      rw [ha]; exact hl
