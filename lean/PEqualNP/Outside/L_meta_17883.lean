import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17883_aux

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

theorem foldl_len (n : ℕ) (l : List Gate) (acc : List (List ℕ)) :
    (l.foldl (coneStep n) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons g l ih => rw [List.foldl_cons, ih]; simp [coneStep]; omega

theorem cones_len (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones; rw [foldl_len]; simp

theorem cones_app (n : ℕ) (C : Circuit) (g : Gate) :
    cones n { gates := C.gates ++ [g], output := C.output } = coneStep n (cones n C) g := by
  unfold cones; simp [List.foldl_append]

end PEqualNP.Outside.L_meta_17883_aux

open PEqualNP.Outside.L_meta_17883_aux in
theorem PEqualNP.Outside.L_meta_17883 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) (x5 : List (ℕ × ℕ)),   have x6 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x3] : PEqualNP.CircuitLowerBounds.Gate }], output := x2.output : PEqualNP.CircuitLowerBounds.Circuit };   have x7 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → List (ℕ × ℕ) → Prop := fun (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : List (ℕ × ℕ)) => ∀ x10 < x8.size, PEqualNP.ReadTwo.isAnd x8 x10 → ∃ x13 ∈ x9, ∃ x14 ∈ [x13.1, x13.2], x14 = x7 + x10 ∨ x7 ≤ x14 ∧ PEqualNP.EdgeOwnership.InCone x7 x8 x10 (x14 - x7);   PEqualNP.TopForm.IsAO2 x1 x2 → x3 < x1 + x2.size → x7 x1 x2 ((x3, x4) :: x5) → x7 x1 x6 ((x1 + x2.size, x4) :: x5) := by
  intro n C x3 x4 L
  intro C' P _ hx3 hP
  simp only [P, C'] at hP ⊢
  have hlen := cones_len n C
  have hcone : ∀ j i, j < C.size →
      PEqualNP.EdgeOwnership.InCone n C i j →
      PEqualNP.EdgeOwnership.InCone n { gates := C.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x3] }], output := C.output } i j := by
    intro j i hj h
    unfold PEqualNP.EdgeOwnership.InCone at *
    rw [cones_app]
    unfold PEqualNP.EdgeOwnership.coneStep
    have : j < (PEqualNP.EdgeOwnership.cones n C).length := by
      rw [hlen]; exact hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left this]
    rw [List.getD_eq_getElem?_getD] at h
    exact h
  have hnew : ∀ i, (x3 = n + i ∨ n ≤ x3 ∧ PEqualNP.EdgeOwnership.InCone n C i (x3 - n)) →
      PEqualNP.EdgeOwnership.InCone n { gates := C.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x3] }], output := C.output } i C.size := by
    intro i hi
    unfold PEqualNP.EdgeOwnership.InCone at *
    rw [cones_app]
    unfold PEqualNP.EdgeOwnership.coneStep
    have hs : C.size = (PEqualNP.EdgeOwnership.cones n C).length := by
      rw [hlen]; rfl
    have hge : n ≤ x3 := by rcases hi with h | h <;> omega
    have hlt : x3 < n + (PEqualNP.EdgeOwnership.cones n C).length := by rw [← hs]; exact hx3
    rw [List.getD_eq_getElem?_getD, hs, List.getElem?_concat_length]
    simp only [Option.getD_some]
    rw [List.mem_flatMap]
    refine ⟨x3, ?_, ?_⟩
    · simp [hge, hlt]
    · rcases hi with h | h
      · simp; omega
      · exact List.mem_cons_of_mem _ h.2
  intro i hi hand
  have hsz : (({ gates := C.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x3] }], output := C.output } : PEqualNP.CircuitLowerBounds.Circuit)).size = C.size + 1 := by
    simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  rw [hsz] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
  · have hand' : PEqualNP.ReadTwo.isAnd C i := by
      unfold PEqualNP.ReadTwo.isAnd at *
      refine ⟨hi, ?_⟩
      have := hand.2
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt at *
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi] at this
      rw [List.getD_eq_getElem?_getD]
      exact this
    obtain ⟨p, hp, w, hw, hw2⟩ := hP i hi hand'
    rcases List.mem_cons.mp hp with hp | hp
    · subst hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with hw | hw
      · subst w
        refine ⟨(n + C.size, x4), List.mem_cons_self .., n + C.size, by simp, Or.inr ⟨by omega, ?_⟩⟩
        simp only [Nat.add_sub_cancel_left]
        exact hnew i hw2
      · subst w
        refine ⟨(n + C.size, x4), List.mem_cons_self .., x4, by simp, ?_⟩
        rcases hw2 with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, hcone _ _ (by
            have := h.2
            unfold PEqualNP.EdgeOwnership.InCone at this
            by_contra hc
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen]; simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hc; omega)] at this
            simp at this) h.2⟩
    · refine ⟨p, List.mem_cons_of_mem _ hp, w, hw, ?_⟩
      rcases hw2 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.1, hcone _ _ (by
            have := h.2
            unfold PEqualNP.EdgeOwnership.InCone at this
            by_contra hc
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen]; simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hc; omega)] at this
            simp at this) h.2⟩
  · subst hi
    exact ⟨(n + C.size, x4), List.mem_cons_self .., n + C.size, by simp, Or.inl rfl⟩
