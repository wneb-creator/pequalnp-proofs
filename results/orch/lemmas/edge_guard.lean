import independent_guard

namespace PEqualNP.Outside.L_meta_1886_aux.EdgeGuard

open MapRigidity IndependentGuard

def edgeMasks : List (Fin 1024) :=
  [3,6,12,24,17,33,66,132,264,528,160,640,576,320,288]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma edge_masks_true : ∀ m ∈ edgeMasks, edge10 (row m) = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma edge_restriction : ∀ x : Fin 10 → Bool, edge10 x = true →
    ∃ m ∈ edgeMasks, ∀ i : Fin 10, row m i ≤ x i := by
  intro x hx
  simp only [edge10, Bool.or_eq_true, Bool.and_eq_true, or_assoc] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · refine ⟨3,by decide +kernel,?_⟩
    intro i
    rw [Bool.le_iff_imp]
    intro hi
    have support : ∀ j : Fin 10, row (3 : Fin 1024) j = true → j = 0 ∨ j = 1 := by decide +kernel
    rcases support i hi with rfl | rfl
    · exact h.1
    · exact h.2
  · refine ⟨6,by decide +kernel,?_⟩
    intro i
    rw [Bool.le_iff_imp]
    intro hi
    have support : ∀ j : Fin 10, row (6 : Fin 1024) j = true → j = 1 ∨ j = 2 := by decide +kernel
    rcases support i hi with rfl | rfl
    · exact h.1
    · exact h.2
  · refine ⟨12,by decide +kernel,?_⟩
    intro i
    rw [Bool.le_iff_imp]
    intro hi
    have support : ∀ j : Fin 10, row (12 : Fin 1024) j = true → j = 2 ∨ j = 3 := by decide +kernel
    rcases support i hi with rfl | rfl
    · exact h.1
    · exact h.2
  · refine ⟨24,by decide +kernel,?_⟩
    intro i
    rw [Bool.le_iff_imp]
    intro hi
    have support : ∀ j : Fin 10, row (24 : Fin 1024) j = true → j = 3 ∨ j = 4 := by decide +kernel
    rcases support i hi with rfl | rfl
    · exact h.1
    · exact h.2
  · refine ⟨17,by decide +kernel,?_⟩
    intro i
    rw [Bool.le_iff_imp]
    intro hi
    have support : ∀ j : Fin 10, row (17 : Fin 1024) j = true → j = 4 ∨ j = 0 := by decide +kernel
    rcases support i hi with rfl | rfl
    · exact h.1
    · exact h.2
  · refine ⟨33,by decide +kernel,?_⟩
    intro i
    rw [Bool.le_iff_imp]
    intro hi
    have support : ∀ j : Fin 10, row (33 : Fin 1024) j = true → j = 0 ∨ j = 5 := by decide +kernel
    rcases support i hi with rfl | rfl
    · exact h.1
    · exact h.2
  · refine ⟨66,by decide +kernel,?_⟩
    intro i
    rw [Bool.le_iff_imp]
    intro hi
    have support : ∀ j : Fin 10, row (66 : Fin 1024) j = true → j = 1 ∨ j = 6 := by decide +kernel
    rcases support i hi with rfl | rfl
    · exact h.1
    · exact h.2
  · refine ⟨132,by decide +kernel,?_⟩
    intro i
    rw [Bool.le_iff_imp]
    intro hi
    have support : ∀ j : Fin 10, row (132 : Fin 1024) j = true → j = 2 ∨ j = 7 := by decide +kernel
    rcases support i hi with rfl | rfl
    · exact h.1
    · exact h.2
  · refine ⟨264,by decide +kernel,?_⟩
    intro i
    rw [Bool.le_iff_imp]
    intro hi
    have support : ∀ j : Fin 10, row (264 : Fin 1024) j = true → j = 3 ∨ j = 8 := by decide +kernel
    rcases support i hi with rfl | rfl
    · exact h.1
    · exact h.2
  · refine ⟨528,by decide +kernel,?_⟩
    intro i
    rw [Bool.le_iff_imp]
    intro hi
    have support : ∀ j : Fin 10, row (528 : Fin 1024) j = true → j = 4 ∨ j = 9 := by decide +kernel
    rcases support i hi with rfl | rfl
    · exact h.1
    · exact h.2
  · refine ⟨160,by decide +kernel,?_⟩
    intro i
    rw [Bool.le_iff_imp]
    intro hi
    have support : ∀ j : Fin 10, row (160 : Fin 1024) j = true → j = 5 ∨ j = 7 := by decide +kernel
    rcases support i hi with rfl | rfl
    · exact h.1
    · exact h.2
  · refine ⟨640,by decide +kernel,?_⟩
    intro i
    rw [Bool.le_iff_imp]
    intro hi
    have support : ∀ j : Fin 10, row (640 : Fin 1024) j = true → j = 7 ∨ j = 9 := by decide +kernel
    rcases support i hi with rfl | rfl
    · exact h.1
    · exact h.2
  · refine ⟨576,by decide +kernel,?_⟩
    intro i
    rw [Bool.le_iff_imp]
    intro hi
    have support : ∀ j : Fin 10, row (576 : Fin 1024) j = true → j = 9 ∨ j = 6 := by decide +kernel
    rcases support i hi with rfl | rfl
    · exact h.1
    · exact h.2
  · refine ⟨320,by decide +kernel,?_⟩
    intro i
    rw [Bool.le_iff_imp]
    intro hi
    have support : ∀ j : Fin 10, row (320 : Fin 1024) j = true → j = 6 ∨ j = 8 := by decide +kernel
    rcases support i hi with rfl | rfl
    · exact h.1
    · exact h.2
  · refine ⟨288,by decide +kernel,?_⟩
    intro i
    rw [Bool.le_iff_imp]
    intro hi
    have support : ∀ j : Fin 10, row (288 : Fin 1024) j = true → j = 8 ∨ j = 5 := by decide +kernel
    rcases support i hi with rfl | rfl
    · exact h.1
    · exact h.2

lemma edge_guard_witness (g : (Fin 10 → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i ≤ y i) → g x ≤ g y)
    (notDominating : ¬ ∀ x, edge10 x ≤ g x) :
    ∃ m ∈ edgeMasks, g (row m) = false ∧ edge10 (row m) = true := by
  obtain ⟨x,hx⟩ := not_forall.mp notDominating
  have gx : g x = false := by
    cases h : g x <;> simp_all [Bool.le_iff_imp]
  have fx : edge10 x = true := by
    cases h : edge10 x <;> simp_all [Bool.le_iff_imp]
  obtain ⟨m,hm,restriction⟩ := edge_restriction x fx
  have lower := mono (row m) x restriction
  have gm : g (row m) = false := by
    cases h : g (row m) <;> simp_all [Bool.le_iff_imp]
  exact ⟨m,hm,gm,edge_masks_true m hm⟩

lemma dominating_iff_edges_true (g : (Fin 10 → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i ≤ y i) → g x ≤ g y) :
    (∀ x, edge10 x ≤ g x) ↔ ∀ m ∈ edgeMasks, g (row m) = true := by
  constructor
  · intro dominating m hm
    have h := dominating (row m)
    rw [edge_masks_true m hm] at h
    cases hgm : g (row m) <;> simp_all [Bool.le_iff_imp]
  · intro noWitness
    by_contra hn
    obtain ⟨m,hm,no,_⟩ := edge_guard_witness g mono hn
    rw [noWitness m hm] at no
    cases no

end PEqualNP.Outside.L_meta_1886_aux.EdgeGuard
