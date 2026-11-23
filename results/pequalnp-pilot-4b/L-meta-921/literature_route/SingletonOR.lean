import Mathlib

namespace SingletonOR

variable {α : Type*} [DecidableEq α]

/-- A certificate of size at most four cannot obtain a necessary variable
from a disjunction of two distinct variables, when all inputs of size at most
five must satisfy a fixed conjunction. -/
theorem context_contains_target (S C : Finset α) (a b : α)
    (hab : a ≠ b) (hC : C.card ≤ 4)
    (hcorrect : ∀ T : Finset α, T.card ≤ 5 → C ⊆ T →
      (a ∈ T ∨ b ∈ T) → S ⊆ T) : S ⊆ C := by
  have ha : S ⊆ insert a C := hcorrect (insert a C)
    ((Finset.card_insert_le a C).trans (by omega))
    (Finset.subset_insert _ _) (Or.inl (Finset.mem_insert_self _ _))
  have hb : S ⊆ insert b C := hcorrect (insert b C)
    ((Finset.card_insert_le b C).trans (by omega))
    (Finset.subset_insert _ _) (Or.inr (Finset.mem_insert_self _ _))
  intro p hp
  by_contra hpc
  have hpa : p = a := (Finset.mem_insert.mp (ha hp)).resolve_right hpc
  have hpb : p = b := (Finset.mem_insert.mp (hb hp)).resolve_right hpc
  exact hab (hpa.symm.trans hpb)

end SingletonOR
