import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.BankFactorObstruction

abbrev Signal := (Fin 4 → Bool) → Bool

def source (i : Fin 6) (x : Fin 4 → Bool) : Bool :=
  if i = 0 then x 0 else if i = 1 then x 1 else if i = 2 then x 2 else
    if i = 3 then x 3 else if i = 4 then x 0 || x 1 else x 0 || x 2

def target (i : Fin 2) (x : Fin 4 → Bool) : Bool :=
  if i = 0 then (x 0 || x 1) || x 3 else (x 0 || x 2) || x 3

lemma targets_distinct : target 0 ≠ target 1 := by decide

lemma targets_new : ∀ i : Fin 2, ∀ j : Fin 6, target i ≠ source j := by decide

lemma two_new_signals (S : Finset Signal)
    (h : ∀ i : Fin 2, target i ∈ S ∨ ∃ j : Fin 6, target i = source j) :
    2 ≤ S.card := by
  classical
  have h0 : target 0 ∈ S := (h 0).resolve_right (by rintro ⟨j, hj⟩; exact targets_new 0 j hj)
  have h1 : target 1 ∈ S := (h 1).resolve_right (by rintro ⟨j, hj⟩; exact targets_new 1 j hj)
  have hsub : ({target 0, target 1} : Finset Signal) ⊆ S := by
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact h0
    · exact h1
  have hc := Finset.card_le_card hsub
  simpa [targets_distinct] using hc

-- Three original OR gates, four raw incidences across two centres, two outputs.
-- No network of at most one new signal can meet the proposed incidence budget.
lemma centrewise_factoring_budget_impossible (S : Finset Signal)
    (h : ∀ i : Fin 2, target i ∈ S ∨ ∃ j : Fin 6, target i = source j) :
    ¬ (S.card + 4 ≤ 3 + 2) := by
  have hc := two_new_signals S h
  omega

end PEqualNP.Outside.L_meta_4675.BankFactorObstruction
