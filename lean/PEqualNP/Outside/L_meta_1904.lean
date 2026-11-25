import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1904_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma exists_minimizer {α : Type*} (P : α → Prop) (measure : α → ℕ)
    (hex : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → measure a ≤ measure b := by
  classical
  have h : ∃ k, ∃ a, P a ∧ measure a = k := by
    obtain ⟨a, ha⟩ := hex
    exact ⟨measure a, a, ha, rfl⟩
  obtain ⟨a, ha, hm⟩ := Nat.find_spec h
  refine ⟨a, ha, ?_⟩
  intro b hb
  rw [hm]
  exact Nat.find_min' h ⟨b, hb, rfl⟩

def Correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Prop :=
  Monotone2 C ∧ ∀ x : Fin n → Bool,
    C.eval (List.ofFn x) = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)

noncomputable def dirtySet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter (PEqualNP.CleanedNonEdge.IsDirtyAnd n G C)

lemma exists_extremal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hex : ∃ C, Correct G C) :
    ∃ C, Correct G C ∧
      (∀ D, Correct G D → C.size ≤ D.size) ∧
      ∀ D, Correct G D → D.size ≤ C.size →
        (dirtySet G C).card ≤ (dirtySet G D).card := by
  classical
  obtain ⟨C, hC, hmin⟩ := exists_minimizer (Correct G) Circuit.size hex
  obtain ⟨D, ⟨hD, hsize⟩, hdirty⟩ := exists_minimizer
    (fun D => Correct G D ∧ D.size ≤ C.size)
    (fun D => (dirtySet G D).card) ⟨C, hC, le_rfl⟩
  refine ⟨D, hD, fun E hE => hsize.trans (hmin E hE), ?_⟩
  intro E hE hED
  exact hdirty E ⟨hE, hED.trans hsize⟩

lemma dirty_card_decreases {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (j : ℕ) (hsub : dirtySet G D ⊆ dirtySet G C)
    (hC : j ∈ dirtySet G C) (hD : j ∉ dirtySet G D) :
    (dirtySet G D).card < (dirtySet G C).card := by
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hsub, fun h => hD (h.symm ▸ hC)⟩)

lemma extremal_no_repair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit)
    (hmin : ∀ D, Correct G D → D.size ≤ C.size →
      (dirtySet G C).card ≤ (dirtySet G D).card)
    (D : Circuit) (hD : Correct G D) (hsize : D.size ≤ C.size)
    (hsub : dirtySet G D ⊆ dirtySet G C) (j : ℕ)
    (hCj : j ∈ dirtySet G C) : j ∈ dirtySet G D := by
  by_contra hDj
  exact Nat.not_lt_of_ge (hmin D hD hsize)
    (dirty_card_decreases G C D j hsub hCj hDj)

end PEqualNP.Outside.L_meta_1904_aux
