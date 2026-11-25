import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

def incidencePairInput {n m : ℕ} (p : Fin n) (l : Fin m) : Fin (n + m) → Bool :=
  fun j => decide (j = Fin.castAdd m p ∨ j = Fin.natAdd n l)

def incidenceBoundary {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (S : Finset (Fin n)) : Fin (n + m) → Bool :=
  Fin.addCases (fun p => decide (p ∈ S))
    (fun l => decide (∀ p ∈ S, ¬ I p l))

lemma incidence_boundary_complete {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (F : (Fin (n + m) → Bool) → Bool) (mono : Monotone F)
    (pairs : ∀ p l, I p l → F (incidencePairInput p l) = true)
    (boundary : ∀ S : Finset (Fin n), F (incidenceBoundary I S) = false) :
    ∀ x, F x = decide (∃ p l, I p l ∧ x (Fin.castAdd m p) = true ∧
      x (Fin.natAdd n l) = true) := by
  intro x
  by_cases hex : ∃ p l, I p l ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true
  · obtain ⟨p, l, hI, hp, hl⟩ := hex
    have below : incidencePairInput p l ≤ x := by
      intro j
      apply Bool.le_iff_imp.mpr
      intro hj
      have hit : j = Fin.castAdd m p ∨ j = Fin.natAdd n l := by
        simpa only [incidencePairInput, decide_eq_true_eq] using hj
      rcases hit with rfl | rfl
      · exact hp
      · exact hl
    have hx : F x = true := (Bool.le_iff_imp.mp (mono below)) (pairs p l hI)
    rw [hx]
    exact (decide_eq_true ⟨p, l, hI, hp, hl⟩).symm
  · let S : Finset (Fin n) := Finset.univ.filter (fun p => x (Fin.castAdd m p) = true)
    have below : x ≤ incidenceBoundary I S := by
      intro j
      refine Fin.addCases ?_ ?_ j
      · intro p
        apply Bool.le_iff_imp.mpr
        intro hp
        simp [incidenceBoundary, S, hp]
      · intro l
        apply Bool.le_iff_imp.mpr
        intro hl
        simp only [incidenceBoundary, Fin.addCases_right]
        apply decide_eq_true
        intro p hp hI
        have hx : x (Fin.castAdd m p) = true := (Finset.mem_filter.mp hp).2
        exact hex ⟨p, l, hI, hx, hl⟩
    have hx : F x = false := by
      have h := mono below
      rw [boundary S] at h
      cases hf : F x
      · rfl
      · rw [hf] at h
        exact False.elim ((by decide : ¬ (true : Bool) ≤ false) h)
    rw [hx]
    exact (decide_eq_false hex).symm

end PEqualNP.Outside.L_meta_2583
