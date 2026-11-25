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


def incidencePointClosure {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun p => ∀ l, (∀ q ∈ S, ¬ I q l) → ¬ I p l)

lemma incidencePointClosure_mem {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (S : Finset (Fin n)) (p : Fin n) :
    p ∈ incidencePointClosure I S ↔ ∀ l, (∀ q ∈ S, ¬ I q l) → ¬ I p l := by
  simp [incidencePointClosure]

lemma incidencePointClosure_subset {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (S : Finset (Fin n)) : S ⊆ incidencePointClosure I S := by
  intro p hp
  apply (incidencePointClosure_mem I S p).mpr
  intro l hl
  exact hl p hp

lemma incidence_allowed_closure {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (S : Finset (Fin n)) (l : Fin m) :
    (∀ p ∈ incidencePointClosure I S, ¬ I p l) ↔ ∀ p ∈ S, ¬ I p l := by
  constructor
  · intro h p hp
    exact h p (incidencePointClosure_subset I S hp)
  · intro h p hp
    exact (incidencePointClosure_mem I S p).mp hp l h

lemma incidencePointClosure_idem {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (S : Finset (Fin n)) :
    incidencePointClosure I (incidencePointClosure I S) = incidencePointClosure I S := by
  ext p
  constructor
  · intro hp
    apply (incidencePointClosure_mem I S p).mpr
    intro l hl
    exact (incidencePointClosure_mem I (incidencePointClosure I S) p).mp hp l
      ((incidence_allowed_closure I S l).mpr hl)
  · intro hp
    apply (incidencePointClosure_mem I (incidencePointClosure I S) p).mpr
    intro l hl
    exact (incidencePointClosure_mem I S p).mp hp l
      ((incidence_allowed_closure I S l).mp hl)

lemma incidenceBoundary_le_closure {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (S : Finset (Fin n)) :
    incidenceBoundary I S ≤ incidenceBoundary I (incidencePointClosure I S) := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro p
    apply Bool.le_iff_imp.mpr
    intro hp
    have hmem : p ∈ S := by simpa [incidenceBoundary] using hp
    have hclosed := incidencePointClosure_subset I S hmem
    simpa [incidenceBoundary] using hclosed
  · intro l
    simp only [incidenceBoundary, Fin.addCases_right, incidence_allowed_closure, le_refl]

lemma incidence_closed_boundary_complete {n m : ℕ} (I : Fin n → Fin m → Prop)
    [DecidableRel I] (F : (Fin (n + m) → Bool) → Bool) (mono : Monotone F)
    (pairs : ∀ p l, I p l → F (incidencePairInput p l) = true)
    (boundary : ∀ S : Finset (Fin n), incidencePointClosure I S = S →
      F (incidenceBoundary I S) = false) :
    ∀ x, F x = decide (∃ p l, I p l ∧ x (Fin.castAdd m p) = true ∧
      x (Fin.natAdd n l) = true) := by
  apply incidence_boundary_complete I F mono pairs
  intro S
  have h := mono (incidenceBoundary_le_closure I S)
  have hclosed := boundary (incidencePointClosure I S) (incidencePointClosure_idem I S)
  rw [hclosed] at h
  cases hf : F (incidenceBoundary I S)
  · rfl
  · rw [hf] at h
    exact False.elim ((by decide : ¬ (true : Bool) ≤ false) h)

end PEqualNP.Outside.L_meta_2583
