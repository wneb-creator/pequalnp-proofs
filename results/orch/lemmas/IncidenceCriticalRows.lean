import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.CriticalRows

def pairInput {m n : ℕ} (p : Fin m) (l : Fin n) : Fin (m + n) → Bool :=
  Fin.addCases (fun a => decide (a = p)) (fun b => decide (b = l))

def completionInput {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I]
    (X : Finset (Fin m)) : Fin (m + n) → Bool :=
  Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (∀ p ∈ X, ¬ I p l))

def incidence {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I]
    (x : Fin (m + n) → Bool) : Bool :=
  decide (∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd m l) = true)

lemma critical_rows_suffice {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I]
    (f : (Fin (m + n) → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (positive : ∀ p l, I p l → f (pairInput p l) = true)
    (negative : ∀ X, f (completionInput I X) = false) :
    ∀ x, f x = incidence I x := by
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [incidence, decide_eq_true_eq]
  constructor
  · intro hx
    by_contra none
    let X : Finset (Fin m) := Finset.univ.filter fun p => x (Fin.castAdd n p) = true
    have ordered : ∀ i, x i = true → completionInput I X i = true := by
      intro i
      refine Fin.addCases (fun p => ?_) (fun l => ?_) i
      · intro hp
        simpa [completionInput, X] using hp
      · intro hl
        simp only [completionInput, Fin.addCases_right, decide_eq_true_eq]
        intro p hp incident
        exact none ⟨p, l, incident, (Finset.mem_filter.mp hp).2, hl⟩
    have h := mono x (completionInput I X) ordered hx
    rw [negative X] at h
    cases h
  · rintro ⟨p, l, incident, hp, hl⟩
    apply mono (pairInput p l) x ?_ (positive p l incident)
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · intro ha
      have eq : a = p := by simpa [pairInput] using ha
      simpa only [eq] using hp
    · intro hb
      have eq : b = l := by simpa [pairInput] using hb
      simpa only [eq] using hl

lemma incidence_pair {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I]
    {p : Fin m} {l : Fin n} (incident : I p l) :
    incidence I (pairInput p l) = true := by
  rw [incidence, decide_eq_true_eq]
  exact ⟨p, l, incident, by simp [pairInput], by simp [pairInput]⟩

lemma incidence_completion {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I]
    (X : Finset (Fin m)) : incidence I (completionInput I X) = false := by
  rw [incidence, decide_eq_false_iff_not]
  rintro ⟨p, l, incident, hp, hl⟩
  have hpx : p ∈ X := by simpa [completionInput] using hp
  have avoid : ∀ q ∈ X, ¬ I q l := by simpa [completionInput] using hl
  exact avoid p hpx incident

lemma critical_rows_iff {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I]
    (f : (Fin (m + n) → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true) :
    (∀ x, f x = incidence I x) ↔
      (∀ p l, I p l → f (pairInput p l) = true) ∧
        (∀ X, f (completionInput I X) = false) := by
  constructor
  · intro correct
    constructor
    · intro p l incident
      rw [correct]
      exact incidence_pair I incident
    · intro X
      rw [correct]
      exact incidence_completion I X
  · rintro ⟨positive, negative⟩
    exact critical_rows_suffice I f mono positive negative

end PEqualNP.Outside.L_meta_2583.CriticalRows
