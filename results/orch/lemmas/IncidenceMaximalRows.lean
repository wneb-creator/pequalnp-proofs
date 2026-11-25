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

namespace PEqualNP.Outside.L_meta_2583.CriticalRows

def closePoints {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I]
    (X : Finset (Fin m)) : Finset (Fin m) :=
  Finset.univ.filter fun p => ∀ l, (∀ a ∈ X, ¬ I a l) → ¬ I p l

lemma subset_close {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I]
    (X : Finset (Fin m)) : X ⊆ closePoints I X := by
  intro p hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun l hl => hl p hp⟩

lemma avoids_close {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I]
    (X : Finset (Fin m)) (l : Fin n) :
    (∀ p ∈ closePoints I X, ¬ I p l) ↔ ∀ p ∈ X, ¬ I p l := by
  constructor
  · intro h p hp
    exact h p (subset_close I X hp)
  · intro h p hp
    exact (Finset.mem_filter.mp hp).2 l h

lemma close_idem {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I]
    (X : Finset (Fin m)) : closePoints I (closePoints I X) = closePoints I X := by
  ext p
  change (p ∈ Finset.univ.filter (fun p =>
    ∀ l, (∀ a ∈ closePoints I X, ¬ I a l) → ¬ I p l)) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, avoids_close]
  simp only [closePoints, Finset.mem_filter, Finset.mem_univ, true_and]

lemma completion_le_closure {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I]
    (X : Finset (Fin m)) :
    ∀ i, completionInput I X i = true → completionInput I (closePoints I X) i = true := by
  intro i
  refine Fin.addCases (fun p => ?_) (fun l => ?_) i
  · simp only [completionInput, Fin.addCases_left, decide_eq_true_eq]
    exact fun hp => subset_close I X hp
  · simp only [completionInput, Fin.addCases_right, decide_eq_true_eq]
    exact (avoids_close I X l).mpr

lemma closed_rows_suffice {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I]
    (f : (Fin (m + n) → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (positive : ∀ p l, I p l → f (pairInput p l) = true)
    (negative : ∀ X, closePoints I X = X → f (completionInput I X) = false) :
    ∀ x, f x = incidence I x := by
  apply critical_rows_suffice I f mono positive
  intro X
  apply Bool.eq_false_iff.mpr
  intro h
  have monotoneResult := mono (completionInput I X) (completionInput I (closePoints I X))
    (completion_le_closure I X) h
  rw [negative _ (close_idem I X)] at monotoneResult
  cases monotoneResult

lemma closed_rows_iff {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I]
    (f : (Fin (m + n) → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true) :
    (∀ x, f x = incidence I x) ↔
      (∀ p l, I p l → f (pairInput p l) = true) ∧
        (∀ X, closePoints I X = X → f (completionInput I X) = false) := by
  constructor
  · intro correct
    exact ⟨fun p l incident => (correct _).trans (incidence_pair I incident),
      fun X _ => (correct _).trans (incidence_completion I X)⟩
  · rintro ⟨positive, negative⟩
    exact closed_rows_suffice I f mono positive negative

def criticalRows {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I] :
    Set (Fin (m + n) → Bool) :=
  {x | (∃ p l, I p l ∧ x = pairInput p l) ∨
    ∃ X, closePoints I X = X ∧ x = completionInput I X}

lemma criticalRows_determine {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I]
    (f : (Fin (m + n) → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (agree : ∀ x ∈ criticalRows I, f x = incidence I x) :
    f = incidence I := by
  funext x
  apply closed_rows_suffice I f mono ?_ ?_ x
  · intro p l incident
    exact (agree _ (Or.inl ⟨p, l, incident, rfl⟩)).trans (incidence_pair I incident)
  · intro X closed
    exact (agree _ (Or.inr ⟨X, closed, rfl⟩)).trans (incidence_completion I X)

end PEqualNP.Outside.L_meta_2583.CriticalRows

namespace PEqualNP.Outside.L_meta_2583.CriticalRows

lemma closed_iff_omitted_neighbor {m n : ℕ}
    (I : Fin m → Fin n → Prop) [DecidableRel I] (X : Finset (Fin m)) :
    closePoints I X = X ↔
      ∀ p, p ∉ X → ∃ l, (∀ a ∈ X, ¬ I a l) ∧ I p l := by
  constructor
  · intro closed p omitted
    have missing : ¬ ∀ l, (∀ a ∈ X, ¬ I a l) → ¬ I p l := by
      intro h
      have member : p ∈ closePoints I X :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      exact omitted (closed ▸ member)
    push Not at missing
    exact missing
  · intro omitted
    apply Finset.Subset.antisymm ?_ (subset_close I X)
    intro p hp
    by_contra hn
    obtain ⟨l, avoids, incident⟩ := omitted p hn
    exact (Finset.mem_filter.mp hp).2 l avoids incident

lemma closed_completion_maximal {m n : ℕ}
    (I : Fin m → Fin n → Prop) [DecidableRel I] (X : Finset (Fin m))
    (closed : closePoints I X = X) (y : Fin (m + n) → Bool)
    (larger : ∀ i, completionInput I X i = true → y i = true)
    (negative : incidence I y = false) : y = completionInput I X := by
  have noEdge : ¬ ∃ p l, I p l ∧ y (Fin.castAdd n p) = true ∧
      y (Fin.natAdd m l) = true := by
    simpa only [incidence, decide_eq_false_iff_not] using negative
  funext i
  apply Bool.eq_iff_iff.mpr
  constructor
  · refine Fin.addCases (fun p => ?_) (fun l => ?_) i
    · intro hp
      simp only [completionInput, Fin.addCases_left, decide_eq_true_eq]
      by_contra omitted
      obtain ⟨l, avoids, incident⟩ := (closed_iff_omitted_neighbor I X).mp closed p omitted
      have hl : completionInput I X (Fin.natAdd m l) = true := by
        simpa only [completionInput, Fin.addCases_right, decide_eq_true_eq] using avoids
      exact noEdge ⟨p, l, incident, hp, larger _ hl⟩
    · intro hl
      simp only [completionInput, Fin.addCases_right, decide_eq_true_eq]
      intro p hp incident
      have hx : completionInput I X (Fin.castAdd n p) = true := by
        simpa only [completionInput, Fin.addCases_left, decide_eq_true_eq] using hp
      exact noEdge ⟨p, l, incident, larger _ hx, hl⟩
  · exact larger i

lemma closed_iff_completion_maximal {m n : ℕ}
    (I : Fin m → Fin n → Prop) [DecidableRel I] (X : Finset (Fin m)) :
    closePoints I X = X ↔
      ∀ y : Fin (m + n) → Bool,
        (∀ i, completionInput I X i = true → y i = true) →
        incidence I y = false → y = completionInput I X := by
  constructor
  · exact closed_completion_maximal I X
  · intro maximal
    have eq := maximal (completionInput I (closePoints I X))
      (completion_le_closure I X) (incidence_completion I (closePoints I X))
    apply Finset.Subset.antisymm ?_ (subset_close I X)
    intro p hp
    have coordinate := congrFun eq (Fin.castAdd n p)
    have hi : completionInput I (closePoints I X) (Fin.castAdd n p) = true := by
      simpa only [completionInput, Fin.addCases_left, decide_eq_true_eq] using hp
    rw [coordinate] at hi
    simpa only [completionInput, Fin.addCases_left, decide_eq_true_eq] using hi

end PEqualNP.Outside.L_meta_2583.CriticalRows
