import Mathlib.Data.Finset.Card

namespace PEqualNP.Outside.L_meta_4970

lemma star_centre_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} {Q : Finset (Fin l)} (hQ : 2 ≤ Q.card)
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q, (a', b) ∈ E) : a = a' := by
  by_cases h : a = a'
  · exact h
  · obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp
      (lt_of_lt_of_le (by decide : 1 < 2) hQ)
    exact False.elim (hE a a' b b' h hbb' ⟨ha b hb, ha b' hb', ha' b hb, ha' b' hb'⟩)

lemma distinct_centres_intersection_card {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} {Q Q' : Finset (Fin l)} (haa' : a ≠ a')
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q', (a', b) ∈ E) :
    (Q ∩ Q').card ≤ 1 := by
  by_cases h : (Q ∩ Q').card ≤ 1
  · exact h
  · have hQ : 2 ≤ (Q ∩ Q').card := Nat.lt_of_not_ge h
    exact False.elim (haa' (star_centre_unique E hE hQ
      (fun b hb => ha b (Finset.mem_inter.mp hb).1)
      (fun b hb => ha' b (Finset.mem_inter.mp hb).2)))

lemma or_function_determines_leaves {α : Type*} [DecidableEq α]
    (Q R : Finset α)
    (h : ∀ x : α → Bool, decide (∃ b ∈ Q, x b = true) =
      decide (∃ b ∈ R, x b = true)) : Q = R := by
  ext b
  have hb := h (fun a => decide (a = b))
  simpa using hb

lemma line_or_function_determines_leaves {p l : ℕ} (Q R : Finset (Fin l))
    (h : ∀ x : Fin (p + l) → Bool,
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true) =
        decide (∃ b ∈ R, x (Fin.natAdd p b) = true)) : Q = R := by
  apply or_function_determines_leaves
  intro x
  simpa using h (Fin.addCases (fun _ => false) x)

lemma point_or_function_determines_leaves {p l : ℕ} (P R : Finset (Fin p))
    (h : ∀ x : Fin (p + l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
        decide (∃ a ∈ R, x (Fin.castAdd l a) = true)) : P = R := by
  apply or_function_determines_leaves
  intro x
  simpa using h (Fin.addCases x (fun _ => false))

lemma point_or_ne_line_or {p l : ℕ} (P : Finset (Fin p)) (Q : Finset (Fin l))
    (hP : P.Nonempty) :
    ¬ (∀ x : Fin (p + l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
        decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)) := by
  intro h
  have heq := h (Fin.addCases (fun _ => true) (fun _ => false))
  have hnot : ∀ a, a ∉ P := by simpa using heq
  obtain ⟨a, ha⟩ := hP
  exact hnot a ha

lemma reverse_star_centre_unique {p l : ℕ} {E : Finset (Fin p × Fin l)}
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {b b' : Fin l} {P : Finset (Fin p)} (hP : 2 ≤ P.card)
    (hb : ∀ a ∈ P, (a, b) ∈ E) (hb' : ∀ a ∈ P, (a, b') ∈ E) : b = b' := by
  by_contra hne
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp
    (lt_of_lt_of_le (by decide : 1 < 2) hP)
  exact hfour a a' b b' haa' hne ⟨hb a ha, hb' a ha, hb a' ha', hb' a' ha'⟩

end PEqualNP.Outside.L_meta_4970

namespace PEqualNP.Outside.L_meta_4970_aux.Structural

def IsIncreasing {α : Type*} (f : (α → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

lemma below_or_of_complement {α : Type*} [DecidableEq α]
    (Q : Finset α) (f : (α → Bool) → Bool)
    (hf : IsIncreasing f)
    (hzero : f (fun i => decide (i ∉ Q)) ≠ true) :
    ∀ x, f x = true → ∃ i ∈ Q, x i = true := by
  intro x hx
  by_contra hn
  apply hzero
  apply hf x (fun i => decide (i ∉ Q)) _ hx
  intro i hi
  simp only [decide_eq_true_eq]
  intro hiQ
  exact hn ⟨i, hiQ, hi⟩

lemma and_below_or_child {α : Type*} [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool)
    (hf : IsIncreasing f) (hg : IsIncreasing g)
    (hbound : ∀ x, (f x && g x) = true → ∃ i ∈ Q, x i = true) :
    (∀ x, f x = true → ∃ i ∈ Q, x i = true) ∨
      (∀ x, g x = true → ∃ i ∈ Q, x i = true) := by
  let z : α → Bool := fun i => decide (i ∉ Q)
  have hz : ¬ (f z = true ∧ g z = true) := by
    intro h
    obtain ⟨i, hiQ, hiz⟩ := hbound z (by simp [h.1, h.2])
    simp [z, hiQ] at hiz
  by_cases h : f z = true
  · exact Or.inr (below_or_of_complement Q g hg (fun h' => hz ⟨h, h'⟩))
  · exact Or.inl (below_or_of_complement Q f hf h)

lemma and_eq_or_child {α : Type*} [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool)
    (hf : IsIncreasing f) (hg : IsIncreasing g)
    (heq : ∀ x, (f x && g x) = decide (∃ i ∈ Q, x i = true)) :
    (∀ x, f x = decide (∃ i ∈ Q, x i = true)) ∨
      (∀ x, g x = decide (∃ i ∈ Q, x i = true)) := by
  have hb : ∀ x, (f x && g x) = true → ∃ i ∈ Q, x i = true := by
    intro x hx
    rw [heq x] at hx
    exact of_decide_eq_true hx
  rcases and_below_or_child Q f g hf hg hb with h | h
  · left
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · exact h x
    · intro hx
      have hx' : (f x && g x) = true := by
        rw [heq x]
        exact decide_eq_true hx
      rw [Bool.and_eq_true] at hx'
      exact hx'.1
  · right
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · exact h x
    · intro hx
      have hx' : (f x && g x) = true := by
        rw [heq x]
        exact decide_eq_true hx
      rw [Bool.and_eq_true] at hx'
      exact hx'.2

end PEqualNP.Outside.L_meta_4970_aux.Structural
