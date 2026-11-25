import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Bool.Basic
import Mathlib.Order.Monotone.Basic

namespace PEqualNP.Outside.L_meta_2583

def cleanAndSingleton {n : Nat} (i : Fin n) : Fin n → Bool :=
  fun j => decide (j = i)

def cleanAndSupport {n : Nat} (A : (Fin n → Bool) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => A (cleanAndSingleton i) = true

lemma cleanAnd_support_rectangle {n : Nat}
    (F A B : (Fin n → Bool) → Bool) (R : Fin n → Fin n → Prop)
    (monoA : Monotone A) (monoB : Monotone B)
    (below : ∀ z, A z = true → B z = true → F z = true)
    (pairs : ∀ u v, F (cleanAndSingleton u ⊔ cleanAndSingleton v) = true → R u v)
    {u v : Fin n} (hu : u ∈ cleanAndSupport A) (hv : v ∈ cleanAndSupport B) :
    R u v := by
  have ha : A (cleanAndSingleton u) = true := (Finset.mem_filter.mp hu).2
  have hb : B (cleanAndSingleton v) = true := (Finset.mem_filter.mp hv).2
  apply pairs
  apply below
  · exact Bool.le_iff_imp.mp (monoA le_sup_left) ha
  · exact Bool.le_iff_imp.mp (monoB le_sup_right) hb

lemma cleanAnd_support_star {n : Nat}
    (F A B : (Fin n → Bool) → Bool) (R : Fin n → Fin n → Prop)
    (monoA : Monotone A) (monoB : Monotone B)
    (below : ∀ z, A z = true → B z = true → F z = true)
    (pairs : ∀ u v, F (cleanAndSingleton u ⊔ cleanAndSingleton v) = true → R u v)
    (noFour : ∀ a a', a ≠ a' → ∀ b b',
      R a b → R a' b → R a b' → R a' b' → b = b') :
    (cleanAndSupport A).card ≤ 1 ∨ (cleanAndSupport B).card ≤ 1 := by
  by_cases ha : (cleanAndSupport A).card ≤ 1
  · exact Or.inl ha
  · right
    obtain ⟨a, ha, a', ha', hne⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge ha)
    apply Finset.card_le_one.mpr
    intro b hb b' hb'
    apply noFour a a' hne b b'
    · exact cleanAnd_support_rectangle F A B R monoA monoB below pairs ha hb
    · exact cleanAnd_support_rectangle F A B R monoA monoB below pairs ha' hb
    · exact cleanAnd_support_rectangle F A B R monoA monoB below pairs ha hb'
    · exact cleanAnd_support_rectangle F A B R monoA monoB below pairs ha' hb'

lemma incidence_rectangle_star {N : Nat} (I : Fin N → Fin N → Prop)
    (uniqueLine : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l)
    (points lines : Finset (Fin N))
    (rectangle : ∀ p ∈ points, ∀ l ∈ lines, I p l) :
    points.card ≤ 1 ∨ lines.card ≤ 1 := by
  by_cases hp : points.card ≤ 1
  · exact Or.inl hp
  · right
    obtain ⟨p, hp, p', hp', hne⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge hp)
    obtain ⟨l, hl, hu⟩ := uniqueLine p p' hne
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact (hu a ⟨rectangle p hp a ha, rectangle p' hp' a ha⟩).trans
      (hu b ⟨rectangle p hp b hb, rectangle p' hp' b hb⟩).symm

lemma cleanAnd_pair_requires_nonlinear_operand {n : Nat}
    (F A B : (Fin n → Bool) → Bool) (u v : Fin n)
    (below : ∀ z, A z = true → B z = true → F z = true)
    (fu : F (cleanAndSingleton u) = false)
    (fv : F (cleanAndSingleton v) = false)
    (ap : A (cleanAndSingleton u ⊔ cleanAndSingleton v) = true)
    (bp : B (cleanAndSingleton u ⊔ cleanAndSingleton v) = true)
    (noCross : ¬ ((A (cleanAndSingleton u) = true ∧ B (cleanAndSingleton v) = true) ∨
      (A (cleanAndSingleton v) = true ∧ B (cleanAndSingleton u) = true))) :
    (A (cleanAndSingleton u ⊔ cleanAndSingleton v) = true ∧
      A (cleanAndSingleton u) = false ∧ A (cleanAndSingleton v) = false) ∨
    (B (cleanAndSingleton u ⊔ cleanAndSingleton v) = true ∧
      B (cleanAndSingleton u) = false ∧ B (cleanAndSingleton v) = false) := by
  have nbu : A (cleanAndSingleton u) = true → B (cleanAndSingleton u) = false := by
    intro h
    cases hb : B (cleanAndSingleton u)
    · rfl
    · have hf := below (cleanAndSingleton u) h hb
      rw [fu] at hf
      cases hf
  have nbv : A (cleanAndSingleton v) = true → B (cleanAndSingleton v) = false := by
    intro h
    cases hb : B (cleanAndSingleton v)
    · rfl
    · have hf := below (cleanAndSingleton v) h hb
      rw [fv] at hf
      cases hf
  cases hau : A (cleanAndSingleton u)
  · cases hav : A (cleanAndSingleton v)
    · exact Or.inl ⟨ap, rfl, rfl⟩
    · refine Or.inr ⟨bp, ?_, nbv hav⟩
      cases hbu : B (cleanAndSingleton u)
      · rfl
      · exact False.elim (noCross (Or.inr ⟨hav, hbu⟩))
  · refine Or.inr ⟨bp, nbu hau, ?_⟩
    cases hbv : B (cleanAndSingleton v)
    · rfl
    · exact False.elim (noCross (Or.inl ⟨hau, hbv⟩))

end PEqualNP.Outside.L_meta_2583
