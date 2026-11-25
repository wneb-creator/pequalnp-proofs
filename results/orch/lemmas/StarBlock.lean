import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Push

namespace PEqualNP.Outside.L_meta_2585_aux

lemma rectangle_has_thin_side {P L : ℕ} (I : Fin P → Fin L → Prop)
    (hfour : ∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (A : Finset (Fin P)) (B : Finset (Fin L))
    (hI : ∀ p ∈ A, ∀ l ∈ B, I p l) : A.card ≤ 1 ∨ B.card ≤ 1 := by
  classical
  by_cases hA : A.card ≤ 1
  · exact Or.inl hA
  · right
    apply Finset.card_le_one.mpr
    intro l hl l' hl'
    by_contra hll'
    have hA' : ¬ ∀ p ∈ A, ∀ p' ∈ A, p = p' :=
      fun h => hA (Finset.card_le_one.mpr h)
    push Not at hA'
    obtain ⟨p, hp, p', hp', hpp'⟩ := hA'
    exact hfour p p' l l' hpp' hll'
      ⟨hI p hp l hl, hI p hp l' hl', hI p' hp' l hl, hI p' hp' l' hl'⟩

lemma rectangle_is_star {P L : ℕ} (I : Fin P → Fin L → Prop)
    (hfour : ∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (A : Finset (Fin P)) (B : Finset (Fin L))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hI : ∀ p ∈ A, ∀ l ∈ B, I p l) :
    (∃ p, A = {p}) ∨ (∃ l, B = {l}) := by
  obtain h | h := rectangle_has_thin_side I hfour A B hI
  · left
    apply Finset.card_eq_one.mp
    have := Finset.card_pos.mpr hA
    omega
  · right
    apply Finset.card_eq_one.mp
    have := Finset.card_pos.mpr hB
    omega

lemma neighborhood_inter_card_le_one {P L : ℕ} (I : Fin P → Fin L → Prop)
    [DecidableRel I]
    (hfour : ∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (p p' : Fin P) (hpp' : p ≠ p') :
    ((Finset.univ.filter (I p)) ∩ (Finset.univ.filter (I p'))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro l hl l' hl'
  by_contra hll'
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hl hl'
  exact hfour p p' l l' hpp' hll' ⟨hl.1, hl'.1, hl.2, hl'.2⟩

end PEqualNP.Outside.L_meta_2585_aux
