import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_meta_2583_aux.MaximalFalse

lemma point_outside_other_line {q N : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 1 ≤ q)
    (hline : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hjoin : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (l m : Fin N) (hlm : l ≠ m) : ∃ p, I p l ∧ ¬ I p m := by
  by_contra h
  have hsub : ∀ p, I p l → I p m := by simpa using h
  have hcard : 1 < (Finset.univ.filter fun p => I p l).card := by
    rw [hline]
    omega
  obtain ⟨p, hp, p', hp', hne⟩ := Finset.one_lt_card.mp hcard
  have hpI : I p l := (Finset.mem_filter.mp hp).2
  have hp'I : I p' l := (Finset.mem_filter.mp hp').2
  obtain ⟨t, ht, huniq⟩ := hjoin p p' hne
  exact hlm ((huniq l ⟨hpI, hp'I⟩).trans
    (huniq m ⟨hsub p hpI, hsub p' hp'I⟩).symm)

def incidence {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (x y : Fin N → Bool) : Bool :=
  decide (∃ p l, I p l ∧ x p = true ∧ y l = true)

def raisedPoint {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (m : Fin N) (x : Fin N → Bool) : Fin N → Bool :=
  fun p => decide (¬ I p m) || x p

def raisedLine {N : ℕ} (m : Fin N) (y : Fin N → Bool) : Fin N → Bool :=
  fun l => decide (l = m) || y l

lemma above_line_baseline {N : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (houtside : ∀ l m : Fin N, l ≠ m → ∃ p, I p l ∧ ¬ I p m)
    (m : Fin N) (x y : Fin N → Bool) :
    incidence I (raisedPoint I m x) (raisedLine m y) =
      decide ((∃ p, I p m ∧ x p = true) ∨ (∃ l, l ≠ m ∧ y l = true)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [incidence, decide_eq_true_eq]
  constructor
  · rintro ⟨p, l, hI, hx, hy⟩
    by_cases hl : l = m
    · subst l
      exact Or.inl ⟨p, hI, by simpa [raisedPoint, hI] using hx⟩
    · exact Or.inr ⟨l, hl, by simpa [raisedLine, hl] using hy⟩
  · rintro (⟨p, hI, hx⟩ | ⟨l, hl, hy⟩)
    · exact ⟨p, m, hI, by simp [raisedPoint, hx], by simp [raisedLine]⟩
    · obtain ⟨p, hI, hnot⟩ := houtside l m hl
      exact ⟨p, l, hI, by simp [raisedPoint, hnot], by simp [raisedLine, hy]⟩

lemma plane_above_line_baseline {q N : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q)
    (hline : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hjoin : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (m : Fin N) (x y : Fin N → Bool) :
    incidence I (raisedPoint I m x) (raisedLine m y) =
      decide ((∃ p, I p m ∧ x p = true) ∨ (∃ l, l ≠ m ∧ y l = true)) := by
  exact above_line_baseline I
    (point_outside_other_line I (by omega) hline hjoin) m x y

lemma plane_baseline_zero_count {q N : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hline : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (m : Fin N) :
    (Finset.univ.filter fun p => I p m).card +
      (Finset.univ.erase m).card = N + q := by
  rw [hline]
  have hN : 0 < N := Nat.zero_lt_of_lt m.isLt
  simp only [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ,
    Fintype.card_fin]
  omega

end PEqualNP.Outside.L_meta_2583_aux.MaximalFalse
