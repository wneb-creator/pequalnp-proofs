import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

lemma rectangle_degenerate {N : ℕ} {I : Fin N → Fin N → Prop}
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    {p p' l l' : Fin N} (hpl : I p l) (hpl' : I p l')
    (hp'l : I p' l) (hp'l' : I p' l') : p = p' ∨ l = l' := by
  by_cases hp : p = p'
  · exact Or.inl hp
  · obtain ⟨k, _, hk⟩ := hu p p' hp
    exact Or.inr ((hk l ⟨hpl, hp'l⟩).trans (hk l' ⟨hpl', hp'l'⟩).symm)

lemma point_lines_card {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hc : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) : (Finset.univ.filter fun l => I p l).card = q + 1 := by
  classical
  let L := Finset.univ.filter fun l => I p l
  let R := fun l => (Finset.univ.filter fun x => I x l).erase p
  have hcover : L.biUnion R = Finset.univ.erase p := by
    ext x
    constructor
    · intro hx
      obtain ⟨l, _, hx⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ _⟩
    · intro hx
      have hxp := (Finset.mem_erase.mp hx).1
      obtain ⟨l, hl, _⟩ := hu p x hxp.symm
      exact Finset.mem_biUnion.mpr ⟨l, by simp [L, hl.1], by simp [R, hxp, hl.2]⟩
  have hd : (L : Set (Fin N)).PairwiseDisjoint R := by
    intro l hl l' hl' hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    have hpx : p ≠ x := (Finset.mem_erase.mp hx).1.symm
    have hlp : I p l := (Finset.mem_filter.mp hl).2
    have hlp' : I p l' := (Finset.mem_filter.mp hl').2
    have hlx : I x l := (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).2
    have hlx' : I x l' := (Finset.mem_filter.mp (Finset.mem_erase.mp hx').2).2
    exact hne ((rectangle_degenerate hu hlp hlp' hlx hlx').resolve_left hpx)
  have hr (l : Fin N) (hl : l ∈ L) : (R l).card = q := by
    have hp : p ∈ Finset.univ.filter fun x => I x l := by
      simpa only [L, Finset.mem_filter, Finset.mem_univ, true_and] using hl
    simp only [R, Finset.card_erase_of_mem hp, hc]
    omega
  have he := Finset.card_biUnion hd
  rw [hcover, Finset.card_erase_of_mem (Finset.mem_univ p)] at he
  simp only [Finset.card_univ, Fintype.card_fin] at he
  have hsum : ∑ l ∈ L, (R l).card = L.card * q := by
    simp only [Finset.sum_congr rfl hr, Finset.sum_const, smul_eq_mul]
  rw [hsum] at he
  have : L.card * q = (q + 1) * q := by
    rw [← he, hN]
    simp only [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) this

lemma plane_cover_bound {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hc : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N)) (hcover : ∀ p l, I p l → p ∈ A ∨ l ∈ B) :
    N ≤ A.card + B.card := by
  classical
  have hr := point_lines_card I hq hN hc hu
  have hrows (p : Fin N) : (∑ l : Fin N, if I p l then (1 : ℕ) else 0) = q + 1 := by
    simpa using hr p
  have hcols (l : Fin N) : (∑ p : Fin N, if I p l then (1 : ℕ) else 0) = q + 1 := by
    simpa using hc l
  have hineq : N * (q + 1) ≤ (A.card + B.card) * (q + 1) := by
    calc
      N * (q + 1) = ∑ p : Fin N, ∑ l : Fin N, if I p l then (1 : ℕ) else 0 := by
        simp [hrows]
      _ ≤ ∑ p : Fin N, ∑ l : Fin N,
          ((if p ∈ A then (if I p l then (1 : ℕ) else 0) else 0) +
            (if l ∈ B then (if I p l then (1 : ℕ) else 0) else 0)) := by
        apply Finset.sum_le_sum
        intro p _
        apply Finset.sum_le_sum
        intro l _
        by_cases hi : I p l
        · rcases hcover p l hi with hp | hl
          · simp [hi, hp]
          · simp [hi, hl]
        · simp [hi]
      _ = (A.card + B.card) * (q + 1) := by
        simp only [Finset.sum_add_distrib]
        have ha : (∑ p : Fin N, ∑ l : Fin N,
            if p ∈ A then (if I p l then (1 : ℕ) else 0) else 0) = A.card * (q + 1) := by
          simp [Finset.sum_ite_irrel, hrows]
        have hb : (∑ p : Fin N, ∑ l : Fin N,
            if l ∈ B then (if I p l then (1 : ℕ) else 0) else 0) = B.card * (q + 1) := by
          rw [Finset.sum_comm]
          simp [Finset.sum_ite_irrel, hcols]
        rw [ha, hb, Nat.add_mul]
  exact Nat.le_of_mul_le_mul_right hineq (by omega)

end PEqualNP.Outside.L_meta_2583
