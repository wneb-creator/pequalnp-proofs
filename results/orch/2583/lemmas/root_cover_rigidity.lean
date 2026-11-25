import PEqualNP.Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2583_aux.Geometry

theorem point_degree_le
    {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hjoin : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card ≤ q + 1 := by
  classical
  let lines : Finset (Fin N) := Finset.univ.filter (fun l => I p l)
  let others : Finset (Fin N) := Finset.univ.erase p
  have lower : ∀ l ∈ lines,
      q ≤ (others.bipartiteAbove (fun l p' => I p' l) l).card := by
    intro l hl
    have hpl : I p l := (Finset.mem_filter.mp hl).2
    have heq : others.bipartiteAbove (fun l p' => I p' l) l =
        (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp [others, Finset.bipartiteAbove, and_comm]
    rw [heq, Finset.card_erase_of_mem (by simp [hpl]), hline]
    omega
  have upper : ∀ p' ∈ others,
      (lines.bipartiteBelow (fun l p' => I p' l) p').card ≤ 1 := by
    intro p' hp'
    apply Finset.card_le_one.mpr
    intro l hl l' hl'
    have hpne : p ≠ p' := (Finset.mem_erase.mp hp').1.symm
    obtain ⟨l₀, _, huniq⟩ := hjoin p p' hpne
    have hlI : I p l ∧ I p' l := by
      simpa [lines, Finset.bipartiteBelow] using hl
    have hl'I : I p l' ∧ I p' l' := by
      simpa [lines, Finset.bipartiteBelow] using hl'
    exact (huniq l hlI).trans (huniq l' hl'I).symm
  have count := Finset.card_mul_le_card_mul
    (r := fun l p' => I p' l) lower upper
  have bound : lines.card * q ≤ N - 1 := by
    simpa [others] using count
  have hNsub : N - 1 = (q + 1) * q := by
    rw [hN]
    simp [pow_two, Nat.add_mul]
  rw [hNsub] at bound
  exact (mul_le_mul_iff_left₀ (by omega : 0 < q)).mp bound

theorem cover_card_of_degrees
    {N d : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hd : 0 < d)
    (hline : ∀ l : Fin N, d ≤ (Finset.univ.filter (fun p => I p l)).card)
    (hpoint : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card ≤ d)
    (A B : Finset (Fin N))
    (hcover : ∀ p l : Fin N, I p l → p ∈ A ∨ l ∈ B) :
    N ≤ A.card + B.card := by
  classical
  let uncovered : Finset (Fin N) := Finset.univ \ B
  have lower : ∀ l ∈ uncovered, d ≤ (A.bipartiteBelow I l).card := by
    intro l hl
    have hlB : l ∉ B := (Finset.mem_sdiff.mp hl).2
    have heq : A.bipartiteBelow I l = Finset.univ.filter (fun p => I p l) := by
      ext p
      simp only [Finset.mem_bipartiteBelow, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨And.right, fun hp => ⟨(hcover p l hp).resolve_right hlB, hp⟩⟩
    rw [heq]
    exact hline l
  have upper : ∀ p ∈ A, (uncovered.bipartiteAbove I p).card ≤ d := by
    intro p _
    apply le_trans (Finset.card_le_card ?_) (hpoint p)
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ l,
      (Finset.mem_filter.mp hl).2⟩
  have count := Finset.card_mul_le_card_mul' (r := I) lower upper
  have hle : uncovered.card ≤ A.card := (mul_le_mul_iff_left₀ hd).mp count
  have htotal := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
  simp only [Finset.card_univ, Fintype.card_fin] at htotal
  change (Finset.univ \ B).card ≤ A.card at hle
  omega

theorem plane_cover_card
    {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hjoin : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N))
    (hcover : ∀ p l : Fin N, I p l → p ∈ A ∨ l ∈ B) :
    N ≤ A.card + B.card := by
  apply cover_card_of_degrees I (d := q + 1) (by omega)
  · intro l
    exact (hline l).ge
  · exact point_degree_le I hq hN hline hjoin
  · exact hcover

end PEqualNP.Outside.L_meta_2583_aux.Geometry

namespace PEqualNP.Outside.L_meta_2583_aux.Rigidity

open scoped BigOperators

lemma cover_no_overlap_of_size
    {N d : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = d)
    (hpoint : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card ≤ d)
    (A B : Finset (Fin N)) (hsize : A.card + B.card ≤ N)
    (hcover : ∀ p l, I p l → p ∈ A ∨ l ∈ B)
    {p₀ l₀ : Fin N} (hp₀ : p₀ ∈ A) (hl₀ : l₀ ∈ B) (hi : I p₀ l₀) : False := by
  classical
  let U : Finset (Fin N) := Finset.univ \ B
  have upper (p : Fin N) : (U.bipartiteAbove I p).card ≤ d := by
    apply le_trans (Finset.card_le_card ?_) (hpoint p)
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, (Finset.mem_filter.mp hl).2⟩
  have strict : (U.bipartiteAbove I p₀).card < d := by
    apply lt_of_lt_of_le (Finset.card_lt_card ?_) (hpoint p₀)
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, (Finset.mem_filter.mp hl).2⟩
    · intro heq
      have hm : l₀ ∈ U.bipartiteAbove I p₀ := by rw [heq]; simp [hi]
      have hn : l₀ ∉ B := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hm).1).2
      exact hn hl₀
  have right (l : Fin N) (hl : l ∈ U) : (A.bipartiteBelow I l).card = d := by
    have heq : A.bipartiteBelow I l = Finset.univ.filter (fun p => I p l) := by
      ext p
      simp only [Finset.mem_bipartiteBelow, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨And.right, fun hp => ⟨(hcover p l hp).resolve_right
        (Finset.mem_sdiff.mp hl).2, hp⟩⟩
    rw [heq, hline]
  have count : (∑ p ∈ A, (U.bipartiteAbove I p).card) = U.card * d := by
    rw [Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    calc
      (∑ l ∈ U, (A.bipartiteBelow I l).card) = ∑ _l ∈ U, d :=
        Finset.sum_congr rfl (fun l hl => right l hl)
      _ = U.card * d := by simp
  have less : (∑ p ∈ A, (U.bipartiteAbove I p).card) < A.card * d := by
    have hs := Finset.sum_lt_sum (s := A) (fun p _ => upper p) ⟨p₀, hp₀, strict⟩
    simpa using hs
  have total : U.card + B.card = N := by
    simpa [U] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
  have bound : A.card ≤ U.card := by omega
  rw [count] at less
  exact (not_lt_of_ge (Nat.mul_le_mul_right d bound)) less

lemma plane_minimum_cover
    {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hjoin : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N)) (hsize : A.card + B.card ≤ N)
    (hcover : ∀ p l, I p l → p ∈ A ∨ l ∈ B) :
    (A = Finset.univ ∧ B = ∅) ∨ (A = ∅ ∧ B = Finset.univ) := by
  classical
  have hpoint := Geometry.point_degree_le I hq hN hline hjoin
  have no_overlap {p l : Fin N} (hp : p ∈ A) (hl : l ∈ B) (hi : I p l) : False :=
    cover_no_overlap_of_size I hline hpoint A B hsize hcover hp hl hi
  by_cases hA : A.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hA
    have allA : A = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro p
      by_cases he : p₀ = p
      · simpa [← he] using hp₀
      · obtain ⟨l, hl, _⟩ := hjoin p₀ p he
        exact (hcover p l hl.2).resolve_right (fun hlB => no_overlap hp₀ hlB hl.1)
    have emptyB : B = ∅ := by
      apply Finset.card_eq_zero.mp
      simp only [allA, Finset.card_univ, Fintype.card_fin] at hsize
      omega
    exact Or.inl ⟨allA, emptyB⟩
  · have emptyA : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    have allB : B = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro l
      have hpos : 0 < (Finset.univ.filter (fun p => I p l)).card := by rw [hline]; omega
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
      exact (hcover p l (Finset.mem_filter.mp hp).2).resolve_left (by simp [emptyA])
    exact Or.inr ⟨emptyA, allB⟩

end PEqualNP.Outside.L_meta_2583_aux.Rigidity
