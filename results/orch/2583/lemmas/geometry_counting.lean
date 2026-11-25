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
