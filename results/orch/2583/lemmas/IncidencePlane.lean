import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

lemma incidence_no_rectangle {N : ℕ} (I : Fin N → Fin N → Prop)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    {p p' l l' : Fin N} (hpp : p ≠ p') (hll : l ≠ l')
    (hpl : I p l) (hpl' : I p l') (hp'l : I p' l) (hp'l' : I p' l') : False := by
  obtain ⟨k, _, hk⟩ := hpair p p' hpp
  exact hll ((hk l ⟨hpl, hp'l⟩).trans (hk l' ⟨hpl', hp'l'⟩).symm)

lemma incidence_point_degree (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) : (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  classical
  let L : Finset (Fin N) := Finset.univ.filter (fun l => I p l)
  let B : Fin N → Finset (Fin N) := fun l => (Finset.univ.filter (fun r => I r l)).erase p
  have hcover : L.biUnion B = Finset.univ.erase p := by
    ext r
    constructor
    · intro hr
      obtain ⟨l, _, hrl⟩ := Finset.mem_biUnion.mp hr
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hrl).1, Finset.mem_univ r⟩
    · intro hr
      have hrp : p ≠ r := Ne.symm (Finset.mem_erase.mp hr).1
      obtain ⟨l, hl, _⟩ := hpair p r hrp
      apply Finset.mem_biUnion.mpr
      exact ⟨l, by simp [L, hl.1], by simp [B, Ne.symm hrp, hl.2]⟩
  have hdisjoint : (L : Set (Fin N)).PairwiseDisjoint B := by
    intro l hl l' hl' hll
    apply Finset.disjoint_left.mpr
    intro r hr hr'
    have hrp : p ≠ r := Ne.symm (Finset.mem_erase.mp hr).1
    have hpl : I p l := (Finset.mem_filter.mp hl).2
    have hpl' : I p l' := (Finset.mem_filter.mp hl').2
    have hrl : I r l := (Finset.mem_filter.mp (Finset.mem_erase.mp hr).2).2
    have hrl' : I r l' := (Finset.mem_filter.mp (Finset.mem_erase.mp hr').2).2
    exact incidence_no_rectangle I hpair hrp hll hpl hpl' hrl hrl'
  have hB : ∀ l ∈ L, (B l).card = q := by
    intro l hl
    have hpl : p ∈ Finset.univ.filter (fun r => I r l) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, (Finset.mem_filter.mp hl).2⟩
    dsimp [B]
    rw [Finset.card_erase_of_mem hpl, hline l]
    omega
  have hcount : L.card * q = N - 1 := by
    calc
      L.card * q = ∑ l ∈ L, q := by simp
      _ = ∑ l ∈ L, (B l).card := Finset.sum_congr rfl (fun l hl => (hB l hl).symm)
      _ = (L.biUnion B).card := (Finset.card_biUnion hdisjoint).symm
      _ = N - 1 := by rw [hcover]; simp
  have hnum : N - 1 = (q + 1) * q := by
    simp [hN, pow_two, Nat.add_mul]
  have heq : L.card * q = (q + 1) * q := hcount.trans hnum
  exact Nat.eq_of_mul_eq_mul_right (by omega) heq

end PEqualNP.Outside.L_meta_2583
