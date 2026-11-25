import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.Structural

lemma point_degree (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) : (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  classical
  let L : Finset (Fin N) := Finset.univ.filter (fun l => I p l)
  let F (l : Fin N) : Finset (Fin N) := (Finset.univ.filter (fun r => I r l)).erase p
  have hc : ∀ l ∈ L, (F l).card = q := by
    intro l hl
    have hp : p ∈ Finset.univ.filter (fun r => I r l) := by
      simpa [L] using hl
    simp only [F, Finset.card_erase_of_mem hp, hline]
    omega
  have hd : (L : Set (Fin N)).PairwiseDisjoint F := by
    intro l hl l' hl' hne
    apply Finset.disjoint_left.mpr
    intro r hr hr'
    have hrl : r ≠ p ∧ I r l := by simpa [F] using hr
    have hrl' : r ≠ p ∧ I r l' := by simpa [F] using hr'
    have hpl : I p l := by simpa [L] using hl
    have hpl' : I p l' := by simpa [L] using hl'
    obtain ⟨a, ha, hu⟩ := hpair p r (Ne.symm hrl.1)
    exact hne ((hu l ⟨hpl, hrl.2⟩).trans (hu l' ⟨hpl', hrl'.2⟩).symm)
  have hu : L.biUnion F = Finset.univ.erase p := by
    ext r
    simp only [Finset.mem_biUnion, L, F, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_erase]
    constructor
    · rintro ⟨l, hpl, hrp, hrl⟩
      exact ⟨hrp, trivial⟩
    · rintro ⟨hrp, _⟩
      obtain ⟨l, ⟨hpl, hrl⟩, _⟩ := hpair p r (Ne.symm hrp)
      exact ⟨l, hpl, hrp, hrl⟩
  have hsum : (L.biUnion F).card = L.card * q := by
    rw [Finset.card_biUnion hd]
    exact Finset.sum_const_nat hc
  have hcount : (Finset.univ.erase p).card + 1 = N := by
    simpa using Finset.card_erase_add_one (Finset.mem_univ p)
  rw [← hu, hsum] at hcount
  change L.card = q + 1
  have hmul : q * L.card = q * (q + 1) := by nlinarith
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul

lemma pencil_cover_card {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) (X : Finset (Fin N)) (hp : p ∉ X)
    (hc : ∀ l : Fin N, I p l → ∃ a ∈ X, I a l) :
    (Finset.univ.filter (fun l => I p l)).card ≤ X.card := by
  classical
  let L := Finset.univ.filter (fun l => I p l)
  let J := fun a : Fin N => Finset.univ.filter (fun l => I p l ∧ I a l)
  have hJ : ∀ a ∈ X, (J a).card ≤ 1 := by
    intro a ha
    apply Finset.card_le_one.mpr
    intro l hl r hr
    have hpa : p ≠ a := by rintro rfl; exact hp ha
    obtain ⟨k, _, hk⟩ := hpair p a hpa
    exact (hk l (Finset.mem_filter.mp hl).2).trans
      (hk r (Finset.mem_filter.mp hr).2).symm
  have hsub : L ⊆ X.biUnion J := by
    intro l hl
    obtain ⟨a, ha, hal⟩ := hc l (Finset.mem_filter.mp hl).2
    exact Finset.mem_biUnion.mpr ⟨a, ha, by simp [J, (Finset.mem_filter.mp hl).2, hal]⟩
  calc
    L.card ≤ (X.biUnion J).card := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ X, (J a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ X, 1 := Finset.sum_le_sum hJ
    _ = X.card := by simp

lemma independent_pencil_replacement {q N : ℕ} (I : Fin N → Fin N → Prop)
    [DecidableRel I] (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) (X Y : Finset (Fin N)) (hp : p ∉ X)
    (hind : ∀ a ∈ X, ∀ b ∈ Y, ¬ I a b)
    (hreplace : ∀ l : Fin N, I p l → ∃ a ∈ X, ∃ b ∈ insert l Y, I a b) :
    q + 1 ≤ X.card := by
  rw [← point_degree q N I hq hN hline hpair p]
  apply pencil_cover_card I hpair p X hp
  intro l hpl
  obtain ⟨a, ha, b, hb, hab⟩ := hreplace l hpl
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact ⟨a, ha, hab⟩
  · exact (hind a ha b hb hab).elim

end PEqualNP.Outside.L_meta_2583_aux.Structural
