import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1453

open Finset

/-- Colourings that give two fixed different points the same colour: at most a `1/K` share. -/
theorem card_eq (n K : ℕ) (p q : Fin n) (hpq : p ≠ q) :
    (univ.filter fun g : Fin n → Fin K => g p = g q).card * K ≤ K ^ n := by
  classical
  have h := Finset.card_le_card_of_injOn
    (s := (univ.filter fun g : Fin n → Fin K => g p = g q) ×ˢ (univ : Finset (Fin K)))
    (t := (univ : Finset (Fin n → Fin K)))
    (fun x => Function.update x.1 p x.2) (by intro _ _; simp) (by
      rintro ⟨g, a⟩ hg ⟨g', a'⟩ hg' heq
      simp only [coe_product, coe_filter, mem_univ, true_and, coe_univ, Set.mem_prod,
        Set.mem_setOf_eq, Set.mem_ofPred_eq, Set.mem_univ, and_true] at hg hg'
      have ha : a = a' := by simpa using congrFun heq p
      have hi : ∀ i, i ≠ p → g i = g' i := fun i hi => by
        simpa [Function.update_of_ne hi] using congrFun heq i
      refine Prod.ext (funext fun i => ?_) ha
      by_cases h : i = p
      · subst h; show g i = g' i; rw [hg, hg', hi q hpq.symm]
      · exact hi i h)
  simpa [Finset.card_product] using h

open Classical in
/-- The colourings that are not injective on `S`. -/
noncomputable def nonInj (n K : ℕ) (S : Finset (Fin n)) : Finset (Fin n → Fin K) :=
  univ.filter fun g => ¬ Set.InjOn g (S : Set (Fin n))

theorem nonInj_card (n w : ℕ) (hw : 1 ≤ w) (S : Finset (Fin n)) (hS : S.card ≤ w) :
    2 * (nonInj n (w ^ 2) S).card ≤ (w ^ 2) ^ n := by
  classical
  set K := w ^ 2 with hK
  have hKpos : 0 < K := by positivity
  let E : Finset (Fin n) → Finset (Fin n → Fin K) := fun t =>
    univ.filter fun g => ∃ p ∈ t, ∃ q ∈ t, p ≠ q ∧ g p = g q
  have hsub : nonInj n K S ⊆ (S.powersetCard 2).biUnion E := by
    intro g hg
    have hg' : ¬ Set.InjOn g (S : Set (Fin n)) := by simpa [nonInj] using hg
    simp only [Set.InjOn] at hg'
    push_neg at hg'
    obtain ⟨p, hp, q, hq, hgpq, hne⟩ := hg'
    simp only [mem_biUnion, mem_powersetCard]
    refine ⟨{p, q}, ⟨?_, Finset.card_pair hne⟩, ?_⟩
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact_mod_cast hp
      · exact_mod_cast hq
    · simp only [E, mem_filter, mem_univ, true_and]
      exact ⟨p, by simp, q, by simp, hne, hgpq⟩
  have hE : ∀ t ∈ S.powersetCard 2, (E t).card * K ≤ K ^ n := by
    intro t ht
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (mem_powersetCard.1 ht).2
    refine le_trans (Nat.mul_le_mul_right K (Finset.card_le_card ?_)) (card_eq n K a b hab)
    intro g hg
    simp only [E, mem_filter, mem_univ, true_and, mem_insert, mem_singleton] at hg ⊢
    obtain ⟨p, hp, q, hq, hne, h⟩ := hg
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd rfl hne
    · exact h
    · exact h.symm
    · exact absurd rfl hne
  have h1 : (nonInj n K S).card * K ≤ (S.card.choose 2) * K ^ n := by
    calc (nonInj n K S).card * K ≤ ((S.powersetCard 2).biUnion E).card * K :=
          Nat.mul_le_mul_right K (Finset.card_le_card hsub)
      _ ≤ (∑ t ∈ S.powersetCard 2, (E t).card) * K :=
          Nat.mul_le_mul_right K Finset.card_biUnion_le
      _ = ∑ t ∈ S.powersetCard 2, (E t).card * K := Finset.sum_mul _ _ _
      _ ≤ ∑ _t ∈ S.powersetCard 2, K ^ n := Finset.sum_le_sum hE
      _ = (S.card.choose 2) * K ^ n := by simp [Finset.card_powersetCard]
  have h2 : S.card.choose 2 * 2 ≤ K := by
    rw [Nat.choose_two_right]
    calc S.card * (S.card - 1) / 2 * 2 ≤ S.card * (S.card - 1) := Nat.div_mul_le_self _ _
      _ ≤ w * w := Nat.mul_le_mul hS ((Nat.sub_le _ _).trans hS)
      _ = K := by rw [hK]; ring
  have h3 : 2 * (nonInj n K S).card * K ≤ K ^ n * K := by
    calc 2 * (nonInj n K S).card * K = 2 * ((nonInj n K S).card * K) := by ring
      _ ≤ 2 * ((S.card.choose 2) * K ^ n) := Nat.mul_le_mul_left 2 h1
      _ = (S.card.choose 2 * 2) * K ^ n := by ring
      _ ≤ K * K ^ n := Nat.mul_le_mul_right _ h2
      _ = K ^ n * K := by ring
  exact Nat.le_of_mul_le_mul_right h3 hKpos

end PEqualNP.Outside.L_meta_1453

theorem PEqualNP.Outside.L_meta_1453 : ∀ (n w : ℕ), 2 ≤ n → 1 ≤ w → ∃ c : Fin (w * Nat.clog 2 n + 1) → Fin n → Fin (w ^ 2), ∀ S : Finset (Fin n), S.card ≤ w → ∃ j : Fin (w * Nat.clog 2 n + 1), Set.InjOn (c j) (S : Set (Fin n)) := by
  classical
  intro n w hn hw
  set N := w * Nat.clog 2 n + 1 with hN
  set K := w ^ 2 with hK
  set s := min w n with hs
  let Bad : Finset (Fin N → Fin n → Fin K) :=
    ((Finset.univ : Finset (Fin n)).powersetCard s).biUnion fun S =>
      Fintype.piFinset fun _ : Fin N => PEqualNP.Outside.L_meta_1453.nonInj n K S
  have hT : Fintype.card (Fin N → Fin n → Fin K) = (K ^ n) ^ N := by simp
  have hTpos : 0 < (K ^ n) ^ N := by positivity
  have hbad : Bad.card * 2 ^ N ≤ n.choose s * (K ^ n) ^ N := by
    have hS : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
        (Fintype.piFinset fun _ : Fin N => PEqualNP.Outside.L_meta_1453.nonInj n K S).card * 2 ^ N
          ≤ (K ^ n) ^ N := by
      intro S hS
      have hc : S.card ≤ w := by
        rw [(Finset.mem_powersetCard.1 hS).2]; exact min_le_left _ _
      have := PEqualNP.Outside.L_meta_1453.nonInj_card n w hw S hc
      rw [Fintype.card_piFinset]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Nat.mul_pow]
      exact Nat.pow_le_pow_left (by rw [Nat.mul_comm]; exact this) N
    calc Bad.card * 2 ^ N
        ≤ (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
            (Fintype.piFinset fun _ : Fin N => PEqualNP.Outside.L_meta_1453.nonInj n K S).card) * 2 ^ N :=
          Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
            (Fintype.piFinset fun _ : Fin N => PEqualNP.Outside.L_meta_1453.nonInj n K S).card * 2 ^ N :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ _S ∈ (Finset.univ : Finset (Fin n)).powersetCard s, (K ^ n) ^ N := Finset.sum_le_sum hS
      _ = n.choose s * (K ^ n) ^ N := by simp [Finset.card_powersetCard]
  have hch : n.choose s < 2 ^ N := by
    calc n.choose s ≤ n ^ s := Nat.choose_le_pow n s
      _ ≤ n ^ w := Nat.pow_le_pow_right (by omega) (min_le_left _ _)
      _ ≤ (2 ^ Nat.clog 2 n) ^ w := Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) n) w
      _ = 2 ^ (w * Nat.clog 2 n) := by rw [← pow_mul, Nat.mul_comm]
      _ < 2 ^ N := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hlt : Bad.card < Fintype.card (Fin N → Fin n → Fin K) := by
    rw [hT]
    have h1 : Bad.card * 2 ^ N < (K ^ n) ^ N * 2 ^ N :=
      lt_of_le_of_lt hbad (by rw [Nat.mul_comm]; exact Nat.mul_lt_mul_of_pos_left hch hTpos)
    exact Nat.lt_of_mul_lt_mul_right h1
  obtain ⟨c, hc⟩ : ∃ c, c ∉ Bad := by
    by_contra hall
    push_neg at hall
    have : Bad = Finset.univ := Finset.eq_univ_iff_forall.2 hall
    rw [this, Finset.card_univ] at hlt
    exact lt_irrefl _ hlt
  refine ⟨c, fun S hSw => ?_⟩
  have hSs : S.card ≤ s := le_min hSw (by simpa using Finset.card_le_univ S)
  obtain ⟨S', hsub, -, hcard⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ S) hSs
    (show s ≤ (Finset.univ : Finset (Fin n)).card by simp [hs])
  have hnot : ¬ ∀ j : Fin N, c j ∈ PEqualNP.Outside.L_meta_1453.nonInj n K S' := by
    intro hj
    apply hc
    simp only [Bad, Finset.mem_biUnion, Finset.mem_powersetCard, Fintype.mem_piFinset]
    exact ⟨S', ⟨Finset.subset_univ _, hcard⟩, hj⟩
  push_neg at hnot
  obtain ⟨j, hj⟩ := hnot
  refine ⟨j, ?_⟩
  simp only [PEqualNP.Outside.L_meta_1453.nonInj, Finset.mem_filter, Finset.mem_univ, true_and,
    not_not] at hj
  exact hj.mono (by exact_mod_cast hsub)
