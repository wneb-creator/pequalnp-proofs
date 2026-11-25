import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4980_aux

-- Every point of a projective plane of order q lies on exactly q + 1 lines.
theorem lines_through {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] (hq : 0 < q)
    (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  classical
  haveI : Nonempty (Fin N) := ⟨p⟩
  have hex : ∀ p' : Fin N, p' ≠ p → ∃ l, I p l ∧ I p' l :=
    fun p' h => (hU p p' (Ne.symm h)).exists
  choose! g hg using hex
  have h1 := Finset.card_eq_sum_card_fiberwise (f := g) (s := Finset.univ.filter (fun p' => p' ≠ p))
    (t := Finset.univ.filter (fun l => I p l)) (by
      intro p' hp'
      simp only [Finset.mem_coe, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq] at hp' ⊢
      exact (hg p' hp').1)
  have h2 : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.filter (fun p' => p' ≠ p)).filter (fun p' => g p' = l)).card = q := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    have : (Finset.univ.filter (fun p' => p' ≠ p)).filter (fun p' => g p' = l) =
        (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · rintro ⟨hne, rfl⟩
        exact ⟨hne, (hg p' hne).2⟩
      · rintro ⟨hne, hp'⟩
        exact ⟨hne, (hU p p' (Ne.symm hne)).unique (hg p' hne) ⟨hl, hp'⟩⟩
    rw [this, Finset.card_erase_of_mem (by simp [hl]), ← Fintype.card_subtype, hL]
    simp
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h1
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [← h1, hN, Nat.add_sub_cancel]
  ring

theorem main (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 0 < q)
    (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∃ (pt : Fin (q * q) ↪ Fin N) (ln : Fin (q + 1) × Fin q ↪ Fin N)
      (co : Fin (q + 1) → Fin (q * q) → Fin q),
      (∀ c c' : Fin (q + 1), c ≠ c' → Function.Bijective fun a : Fin (q * q) => (co c a, co c' a)) ∧
      ∀ (a : Fin (q * q)) (c : Fin (q + 1)) (i : Fin q), I (pt a) (ln (c, i)) ↔ co c a = i := by
  classical
  have uniq : ∀ {p p' l l' : Fin N}, p ≠ p' → I p l → I p' l → I p l' → I p' l' → l = l' :=
    fun hp h1 h2 h3 h4 => (hU _ _ hp).unique ⟨h1, h2⟩ ⟨h3, h4⟩
  obtain ⟨L0⟩ : Nonempty (Fin N) := ⟨⟨0, by rw [hN]; omega⟩⟩
  have eI : Fin (q + 1) ≃ {p // I p L0} := (Fintype.equivFinOfCardEq (hL L0)).symm
  have Pon : ∀ c, I (eI c).1 L0 := fun c => (eI c).2
  have Pinj : ∀ c c', c ≠ c' → (eI c).1 ≠ (eI c').1 :=
    fun c c' h h' => h (eI.injective (Subtype.ext h'))
  have hA : Fintype.card {p // ¬ I p L0} = q * q := by
    rw [Fintype.card_subtype_compl, hL L0, Fintype.card_fin, hN, sq]
    omega
  have eA : Fin (q * q) ≃ {p // ¬ I p L0} := (Fintype.equivFinOfCardEq hA).symm
  have hne : ∀ c (a : Fin (q * q)), (eI c).1 ≠ (eA a).1 := fun c a h => (eA a).2 (h ▸ Pon c)
  have hC : ∀ c, Fintype.card {l // I (eI c).1 l ∧ l ≠ L0} = q := by
    intro c
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun l => I (eI c).1 l ∧ l ≠ L0) =
        (Finset.univ.filter fun l => I (eI c).1 l).erase L0 := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      exact and_comm
    rw [this, Finset.card_erase_of_mem (by simp [Pon c]), lines_through hq hN hL hU]
    simp
  have F : ∀ c, Fin q ≃ {l // I (eI c).1 l ∧ l ≠ L0} :=
    fun c => (Fintype.equivFinOfCardEq (hC c)).symm
  have hm : ∀ c (a : Fin (q * q)), ∃ m, I (eI c).1 m ∧ I (eA a).1 m ∧ m ≠ L0 := by
    intro c a
    obtain ⟨m, ⟨h1, h2⟩, -⟩ := hU _ _ (hne c a)
    exact ⟨m, h1, h2, fun h => (eA a).2 (h ▸ h2)⟩
  choose m hm1 hm2 hm3 using hm
  refine ⟨⟨fun a => (eA a).1, fun a a' h => eA.injective (Subtype.ext h)⟩,
    ⟨fun x => (F x.1 x.2).1, ?_⟩, fun c a => (F c).symm ⟨m c a, hm1 c a, hm3 c a⟩, ?_, ?_⟩
  · rintro ⟨c, i⟩ ⟨c', i'⟩ h
    simp only at h
    by_cases hc : c = c'
    · subst hc
      have := (F c).injective (Subtype.ext h)
      rw [this]
    · exfalso
      have h2 : I (eI c').1 (F c i).1 := by rw [h]; exact (F c' i').2.1
      exact (F c i).2.2 (uniq (Pinj c c' hc) (F c i).2.1 h2 (Pon c) (Pon c'))
  · intro c c' hcc
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp⟩
    intro a a' h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 : m c a = m c a' := congrArg Subtype.val ((F c).symm.injective h1)
    have e2 : m c' a = m c' a' := congrArg Subtype.val ((F c').symm.injective h2)
    by_contra hna
    have hpne : (eA a).1 ≠ (eA a').1 := fun h => hna (eA.injective (Subtype.ext h))
    have k1 : I (eA a').1 (m c a) := by rw [e1]; exact hm2 c a'
    have k2 : I (eA a').1 (m c' a) := by rw [e2]; exact hm2 c' a'
    have e3 : m c a = m c' a := uniq hpne (hm2 c a) k1 (hm2 c' a) k2
    have k3 : I (eI c').1 (m c a) := by rw [e3]; exact hm1 c' a
    exact hm3 c a (uniq (Pinj c c' hcc) (hm1 c a) k3 (Pon c) (Pon c'))
  · intro a c i
    show I (eA a).1 (F c i).1 ↔ (F c).symm ⟨m c a, hm1 c a, hm3 c a⟩ = i
    rw [Equiv.symm_apply_eq, Subtype.ext_iff]
    constructor
    · intro h
      exact uniq (hne c a) (hm1 c a) (hm2 c a) (F c i).2.1 h
    · intro h
      have h' : m c a = (F c i).1 := h
      rw [← h']
      exact hm2 c a

end PEqualNP.Outside.L_meta_4980_aux

theorem PEqualNP.Outside.L_meta_4980 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (0 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∃ (x9 : Fin (x1 * x1) ↪ Fin x2) (x10 : Fin (x1 + (1 : ℕ)) × Fin x1 ↪ Fin x2) (x11 : Fin (x1 + (1 : ℕ)) → Fin (x1 * x1) → Fin x1), (∀ (x12 x13 : Fin (x1 + (1 : ℕ))), x12 ≠ x13 → Function.Bijective fun (x15 : Fin (x1 * x1)) => (x11 x12 x15, x11 x13 x15)) ∧ ∀ (x12 : Fin (x1 * x1)) (x13 : Fin (x1 + (1 : ℕ))) (x14 : Fin x1), x3 (x9 x12) (x10 (x13, x14)) ↔ x11 x13 x12 = x14 := by
  intro q N I _ hq hN hL hU
  exact PEqualNP.Outside.L_meta_4980_aux.main q N I hq hN hL hU
