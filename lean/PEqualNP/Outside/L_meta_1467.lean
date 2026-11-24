import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1467

theorem modlem (N a : ℕ) (h : a < 2 * N) : a % N = if a < N then a else a - N := by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The next residue. -/
def s {N : ℕ} (hN : 0 < N) (z : Fin N) : Fin N := ⟨(z.val + 1) % N, Nat.mod_lt _ hN⟩

/-- The previous residue. -/
def r {N : ℕ} (hN : 0 < N) (z : Fin N) : Fin N :=
  if z.val = 0 then ⟨N - 1, by omega⟩ else ⟨z.val - 1, by have := z.isLt; omega⟩

theorem sval {N : ℕ} (hN : 0 < N) (z : Fin N) :
    (s hN z).val = if z.val + 1 < N then z.val + 1 else 0 := by
  have hz := z.isLt
  simp only [s]
  rw [modlem N _ (by omega)]
  split_ifs <;> omega

theorem rval {N : ℕ} (hN : 0 < N) (z : Fin N) :
    (r hN z).val = if z.val = 0 then N - 1 else z.val - 1 := by
  simp only [r]
  split_ifs <;> rfl

theorem rs {N : ℕ} (hN : 0 < N) (z : Fin N) : r hN (s hN z) = z := by
  have hz := z.isLt
  apply Fin.ext
  rw [rval, sval]
  have hN1 : N - 1 + 1 = N := Nat.sub_add_cancel hN
  split_ifs with h1 h2 h2
  all_goals first | omega | contradiction

theorem s_ne {N : ℕ} (hN : 0 < N) (h3 : 3 ≤ N) (z : Fin N) : s hN z ≠ z := by
  intro h
  have hz := z.isLt
  have := congrArg Fin.val h
  rw [sval] at this
  split_ifs at this <;> omega

theorem ss_ne {N : ℕ} (hN : 0 < N) (h3 : 3 ≤ N) (z : Fin N) : s hN (s hN z) ≠ z := by
  intro h
  have hz := z.isLt
  have := congrArg Fin.val h
  rw [sval, sval] at this
  split_ifs at this <;> omega

theorem r_ne {N : ℕ} (hN : 0 < N) (h3 : 3 ≤ N) (z : Fin N) : r hN z ≠ z := by
  intro h
  have hz := z.isLt
  have := congrArg Fin.val h
  rw [rval] at this
  split_ifs at this <;> omega

theorem rr_ne {N : ℕ} (hN : 0 < N) (h3 : 3 ≤ N) (z : Fin N) : r hN (r hN z) ≠ z := by
  intro h
  have hz := z.isLt
  have := congrArg Fin.val h
  rw [rval, rval] at this
  split_ifs at this <;> omega

end PEqualNP.Outside.L_meta_1467

open PEqualNP.Outside.L_meta_1467 in
theorem PEqualNP.Outside.L_meta_1467 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)),
    2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) →
    (∀ u v : Fin n, u ≠ v → ∃ i : Fin m, u ∈ S i ∧ v ∈ S i) →
    (∃ (i : Fin m) (v : Fin n), v ∉ S i) →
    ∃ b : Fin m → Fin n, (∀ i : Fin m, b i ∉ S i) ∧
      ∀ i j : Fin m, i ≠ j → ¬ (b i ∈ S j ∧ b j ∈ S i) := by
  classical
  intro q n m S hq hcard hmeet hline hoff
  obtain ⟨i0, O, hO⟩ := hoff
  have hN : 0 < q + 1 := by omega
  have h3 : 3 ≤ q + 1 := by omega
  let e : S i0 ≃ Fin (q + 1) := Finset.equivFinOfCardEq (hcard i0)
  let pt : Fin (q + 1) → Fin n := fun z => ((e.symm z : S i0) : Fin n)
  have hpt0 : ∀ z, pt z ∈ S i0 := fun z => (e.symm z).2
  have hptinj : ∀ z z', pt z = pt z' → z = z' := fun z z' h => e.symm.injective (Subtype.ext h)
  have hptsurj : ∀ p ∈ S i0, ∃ z, pt z = p := fun p hp => ⟨e ⟨p, hp⟩, by simp [pt]⟩
  have huniq : ∀ i j : Fin m, ∀ u v : Fin n, u ≠ v → u ∈ S i → v ∈ S i → u ∈ S j → v ∈ S j →
      i = j := by
    intro i j u v huv hui hvi huj hvj
    by_contra hij
    have h1 := hmeet i j hij
    have hsub : ({u, v} : Finset (Fin n)) ⊆ S i ∩ S j := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [*]
    have := Finset.card_le_card hsub
    rw [Finset.card_pair huv, h1] at this
    omega
  have hD : ∀ i : Fin m, i ≠ i0 → ∃ z : Fin (q + 1), pt z ∈ S i ∧ ∀ z', pt z' ∈ S i → z' = z := by
    intro i hi
    obtain ⟨p, hp⟩ := Finset.card_eq_one.1 (hmeet i i0 hi)
    have hpm : p ∈ S i ∩ S i0 := by rw [hp]; simp
    obtain ⟨hpi, hp0⟩ := Finset.mem_inter.1 hpm
    obtain ⟨z, rfl⟩ := hptsurj p hp0
    refine ⟨z, hpi, fun z' hz' => hptinj _ _ ?_⟩
    have : pt z' ∈ S i ∩ S i0 := Finset.mem_inter.2 ⟨hz', hpt0 z'⟩
    rw [hp] at this
    simpa using this
  let D : Fin m → Fin (q + 1) := fun i => if h : i ≠ i0 then (hD i h).choose else ⟨0, hN⟩
  have hD1 : ∀ i, i ≠ i0 → pt (D i) ∈ S i := by
    intro i hi
    have : D i = (hD i hi).choose := by simp only [D]; rw [dif_pos hi]
    rw [this]; exact (hD i hi).choose_spec.1
  have hD2 : ∀ i, i ≠ i0 → ∀ z', pt z' ∈ S i → z' = D i := by
    intro i hi z' hz'
    have : D i = (hD i hi).choose := by simp only [D]; rw [dif_pos hi]
    rw [this]; exact (hD i hi).choose_spec.2 z' hz'
  have hK : ∀ z : Fin (q + 1), ∃ k : Fin m, O ∈ S k ∧ pt z ∈ S k := fun z =>
    hline O (pt z) (fun h => hO (h ▸ hpt0 z))
  choose K hKO hKz using hK
  have hKne : ∀ z, K z ≠ i0 := fun z h => hO (h ▸ hKO z)
  have hDK : ∀ z, D (K z) = z := fun z => (hD2 (K z) (hKne z) z (hKz z)).symm
  have hQ : ∀ z, ∃ x, x ∈ S (K z) ∧ x ≠ O ∧ x ∉ S i0 := by
    intro z
    have hc : 1 ≤ (((S (K z)).erase O).erase (pt z)).card := by
      have h1 := Finset.pred_card_le_card_erase (s := S (K z)) (a := O)
      have h2 := Finset.pred_card_le_card_erase (s := (S (K z)).erase O) (a := pt z)
      rw [hcard] at h1
      omega
    obtain ⟨x, hx⟩ := Finset.card_pos.1 hc
    simp only [Finset.mem_erase] at hx
    refine ⟨x, hx.2.2, hx.2.1, fun hx0 => ?_⟩
    obtain ⟨z', rfl⟩ := hptsurj x hx0
    have := hD2 (K z) (hKne z) z' hx.2.2
    rw [hDK] at this
    exact hx.1 (by rw [this])
  choose Q hQK hQO hQ0 using hQ
  have hQline : ∀ z j, Q z ∈ S j → O ∈ S j → j = K z := fun z j hQj hOj =>
    huniq j (K z) O (Q z) (Ne.symm (hQO z)) hOj hQj (hKO z) (hQK z)
  have hQline2 : ∀ z j, Q z ∈ S j → pt z ∈ S j → j = K z := fun z j hQj hpj =>
    huniq j (K z) (Q z) (pt z) (fun h => hQ0 z (h ▸ hpt0 z)) hQj hpj (hQK z) (hKz z)
  let b : Fin m → Fin n := fun i =>
    if i = i0 then O else if O ∈ S i then Q (r hN (D i)) else pt (s hN (D i))
  have b0 : b i0 = O := by simp [b]
  have b1 : ∀ i, i ≠ i0 → O ∈ S i → b i = Q (r hN (D i)) := by
    intro i hi hOi; simp only [b]; rw [if_neg hi, if_pos hOi]
  have b2 : ∀ i, i ≠ i0 → O ∉ S i → b i = pt (s hN (D i)) := by
    intro i hi hOi; simp only [b]; rw [if_neg hi, if_neg hOi]
  refine ⟨b, ?_, ?_⟩
  · intro i
    by_cases h0 : i = i0
    · subst h0; rw [b0]; exact hO
    · by_cases hOi : O ∈ S i
      · rw [b1 i h0 hOi]
        intro hin
        have h2 := congrArg D (hQline _ i hin hOi)
        rw [hDK] at h2
        exact r_ne hN h3 (D i) h2.symm
      · rw [b2 i h0 hOi]
        intro hin
        exact s_ne hN h3 _ (hD2 i h0 _ hin)
  · rintro i j hij ⟨hbi, hbj⟩
    by_cases hi0 : i = i0
    · subst hi0
      rw [b0] at hbi
      rw [b1 j (Ne.symm hij) hbi] at hbj
      exact hQ0 _ hbj
    by_cases hj0 : j = i0
    · subst hj0
      rw [b0] at hbj
      rw [b1 i hi0 hbj] at hbi
      exact hQ0 _ hbi
    by_cases hOi : O ∈ S i <;> by_cases hOj : O ∈ S j
    · rw [b1 i hi0 hOi] at hbi
      rw [b1 j hj0 hOj] at hbj
      have e1 := congrArg D (hQline _ j hbi hOj)
      have e2 := congrArg D (hQline _ i hbj hOi)
      rw [hDK] at e1 e2
      rw [e1] at e2
      exact rr_ne hN h3 (D i) e2.symm
    · rw [b1 i hi0 hOi] at hbi
      rw [b2 j hj0 hOj] at hbj
      have e1 := hD2 i hi0 _ hbj
      have e2 : r hN (D i) = D j := by rw [← e1, rs]
      rw [e2] at hbi
      have := hQline2 _ j hbi (hD1 j hj0)
      exact hOj (this ▸ hKO (D j))
    · rw [b2 i hi0 hOi] at hbi
      rw [b1 j hj0 hOj] at hbj
      have e1 := hD2 j hj0 _ hbi
      have e2 : r hN (D j) = D i := by rw [← e1, rs]
      rw [e2] at hbj
      have := hQline2 _ i hbj (hD1 i hi0)
      exact hOi (this ▸ hKO (D i))
    · rw [b2 i hi0 hOi] at hbi
      rw [b2 j hj0 hOj] at hbj
      have e1 := hD2 j hj0 _ hbi
      have e2 := hD2 i hi0 _ hbj
      rw [← e1] at e2
      exact ss_ne hN h3 (D i) e2
