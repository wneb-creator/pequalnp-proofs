import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.Outside.L_meta_5324_aux

lemma star_cover_matching_bound {n m : ℕ}
    (H M : Finset (Fin n × Fin m))
    (F : Finset (Finset (Fin n × Fin m)))
    (hcover : H ⊆ F.biUnion id)
    (hstar : ∀ S ∈ F,
      (∃ p : Fin n, ∀ e ∈ S, e.1 = p) ∨
      (∃ l : Fin m, ∀ e ∈ S, e.2 = l))
    (hsub : M ⊆ H)
    (hrow : ∀ e ∈ M, ∀ d ∈ M, e.1 = d.1 → e = d)
    (hcol : ∀ e ∈ M, ∀ d ∈ M, e.2 = d.2 → e = d) :
    H.card + M.card ≤ ∑ S ∈ F, (S.card + 1) := by
  classical
  have hH : H.card ≤ ∑ S ∈ F, S.card :=
    (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
  have hMcover : M ⊆ F.biUnion (fun S => M ∩ S) := by
    intro e he
    obtain ⟨S, hSF, heS⟩ := Finset.mem_biUnion.mp (hcover (hsub he))
    exact Finset.mem_biUnion.mpr ⟨S, hSF, Finset.mem_inter.mpr ⟨he, heS⟩⟩
  have hsmall : ∀ S ∈ F, (M ∩ S).card ≤ 1 := by
    intro S hSF
    apply Finset.card_le_one.mpr
    intro e he d hd
    obtain ⟨heM, heS⟩ := Finset.mem_inter.mp he
    obtain ⟨hdM, hdS⟩ := Finset.mem_inter.mp hd
    rcases hstar S hSF with ⟨p, hp⟩ | ⟨l, hl⟩
    · exact hrow e heM d hdM ((hp e heS).trans (hp d hdS).symm)
    · exact hcol e heM d hdM ((hl e heS).trans (hl d hdS).symm)
  have hM : M.card ≤ ∑ S ∈ F, (M ∩ S).card :=
    (Finset.card_le_card hMcover).trans (Finset.card_biUnion_le)
  calc
    H.card + M.card ≤ (∑ S ∈ F, S.card) + ∑ S ∈ F, (M ∩ S).card :=
      Nat.add_le_add hH hM
    _ = ∑ S ∈ F, (S.card + (M ∩ S).card) := by rw [Finset.sum_add_distrib]
    _ ≤ ∑ S ∈ F, (S.card + 1) := by
      exact Finset.sum_le_sum (fun S hSF => Nat.add_le_add_left (hsmall S hSF) S.card)

lemma star_cover_matching_card {n m : ℕ}
    (M : Finset (Fin n × Fin m))
    (F : Finset (Finset (Fin n × Fin m)))
    (hcover : M ⊆ F.biUnion id)
    (hstar : ∀ S ∈ F,
      (∃ p : Fin n, ∀ e ∈ S, e.1 = p) ∨
      (∃ l : Fin m, ∀ e ∈ S, e.2 = l))
    (hrow : ∀ e ∈ M, ∀ d ∈ M, e.1 = d.1 → e = d)
    (hcol : ∀ e ∈ M, ∀ d ∈ M, e.2 = d.2 → e = d) :
    M.card ≤ F.card := by
  classical
  have hMcover : M ⊆ F.biUnion (fun S => M ∩ S) := by
    intro e he
    obtain ⟨S, hSF, heS⟩ := Finset.mem_biUnion.mp (hcover he)
    exact Finset.mem_biUnion.mpr ⟨S, hSF, Finset.mem_inter.mpr ⟨he, heS⟩⟩
  have hsmall : ∀ S ∈ F, (M ∩ S).card ≤ 1 := by
    intro S hSF
    apply Finset.card_le_one.mpr
    intro e he d hd
    obtain ⟨heM, heS⟩ := Finset.mem_inter.mp he
    obtain ⟨hdM, hdS⟩ := Finset.mem_inter.mp hd
    rcases hstar S hSF with ⟨p, hp⟩ | ⟨l, hl⟩
    · exact hrow e heM d hdM ((hp e heS).trans (hp d hdS).symm)
    · exact hcol e heM d hdM ((hl e heS).trans (hl d hdS).symm)
  calc
    M.card ≤ (F.biUnion (fun S => M ∩ S)).card := Finset.card_le_card hMcover
    _ ≤ ∑ S ∈ F, (M ∩ S).card := Finset.card_biUnion_le
    _ ≤ ∑ S ∈ F, 1 := Finset.sum_le_sum hsmall
    _ = F.card := by simp

lemma castAdd_ne_natAdd {n m : ℕ} (p : Fin n) (l : Fin m) :
    Fin.castAdd m p ≠ Fin.natAdd n l := by
  intro h
  have hval := congrArg Fin.val h
  change p.val = n + l.val at hval
  have hle : n ≤ p.val := by rw [hval]; exact Nat.le_add_right n l.val
  exact Nat.not_le_of_gt p.isLt hle

lemma pair_input_left {n m : ℕ} (e : Fin n × Fin m) (p : Fin n)
    (h : decide (Fin.castAdd m p = Fin.castAdd m e.1 ∨
      Fin.castAdd m p = Fin.natAdd n e.2) = true) : p = e.1 := by
  rcases of_decide_eq_true h with h | h
  · exact Fin.ext (congrArg (fun i : Fin (n + m) => i.val) h)
  · exact (castAdd_ne_natAdd p e.2 h).elim

lemma pair_input_right {n m : ℕ} (e : Fin n × Fin m) (l : Fin m)
    (h : decide (Fin.natAdd n l = Fin.castAdd m e.1 ∨
      Fin.natAdd n l = Fin.natAdd n e.2) = true) : l = e.2 := by
  rcases of_decide_eq_true h with h | h
  · exact (castAdd_ne_natAdd e.1 l h.symm).elim
  · exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

lemma meet_closed_safe_accepts_one_edge {n m : ℕ}
    (E : Finset (Fin n × Fin m)) (R : (Fin (n + m) → Bool) → Prop)
    (hmeet : ∀ x y, R x → R y → R (fun i => x i && y i))
    (hsafe : ∀ x, R x → ∃ p l, (p, l) ∈ E ∧
      x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)
    (e d : Fin n × Fin m)
    (he : R (fun i => decide (i = Fin.castAdd m e.1 ∨ i = Fin.natAdd n e.2)))
    (hd : R (fun i => decide (i = Fin.castAdd m d.1 ∨ i = Fin.natAdd n d.2))) :
    e = d := by
  obtain ⟨p, l, _, hp, hl⟩ := hsafe _ (hmeet _ _ he hd)
  obtain ⟨hpe, hpd⟩ := Bool.and_eq_true_iff.mp hp
  obtain ⟨hle, hld⟩ := Bool.and_eq_true_iff.mp hl
  exact Prod.ext ((pair_input_left e p hpe).symm.trans (pair_input_left d p hpd))
    ((pair_input_right e l hle).symm.trans (pair_input_right d l hld))

lemma meet_closed_safe_family_edge_bound {n m : ℕ} {ι : Type*} [DecidableEq ι]
    (E H : Finset (Fin n × Fin m)) (T : Finset ι)
    (R : ι → (Fin (n + m) → Bool) → Prop)
    (hmeet : ∀ t ∈ T, ∀ x y, R t x → R t y → R t (fun i => x i && y i))
    (hsafe : ∀ t ∈ T, ∀ x, R t x → ∃ p l, (p, l) ∈ E ∧
      x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)
    (hcover : ∀ e ∈ H, ∃ t ∈ T,
      R t (fun i => decide (i = Fin.castAdd m e.1 ∨ i = Fin.natAdd n e.2))) :
    H.card ≤ T.card := by
  classical
  let S : ι → Finset (Fin n × Fin m) := fun t => H.filter
    (fun e => R t (fun i => decide (i = Fin.castAdd m e.1 ∨ i = Fin.natAdd n e.2)))
  have hsub : H ⊆ T.biUnion S := by
    intro e he
    obtain ⟨t, ht, het⟩ := hcover e he
    exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_filter.mpr ⟨he, het⟩⟩
  have hcard : ∀ t ∈ T, (S t).card ≤ 1 := by
    intro t ht
    apply Finset.card_le_one.mpr
    intro e he d hd
    exact meet_closed_safe_accepts_one_edge E (R t) (hmeet t ht) (hsafe t ht) e d
      (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hd).2
  calc
    H.card ≤ (T.biUnion S).card := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ T, (S t).card := Finset.card_biUnion_le
    _ ≤ ∑ t ∈ T, 1 := Finset.sum_le_sum hcard
    _ = T.card := by simp

end PEqualNP.Outside.L_meta_5324_aux
