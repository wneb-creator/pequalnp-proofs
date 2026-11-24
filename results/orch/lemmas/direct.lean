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

end PEqualNP.Outside.L_meta_5324_aux
