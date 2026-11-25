import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux.SixBirthCounting

lemma six_of_birth_shapes {α : Type} [DecidableEq α]
    (L : Nat → Finset α) (M : Finset Nat) (N : Fin 3 → Finset α) (j : Fin 3 → Nat)
    (hcard : ∀ i, (N i).card = 3)
    (hmeet : ∀ i k, i ≠ k → (N i ∩ N k).card ≤ 1)
    (hj : ∀ i, j i ∈ M) (hlabel : ∀ i, L (j i) = N i)
    (hshape : ∀ i,
      (∃ a ∈ M, L a ⊆ N i ∧ (L a).card = 2) ∨
      (∃ a ∈ M, ∃ b ∈ M, a ≠ b ∧ 4 ≤ (L a).card ∧ 4 ≤ (L b).card ∧
        L a ∩ L b = N i)) :
    6 ≤ M.card := by
  classical
  by_contra hsmall
  have hM : M.card ≤ 5 := by omega
  have hN : Function.Injective N := by
    intro i k he
    by_contra hne
    have hc := hmeet i k hne
    rw [← he, Finset.inter_self, hcard i] at hc
    omega
  have hji : Function.Injective j := by
    intro i k he
    apply hN
    calc
      N i = L (j i) := (hlabel i).symm
      _ = L (j k) := congrArg L he
      _ = N k := hlabel k
  let J : Finset Nat := Finset.univ.image j
  have hJcard : J.card = 3 := by
    dsimp [J]
    rw [Finset.card_image_of_injective _ hji]
    decide
  have hJsub : J ⊆ M := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hj i
  let A := M \ J
  have hAcard : A.card ≤ 2 := by
    have he := Finset.card_sdiff_add_card_eq_card hJsub
    change A.card + J.card = M.card at he
    omega
  have mem_aux (a : Nat) (ha : a ∈ M) (hc : (L a).card ≠ 3) : a ∈ A := by
    refine Finset.mem_sdiff.mpr ⟨ha, ?_⟩
    intro hJ
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hJ
    have hl : L a = N i := by simpa only [he] using hlabel i
    have hh := congrArg Finset.card hl
    rw [hcard i] at hh
    exact hc hh
  have shape_aux : ∀ i,
      (∃ a ∈ A, L a ⊆ N i ∧ (L a).card = 2) ∨
      (∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ 4 ≤ (L a).card ∧ 4 ≤ (L b).card ∧
        L a ∩ L b = N i) := by
    intro i
    rcases hshape i with ⟨a, ha, hs, hc⟩ | ⟨a, ha, b, hb, hab, hca, hcb, he⟩
    · exact Or.inl ⟨a, mem_aux a ha (by omega), hs, hc⟩
    · exact Or.inr ⟨a, mem_aux a ha (by omega), b, mem_aux b hb (by omega),
        hab, hca, hcb, he⟩
  by_cases hall : ∀ i, ∃ a ∈ A, L a ⊆ N i ∧ (L a).card = 2
  · choose aux haux hsub htwo using hall
    have hinj : Function.Injective aux := by
      intro i k he
      by_contra hne
      have hs : L (aux i) ⊆ N i ∩ N k := by
        intro x hx
        exact Finset.mem_inter.mpr ⟨hsub i hx,
          hsub k (by simpa only [he] using hx)⟩
      have hc := (Finset.card_le_card hs).trans (hmeet i k hne)
      rw [htwo i] at hc
      omega
    have hc : 3 ≤ A.card := by
      calc
        3 = (Finset.univ.image aux).card := by
          rw [Finset.card_image_of_injective _ hinj]
          decide
        _ ≤ A.card := Finset.card_le_card (by
          intro a ha
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
          exact haux i)
    omega
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    rcases shape_aux i with hor | ⟨a, ha, b, hb, hab, hca, hcb, hinter⟩
    · exact hi hor
    have hpair : ({a, b} : Finset Nat) ⊆ A := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    have hpaircard : A.card ≤ ({a, b} : Finset Nat).card := by
      rw [Finset.card_pair hab]
      exact hAcard
    have hAeq : A = {a, b} := (Finset.eq_of_subset_of_card_le hpair hpaircard).symm
    obtain ⟨k, hki⟩ : ∃ k : Fin 3, k ≠ i := exists_ne i
    rcases shape_aux k with ⟨c, hc, _, hcc⟩ | ⟨c, hc, d, hd, hcd, _, _, hinterk⟩
    · have he : c = a ∨ c = b := by simpa only [hAeq, Finset.mem_insert,
        Finset.mem_singleton] using hc
      rcases he with rfl | rfl <;> omega
    · have hc' : c = a ∨ c = b := by simpa only [hAeq, Finset.mem_insert,
        Finset.mem_singleton] using hc
      have hd' : d = a ∨ d = b := by simpa only [hAeq, Finset.mem_insert,
        Finset.mem_singleton] using hd
      have he : N k = N i := by
        rcases hc' with rfl | rfl <;> rcases hd' with rfl | rfl
        · exact (hcd rfl).elim
        · exact hinterk.symm.trans hinter
        · exact hinterk.symm.trans ((Finset.inter_comm _ _).trans hinter)
        · exact (hcd rfl).elim
      exact hki (hN he)

end PEqualNP.Outside.L_meta_2590_aux.SixBirthCounting
