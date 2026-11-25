namespace PEqualNP.Outside.L_meta_6659_aux
section CofProtectedRestrict
variable {n m : ℕ} {D : Dag} {ρ : Fin n → Option Bool} {ι : Fin m → Fin n}

theorem equality_cof_restrict_protected_many (hS : Strict n D) (hok : cof_Ok ρ ι) (hm : 2 ≤ m)
    (hess : ∀ i : Fin m, ∃ y y' : Fin m → Bool, (∀ k, k ≠ i → y k = y' k) ∧
      val D (cof_ext ρ ι y) (outW n D) ≠ val D (cof_ext ρ ι y') (outW n D)) :
    ∃ E : Dag, StrictLive m E ∧
      (∀ y, val E y (outW m E) = val D (cof_ext ρ ι y) (outW n D)) ∧
      totalSurplus m E ≤ cof_sur D ρ ι ∧ Bplus m E ≤ cof_surP D ρ ι ∧
      (∀ i : Fin m, (∀ w, Relation.ReflTransGen (sem_step n D) (ι i).val w → fanout D w ≤ 1) →
        i ∈ ineligSet m E) ∧
      (∀ i : Fin m, (∀ w, Relation.ReflTransGen (sem_step n D) (ι i).val w → fanout D w ≤ 1) →
        ∀ e, Relation.ReflTransGen (sem_step m E) i.val e → fanout E e ≤ 1) ∧
      ∀ U : Finset (Σ _ : ℕ, ℕ), U ⊆ cof_kept D ρ ι → Set.InjOn (fun u : Σ _ : ℕ, ℕ => u.1) (U : Set _) →
        (∀ u ∈ U, ∃ i ∈ cof_supp D ρ ι u.1, i ∈ ineligSet m E) →
        totalSurplus m E + U.card ≤ cof_sur D ρ ι := by
  classical
  obtain ⟨E, t, q, hI⟩ := cof_inv_all hS hok
  have hfree : ∀ i : Fin m, cof_live D ρ ι (ι i).val :=
    fun i => cof_live_free hS hok i (hess i)
  have hlo : cof_live D ρ ι (outW n D) := by
    obtain ⟨y, y', -, hne⟩ := hess ⟨0, by omega⟩
    exact ⟨fun hc => hne (hc y y'), Relation.ReflTransGen.refl⟩
  have hout := cof_tr_out hI hfree (by omega) hlo
  obtain ⟨-, hvout⟩ := hI.2.1 _ (cof_live_lt hlo) hlo
  rw [hout] at hvout
  have hne : E ≠ [] := by
    rintro rfl
    obtain ⟨y, y', hyy, hne⟩ := hess ⟨0, by omega⟩
    apply hne
    have h1 : outW m ([] : Dag) = m - 1 := by simp [outW]
    rw [← hvout y, ← hvout y', h1, val_input [] y (m - 1) (by omega),
      val_input [] y' (m - 1) (by omega)]
    exact hyy _ (fun hc => by have := congrArg Fin.val hc; simp at this; omega)
  refine ⟨E, ⟨hI.1, cof_tr_live hI hfree (by omega) hlo, hne⟩, hvout, ?_, ?_, ?_, ?_, ?_⟩
  · unfold totalSurplus cof_sur
    refine (cof_core hS hok hI hout (inner m E) (Finset.Subset.refl _)).trans
      (Finset.sum_le_sum_of_subset (fun w hw => ?_))
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨hw.1, hw.2.1⟩
  · unfold Bplus cof_surP
    refine (cof_core hS hok hI hout _ (Finset.filter_subset _ _)).trans
      (Finset.sum_le_sum_of_subset (fun w hw => ?_))
    rw [Finset.mem_filter] at hw ⊢
    obtain ⟨hw1, lw, htw⟩ := hw
    have hs : supp m E (t w) = cof_supp D ρ ι w := by
      ext i
      rw [mem_supp, cof_mem_supp, (hI.2.1 w (cof_live_lt lw) lw).2]
    exact ⟨hw1, lw, by rw [← hs]; exact (Finset.mem_filter.mp htw).2⟩
  · intro i0 hprot
    rw [mem_ineligSet]
    intro e he
    have hb := cof_fib_bound hS hok hI e
    have hle : ∑ w ∈ cof_fib D ρ ι t e, cof_deg D ρ ι w ≤ (cof_fib D ρ ι t e).card := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_le_sum (fun w hw => ?_)
      rw [cof_fib, Finset.mem_filter] at hw
      obtain ⟨-, lw, hwe⟩ := hw
      refine (cof_deg_le w).trans (hprot w ?_)
      have hv := (hI.2.1 w (cof_live_lt lw) lw).2
      rw [← hwe] at he
      have hne : val D (cof_ext ρ ι (single i0)) w ≠ val D (cof_ext ρ ι (fun _ => false)) w := by
        rw [← hv, ← hv, mem_supp.mp he, val_zero hI.1]
        simp
      exact sem_rtg_mono (fun a b h => h.1) (sem_changed_path hS _ _ (ι i0)
        (cof_ext_agree hok (fun k hk => by simp [single, hk])) w hne)
    omega

  · exact fun i hprot => equality_cof_preserves_protection hS hok hI i hprot

  · intro U hU hinj hbad
    exact equality_cof_slack_units hS hok hI hout U hU hinj hbad

theorem equality_cof_restrict_graph_protected_many {G : Fin n → Fin n → Prop} (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hC : sem_Comp n G D) (hsym : ∀ u v, G u v → G v u)
    (hT : ∀ c a, ρ c = some true → G c a → ρ a = some false)
    (hG' : sem_Gr (fun u v : Fin m => G (ι u) (ι v))) (hm : 0 < m) :
    ∃ E : Dag, StrictLive m E ∧ sem_Comp m (fun u v : Fin m => G (ι u) (ι v)) E ∧
      totalSurplus m E ≤ cof_sur D ρ ι ∧ Bplus m E ≤ cof_surP D ρ ι ∧
      (∀ i : Fin m, (∀ w, Relation.ReflTransGen (sem_step n D) (ι i).val w → fanout D w ≤ 1) →
        i ∈ ineligSet m E) ∧
      (∀ i : Fin m, (∀ w, Relation.ReflTransGen (sem_step n D) (ι i).val w → fanout D w ≤ 1) →
        ∀ e, Relation.ReflTransGen (sem_step m E) i.val e → fanout E e ≤ 1) ∧
      ∀ U : Finset (Σ _ : ℕ, ℕ), U ⊆ cof_kept D ρ ι → Set.InjOn (fun u : Σ _ : ℕ, ℕ => u.1) (U : Set _) →
        (∀ u ∈ U, ∃ i ∈ cof_supp D ρ ι u.1, i ∈ ineligSet m E) →
        totalSurplus m E + U.card ≤ cof_sur D ρ ι := by
  classical
  have hval : ∀ y, val D (cof_ext ρ ι y) (outW n D) = true ↔
      sem_Edge (fun u v : Fin m => G (ι u) (ι v)) y :=
    fun y => (hC _).trans (cof_edge hok hsym hT y)
  have hm2 : 2 ≤ m := by
    obtain ⟨a, -, hne⟩ := hG'.2.2.2 ⟨0, hm⟩ ⟨0, hm⟩
    by_contra hc
    exact hne (Fin.ext (by have := a.isLt; show a.val = 0; omega))
  have hess : ∀ i : Fin m, ∃ y y' : Fin m → Bool, (∀ k, k ≠ i → y k = y' k) ∧
      val D (cof_ext ρ ι y) (outW n D) ≠ val D (cof_ext ρ ι y') (outW n D) := by
    intro i
    obtain ⟨a, ha, -⟩ := hG'.2.2.2 i i
    refine ⟨single a, sem_ins i (single a), sem_ins_agree i _, fun heq => ?_⟩
    have h1 : sem_Edge (fun u v : Fin m => G (ι u) (ι v)) (sem_ins i (single a)) :=
      ⟨i, a, ha, sem_ins_self i _, by simp [sem_ins, single]⟩
    have h2 := (hval _).mpr h1
    rw [← heq] at h2
    exact sem_single_no_edge hG' a ((hval _).mp h2)
  obtain ⟨E, h1, h2, h3, h4, h5, h6, h7⟩ := equality_cof_restrict_protected_many hS hok hm2 hess
  exact ⟨E, h1, fun y => by rw [h2 y]; exact hval y, h3, h4, h5, h6, h7⟩

end CofProtectedRestrict
end PEqualNP.Outside.L_meta_6659_aux
