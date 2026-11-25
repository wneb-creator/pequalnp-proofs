namespace PEqualNP.Outside.L_meta_6659_aux

theorem equality_cf_supported_eight {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {c : Fin 14} {l : List ℕ} (hgood : cf_good c l)
    (hp5 : ∀ w, Relation.ReflTransGen (sem_step 14 D) (cf_iota l (5 : Fin 10)).val w →
      fanout D w ≤ 1)
    (hp8 : ∀ w, Relation.ReflTransGen (sem_step 14 D) (cf_iota l (8 : Fin 10)).val w →
      fanout D w ≤ 1) :
    8 ≤ cof_surP D (cf_rho c) (cf_iota l) := by
  classical
  have hC := sem_heawood_comp hD
  have hS := h.1
  obtain ⟨hinj, hfree, hiso⟩ := hgood
  have hok : cof_Ok (cf_rho c) (cf_iota l) := ⟨fun a b hab => hinj a b hab, hfree⟩
  have hT : ∀ d a : Fin 14, cf_rho c d = some true → HG d a → cf_rho c a = some false := by
    intro d a h1 h2
    have hd : d = c := by
      by_contra hne
      unfold cf_rho at h1
      simp only [hne, ite_false] at h1
      split at h1 <;> simp at h1
    subst hd
    have hne : a ≠ d := fun hac => adj_irrefl d (hac ▸ h2)
    simp [cf_rho, hne, (hc_adjB_iff d a).2 h2]
  have heq : (fun u v : Fin 10 => HG (cf_iota l u) (cf_iota l v)) = k4_Adj := by
    funext u v
    exact propext (by
      show Adj _ _ ↔ k4_adjB u v = true
      rw [← hiso u v]; exact (hc_adjB_iff _ _).symm)
  obtain ⟨E,hE,hCE,_,hB,hprot,hfull,_⟩ := equality_cof_restrict_graph_protected_many
    hS hok hC (fun _ _ huv => adj_symm huv) hT (by rw [heq]; exact k4_gr) (by norm_num)
  have hK : sem_Comp 10 k4_Adj E := heq ▸ hCE
  have eight := ke_protected_matching_supported_lower hE hK
    (hprot 5 hp5) (hprot 8 hp8) (hfull 5 hp5)
  exact eight.trans hB

end PEqualNP.Outside.L_meta_6659_aux
