namespace PEqualNP.Outside.L_meta_6659_aux

theorem equality_cf_main_many {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (b : Fin 14 → ℕ)
    (hb : PureBranch 14 D b) {c : Fin 14} {l : List ℕ} (hgood : cf_good c l)
    (hc : c ∈ eligSet 14 D) (X : Finset (Fin 14))
    (hX : ∀ x ∈ X, x ∈ eligSet 14 D ∧ x ≠ c ∧
      (∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → c ∈ supp 14 D u.1) ∧
      ∃ w, x ∈ supp 14 D w ∧ c ∈ supp 14 D w) :
    ∃ E : Dag, StrictLive 10 E ∧ sem_Comp 10 k4_Adj E ∧
      totalSurplus 10 E + ((ru D b c).card + X.card + 1) ≤ totalSurplus 14 D ∧
      Bplus 10 E + ((ru D b c).card + X.card + 1) ≤ totalSurplus 14 D ∧
      (∀ i : Fin 10, (∀ w, Relation.ReflTransGen (sem_step 14 D) (cf_iota l i).val w →
        fanout D w ≤ 1) → i ∈ ineligSet 10 E) ∧
      ∀ J : Finset (Fin 10),
        (∀ i ∈ J, i ∈ ineligSet 10 E ∧ cf_iota l i ∈ eligSet 14 D ∧
          cf_iota l i ≠ c ∧ cf_iota l i ∉ X) →
        totalSurplus 10 E + ((ru D b c).card + X.card + 1) + J.card ≤ totalSurplus 14 D := by
  classical
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  have hS := h.1
  obtain ⟨hinj, hfree, hiso⟩ := hgood
  have hok : cof_Ok (cf_rho c) (cf_iota l) := ⟨fun a b hab => hinj a b hab, hfree⟩
  have hρc : cf_rho c c = some true := by simp [cf_rho]
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
  obtain ⟨E, hE, hCE, hsur, hsurP, hprot, hslack⟩ := equality_cof_restrict_graph_many hS hok hC
    (fun _ _ huv => adj_symm huv) hT (by rw [heq]; exact k4_gr) (by norm_num)
  have hbel : ∀ x ∈ eligSet 14 D, (⟨b x, 0⟩ : Σ _ : ℕ, ℕ) ∈ units 14 D := fun x hx =>
    mem_units.2 ⟨sb_mem_inner.2 (lt_of_fanout_pos hS (w := b x) (by
      have := (hb x hx).1; omega)), by
      show 0 + 1 < fanout D (b x); have := (hb x hx).1; omega⟩
  have hel : ∀ x ∈ insert c X, x ∈ eligSet 14 D := fun x hx => by
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hc
    · exact (hX x hx).1
  have hS2inj : Set.InjOn (fun x => (⟨b x, 0⟩ : Σ _ : ℕ, ℕ))
      (insert c X : Finset (Fin 14)) := by
    intro x hx y hy hxy
    have h1 : b x = b y := congrArg Sigma.fst hxy
    have h2 := (hb x (hel x hx)).2
    rw [h1, (hb y (hel y hy)).2] at h2
    exact (Finset.singleton_injective h2).symm
  have hdis : Disjoint (ru D b c)
      ((insert c X).image (fun x => (⟨b x, 0⟩ : Σ _ : ℕ, ℕ))) := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu2
    exact (Finset.mem_sdiff.1 (mem_ru.1 hu1).1).2 (Finset.mem_image.2 ⟨x, hel x hx, rfl⟩)
  have hsub : ru D b c ∪ (insert c X).image (fun x => (⟨b x, 0⟩ : Σ _ : ℕ, ℕ)) ⊆
      units 14 D := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · exact (Finset.mem_filter.1 (Finset.mem_sdiff.1 (mem_ru.1 hu).1).1).1
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
      exact hbel x (hel x hx)
  have hlost : ∀ u ∈ ru D b c ∪ (insert c X).image (fun x => (⟨b x, 0⟩ : Σ _ : ℕ, ℕ)),
      u ∉ cof_kept D (cf_rho c) (cf_iota l) := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · exact cof_lost_of_true hS hρc (mem_ru.1 hu).2
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact cof_lost_of_true hS hρc (by
          show x ∈ supp 14 D (b x)
          rw [(hb x hc).2]; exact Finset.mem_singleton_self x)
      · obtain ⟨hxe, hxc, hres, w, hw⟩ := hX x hx
        obtain ⟨z, hxz, hcz⟩ := hG.2.2.1 x c hxc
        obtain ⟨hs1, -, -, e, he, -, hec⟩ :=
          sem_diff_two_exits hG h hC b hb hxc hxe hres hw hxz hcz
        have hbx : b x ∈ carrierDiff 14 D x c := sem_mem_diff.2 (by
          rw [(hb x hxe).2]
          exact ⟨Finset.mem_singleton_self x,
            fun hcx => hxc (Finset.mem_singleton.1 hcx).symm⟩)
        exact cof_lost_of_deg (cof_diff_deplete hS hρc hbx (hb x hxe).1 hs1 he hec)
  have hcard : (ru D b c ∪ (insert c X).image (fun x => (⟨b x, 0⟩ : Σ _ : ℕ, ℕ))).card =
      (ru D b c).card + X.card + 1 := by
    rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injOn hS2inj,
      Finset.card_insert_of_notMem (fun hcX => (hX c hcX).2.1 rfl)]
    omega
  have h1 := cof_sur_add_lost _ hsub hlost
  have h2 := cof_surP_add_lost _ hsub (fun u hu hk => hlost u hu (cof_keptP_sub hk))
  rw [hcard] at h1 h2
  refine ⟨E, hE, heq ▸ hCE, by omega, by omega, hprot, ?_⟩
  intro J hJ
  let U := J.image (fun i => (⟨b (cf_iota l i),0⟩ : Σ _ : ℕ, ℕ))
  let K := U.filter (fun u => u ∈ cof_kept D (cf_rho c) (cf_iota l))
  let L := ru D b c ∪ (insert c X).image (fun y => (⟨b y,0⟩ : Σ _ : ℕ, ℕ))
  have hUunit : U ⊆ units 14 D := by
    intro u hu
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    exact hbel _ (hJ i hi).2.1
  have hUdisL : Disjoint U L := by
    rw [Finset.disjoint_left]
    intro u hu hL
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    let x := cf_iota l i
    have hx := (hJ i hi).2.1
    rcases Finset.mem_union.mp hL with hres | himage
    · exact (Finset.mem_sdiff.mp (mem_ru.mp hres).1).2 (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    · obtain ⟨y,hy,heq⟩ := Finset.mem_image.mp himage
      have hby : b y = b x := congrArg Sigma.fst heq
      have hs := (hb y (hel y hy)).2
      rw [hby,(hb x hx).2] at hs
      have hyx : y = x := Finset.singleton_injective hs.symm
      subst y
      rcases Finset.mem_insert.mp hy with hc' | hxX
      · exact (hJ i hi).2.2.1 hc'
      · exact (hJ i hi).2.2.2 hxX
  have hKU : K ⊆ U := Finset.filter_subset _ _
  have hKkept : K ⊆ cof_kept D (cf_rho c) (cf_iota l) := fun u hu =>
    (Finset.mem_filter.mp hu).2
  have hfst : Set.InjOn (fun u : Σ _ : ℕ, ℕ => u.1) (U : Set _) := by
    intro u hu v hv heq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
    change b (cf_iota l i) = b (cf_iota l j) at heq
    simp only [heq]
  have hKbad : ∀ u ∈ K, ∃ i ∈ cof_supp D (cf_rho c) (cf_iota l) u.1,
      i ∈ ineligSet 10 E := by
    intro u hu
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp (hKU hu)
    refine ⟨i,?_,(hJ i hi).1⟩
    apply cof_mem_supp.mpr
    apply sem_val_of_supp hS (u := cf_iota l i)
    · rw [(hb _ (hJ i hi).2.1).2]
      exact Finset.mem_singleton_self _
    · rw [cof_ext_free hok]
      simp [single]
  have hs := hslack K hKkept (hfst.mono hKU) hKbad
  have hVlost : ∀ u ∈ U \ K, u ∉ cof_kept D (cf_rho c) (cf_iota l) := by
    intro u hu hk
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hu).1,hk⟩)
  have hLsub : L ∪ (U \ K) ⊆ units 14 D := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact hsub hu
    · exact hUunit (Finset.mem_sdiff.mp hu).1
  have hLlost : ∀ u ∈ L ∪ (U \ K), u ∉ cof_kept D (cf_rho c) (cf_iota l) := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact hlost u hu
    · exact hVlost u hu
  have hl := cof_sur_add_lost (L ∪ (U \ K)) hLsub hLlost
  have hd : Disjoint L (U \ K) := hUdisL.symm.mono_right Finset.sdiff_subset
  rw [Finset.card_union_of_disjoint hd] at hl
  have hLc : L.card = (ru D b c).card + X.card + 1 := hcard
  have hpart := Finset.card_sdiff_add_card_eq_card hKU
  have hUinj : Set.InjOn (fun i => (⟨b (cf_iota l i),0⟩ : Σ _ : ℕ, ℕ)) (J : Set _) := by
    intro i hi j hj heq
    have hbij : b (cf_iota l i) = b (cf_iota l j) := congrArg Sigma.fst heq
    have hiS := (hb _ (hJ i hi).2.1).2
    rw [hbij,(hb _ (hJ j hj).2.1).2] at hiS
    exact hinj i j (Finset.singleton_injective hiS).symm
  have hUc : U.card = J.card := Finset.card_image_of_injOn hUinj
  omega

end PEqualNP.Outside.L_meta_6659_aux
