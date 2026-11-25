import PNPHighCofactor
import PNPK4Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PEqualNP.Outside.L_meta_6659_aux

section CofMulti
variable {n m : ℕ} {D : Dag} {ρ : Fin n → Option Bool} {ι : Fin m → Fin n}

theorem equality_cof_slack_set {E : Dag} {t q : ℕ → ℕ}
    (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hI : cof_Inv D ρ ι D.length E t q)
    (hout : t (outW n D) = outW m E)
    (V : Finset ℕ)
    (hV : ∀ w ∈ V, w ∈ inner n D ∧ cof_live D ρ ι w ∧
      2 ≤ cof_deg D ρ ι w ∧ fanout E (t w) ≤ 1) :
    totalSurplus m E + V.card ≤ cof_sur D ρ ι := by
  classical
  let T := (inner m E).filter (fun e => 2 ≤ fanout E e)
  let S := (inner n D).filter (fun w => cof_live D ρ ι w)
  let A := (inner n D).filter (fun w => cof_live D ρ ι w ∧ t w ∈ T)
  have hT : T ⊆ inner m E := Finset.filter_subset _ _
  have htotal : totalSurplus m E = surplusOn E T := by
    symm
    apply Finset.sum_subset hT
    intro e he hnot
    have hf : ¬ 2 ≤ fanout E e := by
      intro hf
      exact hnot (Finset.mem_filter.mpr ⟨he,hf⟩)
    omega
  have hVS : V ⊆ S := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨(hV w hw).1,(hV w hw).2.1⟩
  have hAS : A ⊆ S \ V := by
    intro w hw
    obtain ⟨hwinner,hwlive,hwt⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hwinner,hwlive⟩,?_⟩
    intro hwV
    have h1 := (hV w hwV).2.2.2
    have h2 := (Finset.mem_filter.mp hwt).2
    omega
  have hcore := cof_core hS hok hI hout T hT
  have hsum : (∑ w ∈ A, (cof_deg D ρ ι w - 1)) ≤
      ∑ w ∈ S \ V, (cof_deg D ρ ι w - 1) := Finset.sum_le_sum_of_subset hAS
  have hcard : V.card ≤ ∑ w ∈ V, (cof_deg D ρ ι w - 1) := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro w hw
    have := (hV w hw).2.2.1
    omega
  have hsplit := Finset.sum_sdiff (f := fun w => cof_deg D ρ ι w - 1) hVS
  change surplusOn E T ≤ ∑ w ∈ A, (cof_deg D ρ ι w - 1) at hcore
  change (∑ w ∈ S \ V, (cof_deg D ρ ι w - 1)) +
      (∑ w ∈ V, (cof_deg D ρ ι w - 1)) = cof_sur D ρ ι at hsplit
  omega

theorem equality_cof_slack_units {E : Dag} {t q : ℕ → ℕ}
    (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hI : cof_Inv D ρ ι D.length E t q)
    (hout : t (outW n D) = outW m E)
    (U : Finset (Σ _ : ℕ, ℕ)) (hU : U ⊆ cof_kept D ρ ι)
    (hinj : Set.InjOn (fun u : Σ _ : ℕ, ℕ => u.1) (U : Set _))
    (hbad : ∀ u ∈ U, ∃ i ∈ cof_supp D ρ ι u.1, i ∈ ineligSet m E) :
    totalSurplus m E + U.card ≤ cof_sur D ρ ι := by
  classical
  have hc := Finset.card_image_of_injOn hinj
  rw [← hc]
  apply equality_cof_slack_set hS hok hI hout
  intro w hw
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hunit,hlive,hdeg⟩ := cof_mem_kept.mp (hU hu)
  obtain ⟨i,hisupp,hi⟩ := hbad u hu
  refine ⟨(mem_units.mp hunit).1,hlive,by omega,?_⟩
  apply (mem_ineligSet.mp hi) (t u.1)
  rw [mem_supp, (hI.2.1 u.1 (cof_live_lt hlive) hlive).2]
  exact cof_mem_supp.mp hisupp

end CofMulti
end PEqualNP.Outside.L_meta_6659_aux
namespace PEqualNP.Outside.L_meta_6659_aux
section CofManyRestrict
variable {n m : ℕ} {D : Dag} {ρ : Fin n → Option Bool} {ι : Fin m → Fin n}

theorem equality_cof_restrict_many (hS : Strict n D) (hok : cof_Ok ρ ι) (hm : 2 ≤ m)
    (hess : ∀ i : Fin m, ∃ y y' : Fin m → Bool, (∀ k, k ≠ i → y k = y' k) ∧
      val D (cof_ext ρ ι y) (outW n D) ≠ val D (cof_ext ρ ι y') (outW n D)) :
    ∃ E : Dag, StrictLive m E ∧
      (∀ y, val E y (outW m E) = val D (cof_ext ρ ι y) (outW n D)) ∧
      totalSurplus m E ≤ cof_sur D ρ ι ∧ Bplus m E ≤ cof_surP D ρ ι ∧
      (∀ i : Fin m, (∀ w, Relation.ReflTransGen (sem_step n D) (ι i).val w → fanout D w ≤ 1) →
        i ∈ ineligSet m E) ∧
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
  refine ⟨E, ⟨hI.1, cof_tr_live hI hfree (by omega) hlo, hne⟩, hvout, ?_, ?_, ?_, ?_⟩
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

  · intro U hU hinj hbad
    exact equality_cof_slack_units hS hok hI hout U hU hinj hbad

theorem equality_cof_restrict_graph_many {G : Fin n → Fin n → Prop} (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hC : sem_Comp n G D) (hsym : ∀ u v, G u v → G v u)
    (hT : ∀ c a, ρ c = some true → G c a → ρ a = some false)
    (hG' : sem_Gr (fun u v : Fin m => G (ι u) (ι v))) (hm : 0 < m) :
    ∃ E : Dag, StrictLive m E ∧ sem_Comp m (fun u v : Fin m => G (ι u) (ι v)) E ∧
      totalSurplus m E ≤ cof_sur D ρ ι ∧ Bplus m E ≤ cof_surP D ρ ι ∧
      (∀ i : Fin m, (∀ w, Relation.ReflTransGen (sem_step n D) (ι i).val w → fanout D w ≤ 1) →
        i ∈ ineligSet m E) ∧
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
  obtain ⟨E, h1, h2, h3, h4, h5, h6⟩ := equality_cof_restrict_many hS hok hm2 hess
  exact ⟨E, h1, fun y => by rw [h2 y]; exact hval y, h3, h4, h5, h6⟩

end CofManyRestrict
end PEqualNP.Outside.L_meta_6659_aux
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
namespace PEqualNP.Outside.L_meta_6659_aux

theorem ke_embedding_three (R : Finset (Σ _ : ℕ, ℕ)) (hR : R.card ≤ 3) :
    ∃ f : (Σ _ : ℕ, ℕ) → Fin 3, Set.InjOn f (R : Set _) := by
  classical
  let e : (↑R) ≃ Fin R.card := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe])
  let f : (Σ _ : ℕ, ℕ) → Fin 3 := fun u => if hu : u ∈ R then
    ⟨(e ⟨u,hu⟩).val,lt_of_lt_of_le (e ⟨u,hu⟩).isLt hR⟩ else 0
  refine ⟨f,?_⟩
  intro u hu v hv equal
  change u ∈ R at hu
  change v ∈ R at hv
  have fu : f u = ⟨(e ⟨u,hu⟩).val,lt_of_lt_of_le (e ⟨u,hu⟩).isLt hR⟩ := by simp [f,hu]
  have fv : f v = ⟨(e ⟨v,hv⟩).val,lt_of_lt_of_le (e ⟨v,hv⟩).isLt hR⟩ := by simp [f,hv]
  have val := congrArg Fin.val (fu.symm.trans (equal.trans fv))
  exact congrArg Subtype.val (e.injective (Fin.ext val))

theorem ke_assigned_bound {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (b : Fin 10 → ℕ) (hb : PureBranch 10 D b) (pos : Fin 10 → ℕ × Bool)
    (hpos : k4_Pos 10 k4_Adj D pos) (J : Finset (Fin 6)) {t : Fin 10}
    (hJ : ∀ i ∈ J, Fin.natAdd 4 i ∈ ineligSet 10 D ∧
      t ∈ supp 10 D (src D (pos (Fin.natAdd 4 i)))) :
    J.card ≤ 2 + ((residualUnits 10 D b).filter (fun u => t ∈ supp 10 D u.1)).card := by
  classical
  have hinj : Set.InjOn (fun i : Fin 6 => pos (Fin.natAdd 4 i)) (J : Set _) := by
    intro i hi j hj equal
    have he := hpos.2 _ (hJ i hi).1 _ (hJ j hj).1 equal
    apply Fin.ext
    have hv := congrArg Fin.val he
    simpa using hv
  have sub : J.image (fun i => pos (Fin.natAdd 4 i)) ⊆ sem_W 10 D t := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
    exact sem_mem_W.mpr ⟨(hpos.1 _ (hJ i hi).1).1,(hJ i hi).2,by
      rw [(hpos.1 _ (hJ i hi).1).2.1]
      exact Finset.notMem_empty t⟩
  have lower := Finset.card_le_card sub
  rw [Finset.card_image_of_injOn hinj] at lower
  have upper := ke_cc_le h hD b hb t
  omega

theorem ke_coordinate_budget {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (b : Fin 10 → ℕ) (hb : PureBranch 10 D b) (pos : Fin 10 → ℕ × Bool)
    (hpos : k4_Pos 10 k4_Adj D pos) (hR : (residualUnits 10 D b).card ≤ 3)
    (hW : ∀ x : Fin 4, 3 ≤ (sem_W 10 D (Fin.castLE (by decide : 4 ≤ 10) x)).card)
    (J : Finset (Fin 6)) (hJ : ∀ i ∈ J, Fin.natAdd 4 i ∈ ineligSet 10 D) :
    ∃ M : Fin 4 → Finset (Fin 3),
      (∀ x, (M x).Nonempty) ∧ (Finset.univ.biUnion M).card ≤ (residualUnits 10 D b).card ∧
      ∀ t : Fin 4, (J.filter (fun i => ∃ x : Fin 4,
        k4_Adj (Fin.castLE (by decide : 4 ≤ 10) x) (Fin.natAdd 4 i) ∧ M x ⊆ M t)).card ≤
        2 + (M t).card := by
  classical
  let R := residualUnits 10 D b
  obtain ⟨f,hinj⟩ := ke_embedding_three R hR
  let A : Fin 4 → Finset (Σ _ : ℕ, ℕ) := fun x =>
    R.filter (fun u => (Fin.castLE (by decide : 4 ≤ 10) x) ∈ supp 10 D u.1)
  let M : Fin 4 → Finset (Fin 3) := fun x => (A x).image f
  have asub (x) : A x ⊆ R := Finset.filter_subset _ _
  have card (x) : (M x).card = (A x).card := Finset.card_image_of_injOn (hinj.mono (asub x))
  have positive (x) : (A x).Nonempty := by
    apply Finset.card_pos.mp
    have c := ke_cc_le h hD b hb (Fin.castLE (by decide : 4 ≤ 10) x)
    have w := hW x
    have hp : 0 < ((residualUnits 10 D b).filter
        (fun u => (Fin.castLE (by decide : 4 ≤ 10) x) ∈ supp 10 D u.1)).card := by omega
    exact hp
  refine ⟨M,fun x => (positive x).image f,?_,?_⟩
  · have sub : Finset.univ.biUnion M ⊆ R.image f := by
      intro y hy
      obtain ⟨x,_,hy⟩ := Finset.mem_biUnion.mp hy
      exact Finset.image_subset_image (asub x) hy
    have hc := Finset.card_le_card sub
    rw [Finset.card_image_of_injOn hinj] at hc
    exact hc
  · intro t
    rw [card t]
    apply ke_assigned_bound h hD b hb pos hpos
    intro i hi
    obtain ⟨hiJ,x,hxi,hsub⟩ := Finset.mem_filter.mp hi
    have hii := hJ i hiJ
    have inclusion : ∀ u ∈ R, (Fin.castLE (by decide : 4 ≤ 10) x) ∈ supp 10 D u.1 →
        (Fin.castLE (by decide : 4 ≤ 10) t) ∈ supp 10 D u.1 := by
      intro u hu hx
      have hm : f u ∈ M x := Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨hu,hx⟩,rfl⟩
      obtain ⟨v,hv,hvu⟩ := Finset.mem_image.mp (hsub hm)
      have vu : v = u := hinj (asub t hv) hu hvu
      exact vu ▸ (Finset.mem_filter.mp hv).2
    obtain ⟨u,hu⟩ := positive x
    obtain ⟨huR,hux⟩ := Finset.mem_filter.mp hu
    have hut := inclusion u huR hux
    refine ⟨hii,?_⟩
    exact ke_residual_co_label h hD b hb pos hpos (res_elig huR hux) (res_elig huR hut)
      hii (k4_gr.1 _ _ hxi) x.isLt t.isLt inclusion ⟨u.1,hux,hut⟩

end PEqualNP.Outside.L_meta_6659_aux
namespace PEqualNP.Outside.L_meta_6659_aux

theorem ke_low_cover_geometry : ∀ S : Finset (Fin 10),
    (∀ u v : Fin 10, k4_Adj u v → u ∈ S ∨ v ∈ S) → S.card ≤ 5 →
    S = {0,1,2,3} ∨ ∃ omitted : Fin 6, S = insert (Fin.natAdd 4 omitted) {0,1,2,3} := by
  decide +kernel

theorem ke_large_edge_family_many {D : Dag} (J : Finset (Fin 6)) (hJ : 5 ≤ J.card)
    (hin : ∀ i ∈ J, Fin.natAdd 4 i ∈ ineligSet 10 D) (x : Fin 4) :
    ke_many (ineligSet 10 D) (Fin.castLE (by decide : 4 ≤ 10) x) := by
  have geo : ∀ J : Finset (Fin 6), 5 ≤ J.card → ∀ x : Fin 4,
      ∃ i ∈ J, ∃ j ∈ J, i ≠ j ∧
        k4_Adj (Fin.natAdd 4 i) (Fin.castLE (by decide : 4 ≤ 10) x) ∧
        k4_Adj (Fin.natAdd 4 j) (Fin.castLE (by decide : 4 ≤ 10) x) := by decide +kernel
  obtain ⟨i,hi,j,hj,hij,hix,hjx⟩ := geo J hJ x
  apply Finset.one_lt_card.mpr
  refine ⟨Fin.natAdd 4 i,Finset.mem_filter.mpr ⟨hin i hi,hix⟩,
    Fin.natAdd 4 j,Finset.mem_filter.mpr ⟨hin j hj,hjx⟩,?_⟩
  intro equal
  apply hij
  apply Fin.ext
  have hv := congrArg Fin.val equal
  simpa using hv

theorem ke_low_elig_impossible {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (hB : totalSurplus 10 D ≤ 7) (hp : (eligSet 10 D).card ≤ 5) : False := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch k4_gr h.1 hD
  obtain ⟨pos,hpos⟩ := k4_assigned k4_gr h hD
  have cr := card_residual h.1 b hb
  have split := totalSurplus_split 10 D
  have cover : ∀ u v : Fin 10, k4_Adj u v → u ∈ eligSet 10 D ∨ v ∈ eligSet 10 D :=
    fun u v huv => sem_elig_cover k4_gr h hD huv
  rcases ke_low_cover_geometry (eligSet 10 D) cover hp with heq | ⟨omitted,heq⟩
  · have hp4 : (eligSet 10 D).card = 4 := by rw [heq]; decide
    have hR : (residualUnits 10 D b).card ≤ 3 := by omega
    have hin : ∀ i ∈ (Finset.univ : Finset (Fin 6)), Fin.natAdd 4 i ∈ ineligSet 10 D := by
      intro i _
      rw [sem_mem_inelig,heq]
      have geo : ∀ i : Fin 6, Fin.natAdd 4 i ∉ ({0,1,2,3} : Finset (Fin 10)) := by decide
      exact geo i
    have hw : ∀ x : Fin 4, 3 ≤ (sem_W 10 D (Fin.castLE (by decide : 4 ≤ 10) x)).card := by
      intro x
      exact ke_two_neighbors_three h hD pos hpos x.isLt
        (ke_large_edge_family_many Finset.univ (by decide) hin x)
    obtain ⟨M,hM,_,hbudget⟩ := ke_coordinate_budget h hD b hb pos hpos hR hw Finset.univ hin
    obtain ⟨t,ht⟩ := ke_p4_mask_certificate M hM
    have := hbudget t
    omega
  · have hp5 : (eligSet 10 D).card = 5 := by
      rw [heq]
      have geo : ∀ i : Fin 6, (insert (Fin.natAdd 4 i) ({0,1,2,3} : Finset (Fin 10))).card = 5 := by decide
      exact geo omitted
    have hR : (residualUnits 10 D b).card ≤ 2 := by omega
    let J := (Finset.univ : Finset (Fin 6)).erase omitted
    have hJ : J.card = 5 := by simp [J]
    have hin : ∀ i ∈ J, Fin.natAdd 4 i ∈ ineligSet 10 D := by
      intro i hi
      rw [sem_mem_inelig,heq]
      have ine := (Finset.mem_erase.mp hi).1
      have geo : ∀ o i : Fin 6, i ≠ o → Fin.natAdd 4 i ∉
          insert (Fin.natAdd 4 o) ({0,1,2,3} : Finset (Fin 10)) := by decide
      exact geo omitted i ine
    have hw : ∀ x : Fin 4, 3 ≤ (sem_W 10 D (Fin.castLE (by decide : 4 ≤ 10) x)).card := by
      intro x
      exact ke_two_neighbors_three h hD pos hpos x.isLt
        (ke_large_edge_family_many J (by omega) hin x)
    obtain ⟨M,hM,hunion,hbudget⟩ := ke_coordinate_budget h hD b hb pos hpos (by omega) hw J hin
    obtain ⟨t,ht⟩ := ke_p5_mask_certificate omitted M hM (by omega)
    have same : J.filter (fun i => ∃ x : Fin 4,
        k4_Adj (Fin.castLE (by decide : 4 ≤ 10) x) (Fin.natAdd 4 i) ∧ M x ⊆ M t) =
      Finset.univ.filter (fun i : Fin 6 => i ≠ omitted ∧ ∃ x : Fin 4,
        k4_Adj (Fin.castLE (by decide : 4 ≤ 10) x) (Fin.natAdd 4 i) ∧ M x ⊆ M t) := by
      ext i
      simp only [J,Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,true_and,and_true]
    have bound := hbudget t
    rw [same] at bound
    omega

theorem ke_at_most_two_originals {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (hB : totalSurplus 10 D ≤ 7) :
    (({0,1,2,3} : Finset (Fin 10)) ∩ eligSet 10 D).card ≤ 2 := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch k4_gr h.1 hD
  have hp := elig_le_Bplus h.1 b hb
  have split := totalSurplus_split 10 D
  by_cases small : (eligSet 10 D).card ≤ 5
  · exact False.elim (ke_low_elig_impossible h hD hB small)
  · by_cases six : (eligSet 10 D).card = 6
    · exact ke_p6_at_most_two h hD hB six
    · exact ke_p7_at_most_two h hD hB (by omega)

end PEqualNP.Outside.L_meta_6659_aux
namespace PEqualNP.Outside.L_meta_6659_aux

theorem equality_cf_nine_free {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) {c : Fin 14} {l : List ℕ}
    (hgood : cf_good c l) (hc : c ∈ eligSet 14 D) (X : Finset (Fin 14))
    (hX : ∀ x ∈ X, x ∈ eligSet 14 D ∧ x ≠ c ∧
      (∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → c ∈ supp 14 D u.1) ∧
      ∃ w, x ∈ supp 14 D w ∧ c ∈ supp 14 D w)
    (J : Finset (Fin 10)) (hJcard : 3 ≤ J.card)
    (hJ : ∀ i ∈ J, i.val < 4 ∧ cf_iota l i ∈ eligSet 14 D ∧
      cf_iota l i ≠ c ∧ cf_iota l i ∉ X) :
    (ru D b c).card + X.card + 9 ≤ totalSurplus 14 D := by
  classical
  obtain ⟨E,hE,hCE,hbound,_,_,hextra⟩ := equality_cf_main_many h hD b hb hgood hc X hX
  by_cases h6 : totalSurplus 10 E ≤ 6
  · have hel := k4_equality_eligible hE hCE h6
    have hin : ∀ i ∈ J, i ∈ ineligSet 10 E := by
      intro i hi
      apply sem_mem_inelig.mpr
      rw [hel]
      have hv := (hJ i hi).1
      fin_cases i <;> simp_all
    have hx := hextra J (fun i hi => ⟨hin i hi,(hJ i hi).2⟩)
    have hmin := k4_surplus_six hE hCE
    have hle := Bplus_le_total 10 E
    omega
  · by_cases h7 : totalSurplus 10 E ≤ 7
    · have htwo := ke_at_most_two_originals hE hCE h7
      have exists_ineligible : ∃ i ∈ J, i ∈ ineligSet 10 E := by
        by_contra hn
        have sub : J ⊆ ({0,1,2,3} : Finset (Fin 10)) ∩ eligSet 10 E := by
          intro i hi
          refine Finset.mem_inter.mpr ⟨?_,?_⟩
          · have hv := (hJ i hi).1
            fin_cases i <;> simp_all
          · by_contra hne
            exact hn ⟨i,hi,sem_mem_inelig.mpr hne⟩
        have card := Finset.card_le_card sub
        omega
      obtain ⟨i,hi,hin⟩ := exists_ineligible
      have hx := hextra {i} (by
        intro j hj
        have ji := Finset.mem_singleton.mp hj
        subst j
        exact ⟨hin,(hJ i hi).2⟩)
      rw [Finset.card_singleton] at hx
      omega
    · omega

end PEqualNP.Outside.L_meta_6659_aux
