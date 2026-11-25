import PNPNineFree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PEqualNP.Outside.L_meta_6659_aux

def equality_cof_rep {n m : ℕ} (ι : Fin m → Fin n) (q : ℕ → ℕ) (e : ℕ) : ℕ :=
  if he : e < m then (ι ⟨e,he⟩).val else n + q (e-m)

theorem equality_cof_rep_input {n m : ℕ} (ι : Fin m → Fin n) (q : ℕ → ℕ) (i : Fin m) :
    equality_cof_rep ι q i.val = (ι i).val := by
  simp [equality_cof_rep,i.isLt]

theorem equality_cof_rep_gate {n m : ℕ} (ι : Fin m → Fin n) (q : ℕ → ℕ) (j : ℕ) :
    equality_cof_rep ι q (m+j) = n + q j := by
  simp [equality_cof_rep]

theorem equality_cof_rep_reaches {n m : ℕ} {D E : Dag} {ρ : Fin n → Option Bool}
    {ι : Fin m → Fin n} {t q : ℕ → ℕ} (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hI : cof_Inv D ρ ι D.length E t q) {w : ℕ} (hw : cof_live D ρ ι w) :
    Relation.ReflTransGen (sem_step n D) (equality_cof_rep ι q (t w)) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases input : w < n
    · obtain ⟨i,rfl⟩ := cof_live_input hok input hw
      rw [hI.2.2.2.2 i,equality_cof_rep_input]
    · let j := w-n
      have wj : w = n+j := by omega
      have hj : j < D.length := by have := cof_live_lt hw; omega
      rw [wj] at hw ⊢
      rcases hI.2.2.2.1 j hj hw with ⟨i,hi,hqi⟩ | collapsed
      · have image := (hI.2.2.1 i hi).2.2.1
        rw [hqi] at image
        rw [image,equality_cof_rep_gate,hqi]
      · obtain ⟨s,hs⟩ := cof_live_op hS hj hw
        have lt : src D (j,s) < w := by
          rw [wj]
          cases s
          · simpa only [sb_src_false] using (hS j hj).1
          · simpa only [sb_src_true] using (hS j hj).2.1
        have path := ih (src D (j,s)) lt hs
        rw [collapsed s hs] at path
        exact path.tail (sem_step_src hj s)

theorem equality_cof_step_lift {n m : ℕ} {D E : Dag} {ρ : Fin n → Option Bool}
    {ι : Fin m → Fin n} {t q : ℕ → ℕ} (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hI : cof_Inv D ρ ι D.length E t q) {a b : ℕ} (hab : sem_step m E a b) :
    Relation.ReflTransGen (sem_step n D) (equality_cof_rep ι q a) (equality_cof_rep ι q b) := by
  obtain ⟨j,s,hj,rfl,rfl⟩ := sem_step_iff.mp hab
  obtain ⟨hq,_,_,ha,hb,hla,hlb⟩ := hI.2.2.1 j hj
  have image : src E (j,s) = t (src D (q j,s)) := by
    cases s <;> simp only [sb_src_false,sb_src_true] <;> assumption
  have live : cof_live D ρ ι (src D (q j,s)) := by
    cases s <;> simp only [sb_src_false,sb_src_true] <;> assumption
  rw [image,equality_cof_rep_gate]
  exact (equality_cof_rep_reaches hS hok hI live).tail (sem_step_src hq s)

theorem equality_cof_path_lift {n m : ℕ} {D E : Dag} {ρ : Fin n → Option Bool}
    {ι : Fin m → Fin n} {t q : ℕ → ℕ} (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hI : cof_Inv D ρ ι D.length E t q) {a b : ℕ}
    (hab : Relation.ReflTransGen (sem_step m E) a b) :
    Relation.ReflTransGen (sem_step n D) (equality_cof_rep ι q a) (equality_cof_rep ι q b) := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact ih.trans (equality_cof_step_lift hS hok hI step)

theorem equality_cof_preserves_protection {n m : ℕ} {D E : Dag} {ρ : Fin n → Option Bool}
    {ι : Fin m → Fin n} {t q : ℕ → ℕ} (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hI : cof_Inv D ρ ι D.length E t q) (i : Fin m)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step n D) (ι i).val w → fanout D w ≤ 1) :
    ∀ e, Relation.ReflTransGen (sem_step m E) i.val e → fanout E e ≤ 1 := by
  classical
  intro e path
  have lifted := equality_cof_path_lift hS hok hI path
  rw [equality_cof_rep_input] at lifted
  have sum : ∑ w ∈ cof_fib D ρ ι t e, cof_deg D ρ ι w ≤ (cof_fib D ρ ι t e).card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro w hw
    obtain ⟨_,live,image⟩ := Finset.mem_filter.mp hw
    apply (cof_deg_le w).trans
    apply hprotected
    have tail := equality_cof_rep_reaches hS hok hI live
    rw [image] at tail
    exact lifted.trans tail
  have bound := cof_fib_bound hS hok hI e
  omega

end PEqualNP.Outside.L_meta_6659_aux

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

namespace PEqualNP.Outside.L_meta_6659_aux

theorem ke_reachable_chain {n : ℕ} {D : Dag} {i w : ℕ}
    (hprotected : ∀ u, Relation.ReflTransGen (sem_step n D) i u → fanout D u ≤ 1)
    (path : Relation.ReflTransGen (sem_step n D) i w) : sem_Chain n D i w := by
  induction path with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a c prior step ih =>
    have one : fanout D a = 1 := by
      have := hprotected a prior
      have := sem_step_fanout step
      omega
    exact Relation.ReflTransGen.tail ih ⟨step,one⟩

theorem ke_full_gen_protected {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    {i v : Fin 10} (hi : i ∈ ineligSet 10 D) {e : ℕ × Bool}
    (he : sem_W 10 D i = {e}) (hiv : k4_Adj i v)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 10 D) i.val w → fanout D w ≤ 1)
    (hv : ∀ p ∈ sem_W 10 D v, p.1 ≠ e.1 → ¬ supp 10 D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp 10 D (src D (sem_bar e)) ↔ k4_Adj i t := by
  have hG := k4_gr
  have hC := hD
  have hS := h.1
  refine sem_full_support hG h hC hi he (fun j hreach hj => ?_)
  by_contra ht
  rw [Bool.not_eq_false] at ht
  rcases Relation.ReflTransGen.cases_tail hreach with heq | ⟨w, hw1, hw2⟩
  · exact hj (by omega)
  · obtain ⟨j', s, hj', hjeq, hsrc⟩ := sem_step_iff.1 hw2
    have hjj : j' = j := by omega
    subst hjj
    have hew : e ∈ sem_W 10 D i := by rw [he]; exact Finset.mem_singleton_self e
    obtain ⟨he1, he2, -⟩ := sem_mem_W.1 hew
    have hreach2 : Relation.ReflTransGen (sem_step 10 D) i.val w :=
      ((sem_rtg_mono (fun _ _ hab => hab.1) (sem_inelig_chain hS hi he2)).tail
        (sem_step_src he1 e.2)).trans hw1
    have hch := ke_reachable_chain hprotected hreach2
    have hf : fanout D w = 1 := by
      have := hprotected w hreach2
      have := sem_step_fanout hw2
      omega
    have hsub : supp 10 D w ⊆ {i} := sem_dom_pure hG hS hC i w (sem_chain_dom hS hch)
    have hvi : v ≠ i := fun hvi => hG.2.1 i (hvi ▸ hiv)
    have hw' : src D (j', !(!s)) = w := by rw [Bool.not_not]; exact hsrc
    have hmem : v ∈ supp 10 D (src D (j', !s)) :=
      sem_and_sibling_nbrs hG hS hC hj' (!s) ht (hw' ▸ hch) (hw' ▸ hf)
        (by unfold outW; omega) hiv
    have hp : ((j', !s) : ℕ × Bool) ∈ sem_W 10 D v :=
      sem_mem_W.2 ⟨hj', hmem, fun hc => by
        have := hsub (hsrc ▸ sem_supp_and_sub hS hj' ht s hc)
        exact hvi (Finset.mem_singleton.1 this)⟩
    exact hv _ hp hj (by rw [show sem_bar (j', !s) = (j', !(!s)) from rfl, hw']; exact hsub)

theorem ke_three_slot_protected {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (pos : Fin 10 → ℕ × Bool)
    (hpos : k4_Pos 10 k4_Adj D pos) {x i j z : Fin 10}
    (hi : i ∈ ineligSet 10 D) (hj : j ∈ ineligSet 10 D)
    (hij : i ≠ j) (hix : k4_Adj i x) (hjx : k4_Adj j x) (hxz : k4_Adj x z)
    (hzi : z ≠ i) (hzj : z ≠ j) (small : (sem_W 10 D x).card ≤ 3)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 10 D) i.val w → fanout D w ≤ 1) :
    ∀ t, t ∈ supp 10 D (src D (pos i)) ↔ k4_Adj i t := by
  classical
  obtain ⟨H,hHx,hHz,_,_,_⟩ := sem_edge_slots k4_gr h.1 hD hxz
  have ai := ke_as_mem hpos hi hix
  have aj := ke_as_mem hpos hj hjx
  have ni : H ≠ pos i := fun equal => hzi (ke_as_priv hpos hi (equal ▸ hHz))
  have nj : H ≠ pos j := fun equal => hzj (ke_as_priv hpos hj (equal ▸ hHz))
  have nij : pos i ≠ pos j := fun equal => hij (hpos.2 i hi j hj equal)
  have code : sem_W 10 D x = {pos i,pos j,H} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      simp only [Finset.mem_insert,Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simp [nij,Ne.symm ni]),
        Finset.card_pair (Ne.symm nj)]
      exact small
  have full := ke_full_gen_protected h hD hi (ke_as_W h hD hpos hi) hix hprotected
    (fun p hp hne hsub => by
      rw [code] at hp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact hne rfl
      · have hjmem : j ∈ supp 10 D (src D (sem_bar (pos j))) := by
          rw [show src D (sem_bar (pos j)) = src D ((pos j).1,!(pos j).2) from rfl,
            (hpos.1 j hj).2.2.2]
          exact Finset.mem_singleton_self j
        exact hij (Finset.mem_singleton.1 (hsub hjmem)).symm
      · exact hzi (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hHz).2.1)))
  simpa only [sem_bar_bar] using full


theorem ke_p6_protected_obstruction {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (hB : Bplus 10 D ≤ 7) (hp : (eligSet 10 D).card = 6)
    {x t i : Fin 10} (hx4 : x.val < 4) (ht4 : t.val < 4)
    (hxm : ke_many (ineligSet 10 D) x) (htm : ke_many (ineligSet 10 D) t)
    (hi : i ∈ ineligSet 10 D) (hix : k4_Adj i x) (hit : ¬ k4_Adj i t)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 10 D) i.val w → fanout D w ≤ 1) : False := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch k4_gr h.1 hD
  obtain ⟨pos,hpos⟩ := k4_assigned k4_gr h hD
  have wx := ke_two_neighbors_three h hD pos hpos hx4 hxm
  have wt := ke_two_neighbors_three h hD pos hpos ht4 htm
  have cx := ke_cc_le h hD b hb x
  have ct := ke_cc_le h hD b hb t
  have cr := card_residual h.1 b hb
  have hsubx : ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card ≤
      (residualUnits 10 D b).card := Finset.card_le_card (Finset.filter_subset _ _)
  have hsubt : ((residualUnits 10 D b).filter (fun u => t ∈ supp 10 D u.1)).card ≤
      (residualUnits 10 D b).card := Finset.card_le_card (Finset.filter_subset _ _)
  have hR : (residualUnits 10 D b).card = 1 := by omega
  have small : (sem_W 10 D x).card ≤ 3 := by omega
  obtain ⟨rx,hrx⟩ := Finset.card_pos.mp (by omega :
    0 < ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card)
  obtain ⟨rt,hrt⟩ := Finset.card_pos.mp (by omega :
    0 < ((residualUnits 10 D b).filter (fun u => t ∈ supp 10 D u.1)).card)
  obtain ⟨hrxR,hrxx⟩ := Finset.mem_filter.mp hrx
  obtain ⟨hrtR,hrtt⟩ := Finset.mem_filter.mp hrt
  have huniq : ∀ u ∈ residualUnits 10 D b, u = rt := fun u hu =>
    Finset.card_le_one.mp (by omega) u hu rt hrtR
  have incl : ∀ u ∈ residualUnits 10 D b, x ∈ supp 10 D u.1 → t ∈ supp 10 D u.1 := by
    intro u hu _
    rw [huniq u hu]
    exact hrtt
  have htmem := ke_residual_co_label h hD b hb pos hpos (res_elig hrxR hrxx)
    (res_elig hrtR hrtt) hi hix hx4 ht4 incl ⟨rx.1,hrxx,by rw [huniq rx hrxR];exact hrtt⟩
  obtain ⟨j,hj,hji,hjx⟩ := ke_neighbor_pair hxm hi hix
  have hgeo : ∀ x i j : Fin 10, x.val < 4 → k4_Adj i x → k4_Adj j x → i ≠ j →
      ∃ z, k4_Adj x z ∧ z ≠ i ∧ z ≠ j := by decide +kernel
  obtain ⟨z,hxz,hzi,hzj⟩ := hgeo x i j hx4 hix hjx (Ne.symm hji)
  exact hit ((ke_three_slot_protected h hD pos hpos hi hj (Ne.symm hji) hix hjx hxz hzi hzj small hprotected t).1 htmem)


theorem ke_p7_supported_at_most_two {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (hB : Bplus 10 D ≤ 7) (hp : (eligSet 10 D).card = 7) :
    (({0,1,2,3} : Finset (Fin 10)) ∩ eligSet 10 D).card ≤ 2 := by
  classical
  by_contra hnot
  have hcard := inelig_card_add 10 D
  have hIcard : (ineligSet 10 D).card = 3 := by omega
  have heq : ({0,1,2,3} : Finset (Fin 10)) \ ineligSet 10 D =
      ({0,1,2,3} : Finset (Fin 10)) ∩ eligSet 10 D := by
    ext i
    simp only [Finset.mem_sdiff,Finset.mem_inter,sem_mem_inelig,not_not]
  obtain ⟨x,hx4,hxm⟩ := ke_p7_geometry (ineligSet 10 D)
    (k4_inelig_indep h hD) hIcard (by rw [heq]; omega)
  obtain ⟨b,hb⟩ := sem_exists_pureBranch k4_gr h.1 hD
  obtain ⟨pos,hpos⟩ := k4_assigned k4_gr h hD
  have wx := ke_two_neighbors_three h hD pos hpos hx4 hxm
  have cx := ke_cc_le h hD b hb x
  have cr := card_residual h.1 b hb
  have hsubx : ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card ≤
      (residualUnits 10 D b).card := Finset.card_le_card (Finset.filter_subset _ _)
  omega

theorem ke_low_supported_impossible {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (hB : Bplus 10 D ≤ 7) (hp : (eligSet 10 D).card ≤ 5) : False := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch k4_gr h.1 hD
  obtain ⟨pos,hpos⟩ := k4_assigned k4_gr h hD
  have cr := card_residual h.1 b hb
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

theorem ke_matching_protected_geometry : ∀ I : Finset (Fin 10),
    (∀ u ∈ I, ∀ v ∈ I, k4_adjB u v = false) → I.card = 4 → 5 ∈ I → 8 ∈ I →
    ∃ x t : Fin 10, x.val < 4 ∧ t.val < 4 ∧ ke_many I x ∧ ke_many I t ∧
      k4_Adj 5 x ∧ ¬ k4_Adj 5 t := by
  have cases : ∀ I : Finset (Fin 10),
      (∀ u ∈ I, ∀ v ∈ I, k4_adjB u v = false) → I.card = 4 → 5 ∈ I → 8 ∈ I →
      I = {4,5,6,8} ∨ I = {4,5,7,8} ∨ I = {4,5,8,9} ∨
      I = {5,6,7,8} ∨ I = {5,6,8,9} ∨ I = {5,7,8,9} := by decide +kernel
  intro I hind hcard h5 h8
  rcases cases I hind hcard h5 h8 with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0,1,by decide⟩
  · exact ⟨0,1,by decide⟩
  · exact ⟨0,1,by decide⟩
  · exact ⟨0,1,by decide⟩
  · exact ⟨0,3,by decide⟩
  · exact ⟨2,1,by decide⟩

theorem ke_protected_matching_supported_lower {D : Dag}
    (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (h5 : (5 : Fin 10) ∈ ineligSet 10 D) (h8 : (8 : Fin 10) ∈ ineligSet 10 D)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 10 D) 5 w → fanout D w ≤ 1) :
    8 ≤ Bplus 10 D := by
  classical
  by_contra hn
  have hB : Bplus 10 D ≤ 7 := by omega
  have cover : ∀ u v : Fin 10, k4_Adj u v → u ∈ eligSet 10 D ∨ v ∈ eligSet 10 D :=
    fun u v huv => sem_elig_cover k4_gr h hD huv
  have geo : ∀ S : Finset (Fin 10),
      (∀ u v : Fin 10, k4_Adj u v → u ∈ S ∨ v ∈ S) → 5 ∉ S → 8 ∉ S →
      ({0,1,2,3} : Finset (Fin 10)) ⊆ S := by decide +kernel
  have sub := geo (eligSet 10 D) cover (sem_mem_inelig.mp h5) (sem_mem_inelig.mp h8)
  have horig : (({0,1,2,3} : Finset (Fin 10)) ∩ eligSet 10 D).card = 4 := by
    rw [Finset.inter_eq_left.mpr sub]
    decide
  obtain ⟨b,hb⟩ := sem_exists_pureBranch k4_gr h.1 hD
  have hp := elig_le_Bplus h.1 b hb
  by_cases small : (eligSet 10 D).card ≤ 5
  · exact ke_low_supported_impossible h hD hB small
  · by_cases six : (eligSet 10 D).card = 6
    · have hcard := inelig_card_add 10 D
      obtain ⟨x,t,hx,ht,hxm,htm,hix,hit⟩ := ke_matching_protected_geometry (ineligSet 10 D)
        (k4_inelig_indep h hD) (by omega) h5 h8
      exact ke_p6_protected_obstruction h hD hB six hx ht hxm htm h5 hix hit hprotected
    · have bound := ke_p7_supported_at_most_two h hD hB (by omega)
      omega

end PEqualNP.Outside.L_meta_6659_aux

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
