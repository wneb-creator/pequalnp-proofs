import PNPNineFree
import PNPMixed9Finite
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




def m9_neighbors (i : Fin 4) : Finset (Fin 6) :=
  ![{0,1,2},{0,3,4},{1,3,5},{2,4,5}] i

def m9_protected (i : Fin 2) : Fin 4 := Fin.castLE (by decide) i

def m9_forced (r : Fin 6 → Finset (Fin 3)) (a b : Fin 3) (i : Fin 4) : Finset (Fin 6) :=
  Finset.univ.filter (fun t => (∃ x ∈ m9_neighbors i, r x ⊆ r t) ∨
    (i = 2 ∧ t = m9_extra2 a) ∨ (i = 3 ∧ t = m9_extra5 b))

def m9_consumers (r : Fin 6 → Finset (Fin 3)) (a b : Fin 3) (t : Fin 6) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => t ∈ m9_forced r a b i)

def m9_saturated (r : Fin 6 → Finset (Fin 3)) (a b : Fin 3) (i : Fin 2) : Prop :=
  ∃ x ∈ m9_neighbors (m9_protected i), (m9_consumers r a b x).card = 1 + (r x).card

def m9_unit_support (r : Fin 6 → Finset (Fin 3)) (k : Fin 3) : Finset (Fin 6) :=
  Finset.univ.filter (fun t => k ∈ r t)

abbrev m9_constraints (r : Fin 6 → Finset (Fin 3)) (a b : Fin 3) : Prop :=
  (∀ t, (r t).Nonempty ∧ r t ≠ Finset.univ) ∧
  (∀ k, m9_unit_support r k ≠ m9_neighbors 2 ∧ m9_unit_support r k ≠ m9_neighbors 3) ∧
  (∀ t, (m9_consumers r a b t).card ≤ 1 + (r t).card) ∧
  (∀ i, m9_saturated r a b i → m9_forced r a b (m9_protected i) ⊆ m9_neighbors (m9_protected i))

def m9_point_forced (r : Fin 6 → Finset (Fin 3)) (T : Finset (Fin 3)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => ∃ x ∈ m9_neighbors i, r x ⊆ T)

abbrev m9_point_constraints (r : Fin 6 → Finset (Fin 3)) (a b : Fin 3)
    (T : Finset (Fin 3)) : Prop :=
  T.Nonempty ∧
  (∀ i, m9_saturated r a b i → m9_protected i ∉ m9_point_forced r T) ∧
  (m9_point_forced r T).card ≤ T.card ∧
  (∀ t, (m9_consumers r a b t).card + (if T ⊆ r t then 1 else 0) ≤ 1 + (r t).card)

theorem m9_sub_correct : ∀ a b : Fin 8, m9_sub a b = true ↔ m9_mask a ⊆ m9_mask b := by
  decide +kernel

theorem m9_card_correct : ∀ a : Fin 8, m9_card a = (m9_mask a).card := by decide +kernel

theorem m9_bit_correct : ∀ a : Fin 8, ∀ k : Fin 3, m9_bit a k = true ↔ k ∈ m9_mask a := by
  decide +kernel

theorem m9_mask_nonempty : ∀ a : Fin 8, a ≠ 0 ↔ (m9_mask a).Nonempty := by decide +kernel

theorem m9_mask_proper : ∀ a : Fin 8, a ≠ 7 ↔ m9_mask a ≠ Finset.univ := by decide +kernel

theorem m9_filter_four : ∀ f : Fin 4 → Bool,
    (Finset.univ.filter (fun i => f i = true)).card =
      (f 0).toNat + (f 1).toNat + (f 2).toNat + (f 3).toNat := by decide +kernel

theorem m9_force_correct (r : Fin 6 → Fin 8) (a b : Fin 3) (i : Fin 4) (t : Fin 6) :
    m9_force r a b i t = true ↔ t ∈ m9_forced (fun x => m9_mask (r x)) a b i := by
  fin_cases i <;> simp [m9_force,m9_forced,m9_neighbors,m9_sub_correct,or_assoc]

theorem m9_count_correct (r : Fin 6 → Fin 8) (a b : Fin 3) (t : Fin 6) :
    m9_count r a b t = (m9_consumers (fun x => m9_mask (r x)) a b t).card := by
  have equal : m9_consumers (fun x => m9_mask (r x)) a b t =
      Finset.univ.filter (fun i => m9_force r a b i t = true) := by
    ext i
    simp [m9_consumers,m9_force_correct]
  rw [equal,m9_filter_four]
  rfl

theorem m9_full_correct (r : Fin 6 → Fin 8) (a b : Fin 3) (i : Fin 2) :
    m9_full r a b i = true ↔ m9_saturated (fun x => m9_mask (r x)) a b i := by
  fin_cases i <;>
    simp [m9_full,m9_saturated,m9_neighbors,m9_protected,m9_count_correct,m9_card_correct,or_assoc]

theorem m9_pointForce_correct (r : Fin 6 → Fin 8) (T : Fin 8) (i : Fin 4) :
    m9_pointForce r T i = true ↔ i ∈ m9_point_forced (fun x => m9_mask (r x)) (m9_mask T) := by
  unfold m9_point_forced
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ,true_and]
  fin_cases i <;> simp [m9_pointForce,m9_neighbors,m9_sub_correct,or_assoc]

theorem m9_pointCount_correct (r : Fin 6 → Fin 8) (T : Fin 8) :
    (m9_pointForce r T 0).toNat + (m9_pointForce r T 1).toNat +
      (m9_pointForce r T 2).toNat + (m9_pointForce r T 3).toNat =
      (m9_point_forced (fun x => m9_mask (r x)) (m9_mask T)).card := by
  have equal : m9_point_forced (fun x => m9_mask (r x)) (m9_mask T) =
      Finset.univ.filter (fun i => m9_pointForce r T i = true) := by
    ext i
    simp [m9_pointForce_correct]
  rw [equal,m9_filter_four]

theorem m9_unit_code_two : ∀ f : Fin 6 → Bool,
    (f 0).toNat + 2*(f 1).toNat + 4*(f 2).toNat + 8*(f 3).toNat +
      16*(f 4).toNat + 32*(f 5).toNat = 42 ↔
      Finset.univ.filter (fun t => f t = true) = m9_neighbors 2 := by decide +kernel

theorem m9_unit_code_five : ∀ f : Fin 6 → Bool,
    (f 0).toNat + 2*(f 1).toNat + 4*(f 2).toNat + 8*(f 3).toNat +
      16*(f 4).toNat + 32*(f 5).toNat = 52 ↔
      Finset.univ.filter (fun t => f t = true) = m9_neighbors 3 := by decide +kernel

theorem m9_unitMask_correct (r : Fin 6 → Fin 8) (k : Fin 3) :
    (m9_unitMask r k = 42 ↔ m9_unit_support (fun x => m9_mask (r x)) k = m9_neighbors 2) ∧
    (m9_unitMask r k = 52 ↔ m9_unit_support (fun x => m9_mask (r x)) k = m9_neighbors 3) := by
  have equal : Finset.univ.filter (fun t => m9_bit (r t) k = true) =
      m9_unit_support (fun x => m9_mask (r x)) k := by
    ext t
    simp [m9_unit_support,m9_bit_correct]
  constructor
  · simpa only [m9_unitMask,equal] using m9_unit_code_two (fun t => m9_bit (r t) k)
  · simpa only [m9_unitMask,equal] using m9_unit_code_five (fun t => m9_bit (r t) k)

theorem m9_bool_imp (a b : Bool) (h : a = true → b = true) : (!a || b) = true := by
  cases a <;> simp_all

theorem m9_not_both (a b : Bool) (h : a = true → b = true → False) : !(a && b) = true := by
  cases a <;> cases b <;> simp_all

theorem m9_normal_of_constraints (r : Fin 6 → Fin 8) (a b : Fin 3)
    (hc : m9_constraints (fun t => m9_mask (r t)) a b) : m9_normal r a b = true := by
  have proper (t : Fin 6) : r t ≠ 0 ∧ r t ≠ 7 :=
    ⟨(m9_mask_nonempty _).2 (hc.1 t).1,(m9_mask_proper _).2 (hc.1 t).2⟩
  have missing (k : Fin 3) : m9_unitMask r k ≠ 42 ∧ m9_unitMask r k ≠ 52 :=
    ⟨fun equal => (hc.2.1 k).1 ((m9_unitMask_correct r k).1.1 equal),
      fun equal => (hc.2.1 k).2 ((m9_unitMask_correct r k).2.1 equal)⟩
  have budget (t : Fin 6) : m9_count r a b t ≤ 1 + m9_card (r t) := by
    rw [m9_count_correct,m9_card_correct]
    exact hc.2.2.1 t
  have outside (i : Fin 2) (full : m9_full r a b i = true) (t : Fin 6)
      (notNeighbor : t ∉ m9_neighbors (m9_protected i)) :
      m9_force r a b (m9_protected i) t = false := by
    cases value : m9_force r a b (m9_protected i) t with
    | false => rfl
    | true =>
      exact False.elim (notNeighbor (hc.2.2.2 i ((m9_full_correct r a b i).1 full)
        ((m9_force_correct r a b _ t).1 value)))
  have full0 : (!m9_full r a b 0 ||
      (!m9_force r a b 0 3 && !m9_force r a b 0 4 && !m9_force r a b 0 5)) = true := by
    apply m9_bool_imp
    intro full
    have h3 := outside 0 full 3 (by decide)
    have h4 := outside 0 full 4 (by decide)
    have h5 := outside 0 full 5 (by decide)
    change m9_force r a b 0 3 = false at h3
    change m9_force r a b 0 4 = false at h4
    change m9_force r a b 0 5 = false at h5
    simp [h3,h4,h5]
  have full1 : (!m9_full r a b 1 ||
      (!m9_force r a b 1 1 && !m9_force r a b 1 2 && !m9_force r a b 1 5)) = true := by
    apply m9_bool_imp
    intro full
    have h1 := outside 1 full 1 (by decide)
    have h2 := outside 1 full 2 (by decide)
    have h5 := outside 1 full 5 (by decide)
    change m9_force r a b 1 1 = false at h1
    change m9_force r a b 1 2 = false at h2
    change m9_force r a b 1 5 = false at h5
    simp [h1,h2,h5]
  have p0 := proper 0
  have p1 := proper 1
  have p2 := proper 2
  have p3 := proper 3
  have p4 := proper 4
  have p5 := proper 5
  have u0 := missing 0
  have u1 := missing 1
  have u2 := missing 2
  have b0 := budget 0
  have b1 := budget 1
  have b2 := budget 2
  have b3 := budget 3
  have b4 := budget 4
  have b5 := budget 5
  simp only [m9_normal,full0,full1,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq]
  tauto

theorem m9_sub_toNat : ∀ a b : Fin 8,
    (m9_sub a b).toNat = if m9_mask a ⊆ m9_mask b then 1 else 0 := by decide +kernel

theorem m9_pointAllowed_of_constraints (r : Fin 6 → Fin 8) (a b : Fin 3) (T : Fin 8)
    (hc : m9_point_constraints (fun t => m9_mask (r t)) a b (m9_mask T)) :
    m9_pointAllowed r a b T = true := by
  have nonempty : T ≠ 0 := (m9_mask_nonempty T).2 hc.1
  have absent (i : Fin 2) : !(m9_full r a b i && m9_pointForce r T (m9_protected i)) = true := by
    apply m9_not_both
    intro full forced
    exact hc.2.1 i ((m9_full_correct r a b i).1 full)
      ((m9_pointForce_correct r T (m9_protected i)).1 forced)
  have count : (m9_pointForce r T 0).toNat + (m9_pointForce r T 1).toNat +
      (m9_pointForce r T 2).toNat + (m9_pointForce r T 3).toNat ≤ m9_card T := by
    rw [m9_pointCount_correct,m9_card_correct]
    exact hc.2.2.1
  have budget (t : Fin 6) : m9_count r a b t + (m9_sub T (r t)).toNat ≤ 1+m9_card (r t) := by
    rw [m9_count_correct,m9_sub_toNat,m9_card_correct]
    exact hc.2.2.2 t
  have a0 := absent 0
  have a1 := absent 1
  change (!(m9_full r a b 0 && m9_pointForce r T 0)) = true at a0
  change (!(m9_full r a b 1 && m9_pointForce r T 1)) = true at a1
  have b0 := budget 0
  have b1 := budget 1
  have b2 := budget 2
  have b3 := budget 3
  have b4 := budget 4
  have b5 := budget 5
  simp only [m9_pointAllowed,Bool.and_eq_true,decide_eq_true_eq]
  tauto


theorem m9_mask_surjective : Function.Surjective m9_mask := by decide +kernel

theorem m9_mask_injective : Function.Injective m9_mask := by decide +kernel

theorem m9_no_point_constraints_of_certificate
    (certificate : ∀ (r : Fin 6 → Fin 8) (a b : Fin 3) (T : Fin 8),
      (r 0 = 1 ∨ r 0 = 3) → m9_normal r a b = true → m9_pointAllowed r a b T = false)
    (r : Fin 6 → Finset (Fin 3)) (a b : Fin 3) (T : Finset (Fin 3))
    (first : r 0 = {0} ∨ r 0 = {0,1}) (normal : m9_constraints r a b)
    (point : m9_point_constraints r a b T) : False := by
  classical
  choose code encoded using (fun t => m9_mask_surjective (r t))
  obtain ⟨pointCode,pointEncoded⟩ := m9_mask_surjective T
  have vector : (fun t => m9_mask (code t)) = r := funext encoded
  have firstCode : code 0 = 1 ∨ code 0 = 3 := by
    rcases first with first | first
    · apply Or.inl
      apply m9_mask_injective
      rw [encoded,first]
      rfl
    · apply Or.inr
      apply m9_mask_injective
      rw [encoded,first]
      rfl
  have normalCode : m9_normal code a b = true :=
    m9_normal_of_constraints code a b (by simpa only [vector] using normal)
  have pointTrue : m9_pointAllowed code a b pointCode = true :=
    m9_pointAllowed_of_constraints code a b pointCode
      (by simpa only [vector,pointEncoded] using point)
  have pointFalse := certificate code a b pointCode firstCode normalCode
  rw [pointFalse] at pointTrue
  exact Bool.false_ne_true pointTrue

theorem equality_lost_saturates_chain {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (P : Finset (Fin 14)) (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b)
    (J : Finset (Fin 14))
    (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ sem_hw_nb i ⊆ P ∧
      ¬ sup_Occ 14 D P (sem_hw_nb i))
    (budget : J.card = Bzero 14 D) {v : Fin 14}
    (hv : v ∈ ineligSet 14 D) (hvJ : v ∉ J) (hvP : sem_hw_nb v ⊆ P) :
    sem_Chain 14 D v.val (outW 14 D) := by
  classical
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  rcases sem_inelig_reach hG h hC hv with chain | ⟨bv,hbv,hbf,hbs⟩
  · exact chain
  exfalso
  have absent : ∀ i ∈ J, ∀ q,
      (∀ a ∈ P, (a ∈ supp 14 D q ↔ Adj i a)) → False := by
    intro i hi q hq
    refine (hJ i hi).2.2 ⟨q, ?_⟩
    ext a
    rw [Finset.mem_inter, hw_mem_nb]
    exact ⟨fun h1 => (hq a h1.2).1 h1.1,
      fun h1 => ⟨(hq a ((hJ i hi).2.1 (hw_mem_nb.2 h1))).2 h1,
        (hJ i hi).2.1 (hw_mem_nb.2 h1)⟩⟩
  have hb : ∀ i ∈ insert v J,
      ∃ b, sem_Chain 14 D i.val b ∧ 2 ≤ fanout D b ∧ supp 14 D b = ∅ := by
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨bv,hbv,hbf,hbs⟩
    · rcases sem_inelig_reach hG h hC (hJ i hi).1 with chain | branch
      · obtain ⟨j,s,_,_,_,hq⟩ := sem_exact_nbhd hG h.1 hC P hP chain
        exact (absent i hi _ hq).elim
      · exact branch
  choose! β hβ using hb
  have neighbors : ∀ i ∈ insert v J, sem_hw_nb i ⊆ P := by
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hvP
    · exact (hJ i hi).2.1
  have distinct : ∀ i ∈ J, ∀ j ∈ insert v J, i ≠ j → β i ≠ β j := by
    intro i hi j hj different equal
    have hi' : i ∈ insert v J := Finset.mem_insert_of_mem hi
    obtain ⟨a,ha1,ha2⟩ := nbr_diff_exists j i (Ne.symm different)
    obtain ⟨k,s,_,_,_,_,hq⟩ := sem_shared_exact hG h.1 hC P hP (hβ i hi').1
      (sem_chain_dom h.1 (equal ▸ (hβ j hj).1))
      ⟨a,neighbors j hj (hw_mem_nb.2 ha1),ha1,ha2⟩
    exact absent i hi _ hq
  have injective : Set.InjOn β ((insert v J : Finset (Fin 14)) : Set (Fin 14)) := by
    intro i hi j hj equal
    by_contra different
    by_cases hiJ : i ∈ J
    · exact distinct i hiJ j hj different equal
    · have hiv : i = v := (Finset.mem_insert.1 hi).resolve_right hiJ
      have hjJ : j ∈ J := (Finset.mem_insert.1 hj).resolve_left (by
        intro hjv
        exact different (hiv.trans hjv.symm))
      exact distinct j hjJ i hi (Ne.symm different) equal.symm
  have bound : ((insert v J).image β).card ≤ Bzero 14 D := by
    apply bz_card h.1
    intro b hb
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 hb
    exact (hβ i hi).2
  rw [Finset.card_image_of_injOn injective,Finset.card_insert_of_notMem hvJ,budget] at bound
  omega

theorem equality_chain_protected {D : Dag} (strict : Strict 14 D) {v : ℕ}
    (chain : sem_Chain 14 D v (outW 14 D)) :
    ∀ w, Relation.ReflTransGen (sem_step 14 D) v w → fanout D w ≤ 1 := by
  have last : fanout D (outW 14 D) = 0 :=
    fanout_eq_zero_of_ge strict _ (by unfold outW; omega)
  induction chain using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro w path
    rcases Relation.ReflTransGen.cases_head path with equal | ⟨next,first,rest⟩
    · rw [← equal,last]
      omega
    · have positive := sem_step_fanout first
      omega
  | @head a next first rest ih =>
    intro w path
    rcases Relation.ReflTransGen.cases_head path with equal | ⟨next',initial,remaining⟩
    · rw [← equal,first.2]
    · have same : next = next' := sem_step_unique first.1 initial first.2
      subst next'
      exact ih w remaining



noncomputable def equality_missing_cap (D : Dag) : Finset (Fin 14) := by
  classical
  exact ({0, 1, 2, 5} : Finset (Fin 14)).filter
    (fun i => ¬ sup_Occ 14 D mx_L (sem_hw_nb i))



theorem equality_mixed_cap_saturated {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0, 1, 2, 5, 11}) :
    (equality_missing_cap D).card = Bzero 14 D := by
  classical
  have hel := inelig_card_add 14 D
  rw [hI, show ({0, 1, 2, 5, 11} : Finset (Fin 14)).card = 5 from rfl] at hel
  have hcap : ∀ i ∈ ({0, 1, 2, 5} : Finset (Fin 14)), i ∈ ineligSet 14 D := by rw [hI]; decide
  have hstar := mx_star h hD hcap
  have hLl : mx_L ⊆ sem_hw_opp 0 := by decide
  have hPe : mx_L ⊆ eligSet 14 D := by
    intro a ha
    by_contra hne
    have h1 := sem_mem_inelig.2 hne
    rw [hI] at h1
    exact mx_el a ha h1
  let Oc := ({0, 1, 2, 5} : Finset (Fin 14)).filter (fun i => sup_Occ 14 D mx_L (sem_hw_nb i))
  let Mc := ({0, 1, 2, 5} : Finset (Fin 14)).filter (fun i => ¬ sup_Occ 14 D mx_L (sem_hw_nb i))
  have hcnt := hw_count h hD mx_L hLl hPe Oc {3, 4, 6} {0, 1, 2, 5}
    (fun i hi => ⟨mx_cap i (Finset.mem_filter.1 hi).1, (Finset.mem_filter.1 hi).2⟩)
    (fun c hc => ⟨fun hc' => (mx_ctr c hc).1 (Finset.mem_filter.1 hc').1, Or.inl (mx_ctr c hc).2⟩)
    (fun i hi => ⟨hcap i hi, mx_cap i hi⟩)
  have hlost := hw_lost h hD mx_L
    (fun a ha b hb => sem_hw_opp_indep 0 a (hLl ha) b (hLl hb)) Mc
    (fun i hi => ⟨hcap i (Finset.mem_filter.1 hi).1, mx_cap i (Finset.mem_filter.1 hi).1,
      (Finset.mem_filter.1 hi).2⟩)
  have hsplit : Oc.card + Mc.card = 4 :=
    Finset.card_filter_add_card_filter_not (s := ({0, 1, 2, 5} : Finset (Fin 14)))
      (fun i => sup_Occ 14 D mx_L (sem_hw_nb i))
  rw [mx_lab, show ({0, 1, 2, 5} : Finset (Fin 14)).card = 4 from rfl,
    show mx_L.card = 6 from rfl] at hcnt
  have htotal := totalSurplus_split 14 D
  change Mc.card = Bzero 14 D
  omega

theorem equality_mixed_cap_occ_chain {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0, 1, 2, 5, 11}) {v : Fin 14}
    (hv : v ∈ ({0, 1, 2, 5} : Finset (Fin 14)))
    (hmask : sup_Occ 14 D mx_L (sem_hw_nb v)) :
    sem_Chain 14 D v.val (outW 14 D) := by
  classical
  let J := ({0, 1, 2, 5} : Finset (Fin 14)).filter
    (fun i => ¬ sup_Occ 14 D mx_L (sem_hw_nb i))
  have hLl : mx_L ⊆ sem_hw_opp 0 := by decide
  have hin : ∀ i ∈ ({0, 1, 2, 5} : Finset (Fin 14)), i ∈ ineligSet 14 D := by rw [hI]; decide
  apply equality_lost_saturates_chain h hD mx_L
    (fun a ha b hb => sem_hw_opp_indep 0 a (hLl ha) b (hLl hb)) J
  · intro i hi
    exact ⟨hin i (Finset.mem_filter.1 hi).1,mx_cap i (Finset.mem_filter.1 hi).1,
      (Finset.mem_filter.1 hi).2⟩
  · exact equality_mixed_cap_saturated h hD h14 hI
  · exact hin v hv
  · intro hi
    exact (Finset.mem_filter.1 hi).2 hmask
  · exact mx_cap v hv


theorem equality_reachable_chain {n : ℕ} {D : Dag} {i w : ℕ}
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

theorem equality_full_gen_protected {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {i v : Fin 14} (hi : i ∈ ineligSet 14 D) {e : ℕ × Bool}
    (he : sem_W 14 D i = {e}) (hiv : Adj i v)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1)
    (hv : ∀ p ∈ sem_W 14 D v, p.1 ≠ e.1 → ¬ supp 14 D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp 14 D (src D (sem_bar e)) ↔ Adj i t := by
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  have hS := h.1
  refine sem_full_support hG h hC hi he (fun j hreach hj => ?_)
  by_contra ht
  rw [Bool.not_eq_false] at ht
  rcases Relation.ReflTransGen.cases_tail hreach with heq | ⟨w, hw1, hw2⟩
  · exact hj (by omega)
  · obtain ⟨j', s, hj', hjeq, hsrc⟩ := sem_step_iff.1 hw2
    have hjj : j' = j := by omega
    subst hjj
    have hew : e ∈ sem_W 14 D i := by rw [he]; exact Finset.mem_singleton_self e
    obtain ⟨he1, he2, -⟩ := sem_mem_W.1 hew
    have hreach2 : Relation.ReflTransGen (sem_step 14 D) i.val w :=
      ((sem_rtg_mono (fun _ _ hab => hab.1) (sem_inelig_chain hS hi he2)).tail
        (sem_step_src he1 e.2)).trans hw1
    have hch := equality_reachable_chain hprotected hreach2
    have hf : fanout D w = 1 := by
      have := hprotected w hreach2
      have := sem_step_fanout hw2
      omega
    have hsub : supp 14 D w ⊆ {i} := sem_dom_pure hG hS hC i w (sem_chain_dom hS hch)
    have hvi : v ≠ i := fun hvi => hG.2.1 i (hvi ▸ hiv)
    have hw' : src D (j', !(!s)) = w := by rw [Bool.not_not]; exact hsrc
    have hmem : v ∈ supp 14 D (src D (j', !s)) :=
      sem_and_sibling_nbrs hG hS hC hj' (!s) ht (hw' ▸ hch) (hw' ▸ hf)
        (by unfold outW; omega) hiv
    have hp : ((j', !s) : ℕ × Bool) ∈ sem_W 14 D v :=
      sem_mem_W.2 ⟨hj', hmem, fun hc => by
        have := hsub (hsrc ▸ sem_supp_and_sub hS hj' ht s hc)
        exact hvi (Finset.mem_singleton.1 this)⟩
    exact hv _ hp hj (by rw [show sem_bar (j', !s) = (j', !(!s)) from rfl, hw']; exact hsub)

theorem equality_residual_co_label {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) {x t i : Fin 14}
    (hx : x ∈ eligSet 14 D) (ht : t ∈ eligSet 14 D) (hi : i ∈ ineligSet 14 D)
    (hix : Adj i x)
    (inclusion : ∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → t ∈ supp 14 D u.1)
    (shared : ∃ w, x ∈ supp 14 D w ∧ t ∈ supp 14 D w) :
    t ∈ supp 14 D (src D (pos i)) := by
  by_cases hxt : x = t
  · exact hxt ▸ (hpos.1 i hi).2.2.1 x hix
  obtain ⟨w,hw⟩ := shared
  obtain ⟨e0,he0⟩ := ri_gen sem_heawood_gr h (sem_heawood_comp hD) b hb hxt hx inclusion hw
  have hti : t ≠ i := fun equal => sem_mem_inelig.1 hi (equal ▸ ht)
  have hgeo : ∀ i x t : Fin 14, hc_adjB i x = true → t ≠ x → t ≠ i →
      ∃ q, hc_adjB i q = true ∧ q ≠ x ∧ hc_adjB t q = false := by decide +kernel
  obtain ⟨q,hiq,hqx,htq⟩ := hgeo i x t ((hc_adjB_iff _ _).2 hix) (Ne.symm hxt) hti
  have hiq' := (hc_adjB_iff _ _).1 hiq
  have htq' := sem_adjB_false.1 htq
  by_contra hnot
  have heq : pos i = e0 := by
    by_contra hne
    exact hnot (he0 _ (as_mem hpos hi hix) hne)
  obtain ⟨e,he,hnt,hnq⟩ := sem_hw_cover_free h hD hxt (Ne.symm hqx) htq'
  exact hnt (he0 e he (fun equal => hnq (by
    rw [equal,← heq]
    exact (hpos.1 i hi).2.2.1 q hiq')))

theorem equality_three_slot_full {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) {x i j z : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hj : j ∈ ineligSet 14 D)
    (hij : i ≠ j) (hix : Adj i x) (hjx : Adj j x) (hxz : Adj x z)
    (hzi : z ≠ i) (hzj : z ≠ j) (hru : (ru D b x).card ≤ 1)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1) :
    ∀ t, t ∈ supp 14 D (src D (pos i)) ↔ Adj i t := by
  classical
  obtain ⟨H,hHx,hHz,_,_,_⟩ := sem_edge_slots sem_heawood_gr h.1 (sem_heawood_comp hD) hxz
  have ai := as_mem hpos hi hix
  have aj := as_mem hpos hj hjx
  have ni : H ≠ pos i := fun equal => hzi (as_priv hpos hi (equal ▸ hHz))
  have nj : H ≠ pos j := fun equal => hzj (as_priv hpos hj (equal ▸ hHz))
  have nij : pos i ≠ pos j := fun equal => hij (hpos.2 i hi j hj equal)
  have small : (sem_W 14 D x).card ≤ 3 := by
    have := cc_le h hD b hb x
    omega
  have code : sem_W 14 D x = {pos i,pos j,H} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      simp only [Finset.mem_insert,Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simp [nij,Ne.symm ni]),
        Finset.card_pair (Ne.symm nj)]
      exact small
  have full := equality_full_gen_protected h hD hi (as_W h hD hpos hi) hix hprotected
    (fun p hp hne hsub => by
      rw [code] at hp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact hne rfl
      · have hjmem : j ∈ supp 14 D (src D (sem_bar (pos j))) := by
          rw [show src D (sem_bar (pos j)) = src D ((pos j).1,!(pos j).2) from rfl,
            (hpos.1 j hj).2.2.2]
          exact Finset.mem_singleton_self j
        exact hij (Finset.mem_singleton.1 (hsub hjmem)).symm
      · exact hzi (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hHz).2.1)))
  simpa only [sem_bar_bar] using full

theorem equality_assigned_mem {D : Dag} {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 HG D pos) {i t : Fin 14} (hi : i ∈ ineligSet 14 D)
    (ht : t ∈ supp 14 D (src D (pos i))) : pos i ∈ sem_W 14 D t :=
  sem_mem_W.2 ⟨(hpos.1 i hi).1,ht,by
    rw [(hpos.1 i hi).2.1]
    exact Finset.notMem_empty t⟩

theorem equality_assigned_budget {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) (J : Finset (Fin 14)) {t : Fin 14}
    (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ t ∈ supp 14 D (src D (pos i))) :
    J.card ≤ 2 + (ru D b t).card := by
  classical
  have injective : Set.InjOn pos (J : Set (Fin 14)) :=
    fun i hi j hj equal => hpos.2 i (hJ i hi).1 j (hJ j hj).1 equal
  have subset : J.image pos ⊆ sem_W 14 D t := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 he
    exact equality_assigned_mem hpos (hJ i hi).1 (hJ i hi).2
  have lower := Finset.card_le_card subset
  rw [Finset.card_image_of_injOn injective] at lower
  have upper := cc_le h hD b hb t
  omega

theorem equality_assigned_budget_extra {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) (J : Finset (Fin 14)) {t z : Fin 14}
    (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ t ∈ supp 14 D (src D (pos i)))
    (hz : z ∈ eligSet 14 D) (edge : Adj t z) :
    J.card + 1 ≤ 2 + (ru D b t).card := by
  classical
  obtain ⟨H,hHt,hHz,_,_,_⟩ := sem_edge_slots sem_heawood_gr h.1 (sem_heawood_comp hD) edge
  have injective : Set.InjOn pos (J : Set (Fin 14)) :=
    fun i hi j hj equal => hpos.2 i (hJ i hi).1 j (hJ j hj).1 equal
  have fresh : H ∉ J.image pos := by
    intro he
    obtain ⟨i,hi,equal⟩ := Finset.mem_image.1 he
    have same : z = i := as_priv hpos (hJ i hi).1 (equal ▸ hHz)
    exact sem_mem_inelig.1 (hJ i hi).1 (same ▸ hz)
  have subset : insert H (J.image pos) ⊆ sem_W 14 D t := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact hHt
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 he
      exact equality_assigned_mem hpos (hJ i hi).1 (hJ i hi).2
  have lower := Finset.card_le_card subset
  rw [Finset.card_insert_of_notMem fresh,Finset.card_image_of_injOn injective] at lower
  have upper := cc_le h hD b hb t
  omega


theorem equality_three_coordinate_normalize : ∀ M : Finset (Fin 3),
    M.card = 1 ∨ M.card = 2 → ∃ σ : Equiv.Perm (Fin 3),
      M.image σ = {0} ∨ M.image σ = {0,1} := by
  decide +kernel

theorem equality_residual_coordinates {D : Dag} {b : Fin 14 → ℕ}
    (hres : (residualUnits 14 D b).card = 3)
    (h7 : (ru D b 7).card = 1 ∨ (ru D b 7).card = 2) :
    ∃ a : Fin 3 → (Σ _ : ℕ, ℕ), Function.Injective a ∧
      (∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) ∧
      ((Finset.univ.filter (fun k => (7 : Fin 14) ∈ supp 14 D (a k).1)) = {0} ∨
        (Finset.univ.filter (fun k => (7 : Fin 14) ∈ supp 14 D (a k).1)) = {0,1}) := by
  classical
  let S := residualUnits 14 D b
  let e : (↑S) ≃ Fin 3 := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hres)
  let a0 : Fin 3 → (Σ _ : ℕ, ℕ) := fun k => (e.symm k).val
  have inj0 : Function.Injective a0 :=
    fun i j equal => e.symm.injective (Subtype.ext equal)
  have onto0 : ∀ u, u ∈ S ↔ ∃ k, a0 k = u := by
    intro u
    constructor
    · intro hu
      exact ⟨e ⟨u,hu⟩,by simp [a0]⟩
    · rintro ⟨k,rfl⟩
      exact (e.symm k).property
  let M := Finset.univ.filter (fun k => (7 : Fin 14) ∈ supp 14 D (a0 k).1)
  have image : M.image a0 = ru D b 7 := by
    ext u
    constructor
    · rintro hu
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 hu
      exact mem_ru.2 ⟨(onto0 _).2 ⟨k,rfl⟩,(Finset.mem_filter.1 hk).2⟩
    · intro hu
      obtain ⟨hur,hu7⟩ := mem_ru.1 hu
      obtain ⟨k,rfl⟩ := (onto0 u).1 hur
      exact Finset.mem_image.2 ⟨k,Finset.mem_filter.2 ⟨Finset.mem_univ _,hu7⟩,rfl⟩
  have card : M.card = (ru D b 7).card := by
    rw [← image,Finset.card_image_of_injective _ inj0]
  obtain ⟨σ,hσ⟩ := equality_three_coordinate_normalize M (by omega)
  let a : Fin 3 → (Σ _ : ℕ, ℕ) := fun k => a0 (σ.symm k)
  refine ⟨a,inj0.comp σ.symm.injective,?_,?_⟩
  · intro u
    rw [onto0]
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨σ k,by simp [a]⟩
    · rintro ⟨k,rfl⟩
      exact ⟨σ.symm k,rfl⟩
  · have same : Finset.univ.filter (fun k => (7 : Fin 14) ∈ supp 14 D (a k).1) = M.image σ := by
      ext k
      simp only [M,a,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
      constructor
      · intro hk
        exact ⟨σ.symm k,hk,σ.apply_symm_apply k⟩
      · rintro ⟨j,hj,rfl⟩
        simpa using hj
    rw [same]
    exact hσ

noncomputable def equality_coordinate_set {D : Dag}
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (x : Fin 14) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter (fun k => x ∈ supp 14 D (a k).1)

theorem equality_coordinate_image {D : Dag} {b : Fin 14 → ℕ}
    (a : Fin 3 → (Σ _ : ℕ, ℕ))
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) (x : Fin 14) :
    (equality_coordinate_set (D := D) a x).image a = ru D b x := by
  classical
  ext u
  constructor
  · intro hu
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 hu
    exact mem_ru.2 ⟨(onto _).2 ⟨k,rfl⟩,(Finset.mem_filter.1 hk).2⟩
  · intro hu
    obtain ⟨hur,hux⟩ := mem_ru.1 hu
    obtain ⟨k,rfl⟩ := (onto u).1 hur
    exact Finset.mem_image.2 ⟨k,Finset.mem_filter.2 ⟨Finset.mem_univ _,hux⟩,rfl⟩

theorem equality_coordinate_card {D : Dag} {b : Fin 14 → ℕ}
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) (x : Fin 14) :
    (equality_coordinate_set (D := D) a x).card = (ru D b x).card := by
  rw [← equality_coordinate_image a onto x,Finset.card_image_of_injective _ injective]

theorem equality_coordinate_subset {D : Dag} {b : Fin 14 → ℕ}
    (a : Fin 3 → (Σ _ : ℕ, ℕ))
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) (x y : Fin 14) :
    equality_coordinate_set (D := D) a x ⊆ equality_coordinate_set (D := D) a y ↔
      ∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → y ∈ supp 14 D u.1 := by
  classical
  constructor
  · intro sub u hu hx
    obtain ⟨k,rfl⟩ := (onto u).1 hu
    exact (Finset.mem_filter.1 (sub (Finset.mem_filter.2 ⟨Finset.mem_univ _,hx⟩))).2
  · intro inc k hk
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,inc (a k) ((onto _).2 ⟨k,rfl⟩)
      (Finset.mem_filter.1 hk).2⟩


theorem equality_two_assigned_positive {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) {x i j z : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hj : j ∈ ineligSet 14 D)
    (hij : i ≠ j) (hix : Adj i x) (hjx : Adj j x) (hxz : Adj x z)
    (hzi : z ≠ i) (hzj : z ≠ j) : 0 < (ru D b x).card := by
  classical
  obtain ⟨H,hHx,hHz,_,_,_⟩ := sem_edge_slots sem_heawood_gr h.1 (sem_heawood_comp hD) hxz
  have ai := as_mem hpos hi hix
  have aj := as_mem hpos hj hjx
  have ni : H ≠ pos i := fun equal => hzi (as_priv hpos hi (equal ▸ hHz))
  have nj : H ≠ pos j := fun equal => hzj (as_priv hpos hj (equal ▸ hHz))
  have nij : pos i ≠ pos j := fun equal => hij (hpos.2 i hi j hj equal)
  have subset : ({pos i,pos j,H} : Finset (ℕ × Bool)) ⊆ sem_W 14 D x := by
    intro e he
    simp only [Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> assumption
  have lower := Finset.card_le_card subset
  rw [Finset.card_insert_of_notMem (by simp [nij,Ne.symm ni]),
    Finset.card_pair (Ne.symm nj)] at lower
  have upper := cc_le h hD b hb x
  omega



theorem equality_saturated_slot_full {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) (J : Finset (Fin 14)) {x i z : Fin 14}
    (hJ : ∀ j ∈ J, j ∈ ineligSet 14 D ∧ x ∈ supp 14 D (src D (pos j)))
    (hiJ : i ∈ J) (hix : Adj i x) (hz : z ∈ eligSet 14 D) (hxz : Adj x z)
    (saturated : 2 + (ru D b x).card ≤ J.card + 1)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1) :
    ∀ t, t ∈ supp 14 D (src D (pos i)) ↔ Adj i t := by
  classical
  have hi := (hJ i hiJ).1
  obtain ⟨H,hHx,hHz,_,_,_⟩ :=
    sem_edge_slots sem_heawood_gr h.1 (sem_heawood_comp hD) hxz
  have injective : Set.InjOn pos (J : Set (Fin 14)) :=
    fun j hj k hk equal => hpos.2 j (hJ j hj).1 k (hJ k hk).1 equal
  have fresh : H ∉ J.image pos := by
    intro member
    obtain ⟨j,hj,equal⟩ := Finset.mem_image.1 member
    have same : z = j := as_priv hpos (hJ j hj).1 (equal ▸ hHz)
    exact sem_mem_inelig.1 (hJ j hj).1 (same ▸ hz)
  have subset : insert H (J.image pos) ⊆ sem_W 14 D x := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact hHx
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 hp
      exact equality_assigned_mem hpos (hJ j hj).1 (hJ j hj).2
  have code : sem_W 14 D x = insert H (J.image pos) := by
    symm
    apply Finset.eq_of_subset_of_card_le subset
    rw [Finset.card_insert_of_notMem fresh,Finset.card_image_of_injOn injective]
    have upper := cc_le h hD b hb x
    omega
  have full := equality_full_gen_protected h hD hi (as_W h hD hpos hi) hix hprotected
    (fun p hp hne hsub => by
      rw [code] at hp
      rcases Finset.mem_insert.1 hp with rfl | hp
      · have same : z = i := Finset.mem_singleton.1 (hsub (sem_mem_W.1 hHz).2.1)
        exact sem_mem_inelig.1 hi (same ▸ hz)
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 hp
        have member : j ∈ supp 14 D (src D (sem_bar (pos j))) := by
          rw [show src D (sem_bar (pos j)) = src D ((pos j).1,!(pos j).2) from rfl,
            (hpos.1 j (hJ j hj).1).2.2.2]
          exact Finset.mem_singleton_self j
        have same : j = i := Finset.mem_singleton.1 (hsub member)
        exact hne (by rw [same]; rfl))
  simpa only [sem_bar_bar] using full


def equality_m9_line : Fin 6 → Fin 14 := ![7,8,10,13,9,12]

def equality_m9_point : Fin 4 → Fin 14 := ![0,1,2,5]

theorem equality_m9_line_injective : Function.Injective equality_m9_line := by decide +kernel

theorem equality_m9_point_injective : Function.Injective equality_m9_point := by decide +kernel

theorem equality_m9_adjacency : ∀ i : Fin 4, ∀ t : Fin 6,
    t ∈ m9_neighbors i ↔ hc_adjB (equality_m9_point i) (equality_m9_line t) = true := by
  decide +kernel

def equality_m9_cofactor : Fin 6 → List ℕ := ![[2,4,5,6,13,12,8,10,11,9],
  [1,3,4,5,7,13,9,11,12,10],
  [1,2,3,6,13,7,9,12,8,11],
  [0,3,5,6,7,10,8,12,11,9],
  [0,2,3,4,8,7,10,12,13,11],
  [0,1,4,6,7,10,8,13,9,11]]

theorem equality_m9_cf_good : ∀ t : Fin 6,
    cf_good (equality_m9_line t) (equality_m9_cofactor t) := by decide +kernel



theorem equality_m9_ineligible {D : Dag} (hI : ineligSet 14 D = {0,1,2,5,11})
    (i : Fin 4) : equality_m9_point i ∈ ineligSet 14 D := by
  rw [hI]
  exact (by decide +kernel : ∀ i : Fin 4, equality_m9_point i ∈ ({0,1,2,5,11} : Finset (Fin 14))) i

theorem equality_m9_eligible {D : Dag} (hI : ineligSet 14 D = {0,1,2,5,11})
    (t : Fin 6) : equality_m9_line t ∈ eligSet 14 D := by
  by_contra hn
  have hm := hI ▸ sem_mem_inelig.2 hn
  exact (by decide +kernel : ∀ t : Fin 6, equality_m9_line t ∉ ({0,1,2,5,11} : Finset (Fin 14))) t hm

theorem equality_m9_positive {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11}) (t : Fin 6) :
    0 < (ru D b (equality_m9_line t)).card := by
  have geometry : ∀ t : Fin 6, ∃ i j : Fin 4, ∃ z : Fin 14,
      i ≠ j ∧ hc_adjB (equality_m9_point i) (equality_m9_line t) = true ∧
      hc_adjB (equality_m9_point j) (equality_m9_line t) = true ∧
      hc_adjB (equality_m9_line t) z = true ∧
      z ≠ equality_m9_point i ∧ z ≠ equality_m9_point j := by decide +kernel
  obtain ⟨i,j,z,hij,hix,hjx,hxz,hzi,hzj⟩ := geometry t
  exact equality_two_assigned_positive h hD b hb pos hpos (equality_m9_ineligible hI i)
    (equality_m9_ineligible hI j) (fun equal => hij (equality_m9_point_injective equal))
    ((hc_adjB_iff _ _).1 hix) ((hc_adjB_iff _ _).1 hjx) ((hc_adjB_iff _ _).1 hxz) hzi hzj

theorem equality_m9_coordinate_proper {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14) (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) (t : Fin 6) :
    equality_coordinate_set (D := D) a (equality_m9_line t) ≠ Finset.univ := by
  classical
  intro full
  have hall : ∀ u ∈ residualUnits 14 D b, equality_m9_line t ∈ supp 14 D u.1 := by
    intro u hu
    obtain ⟨k,rfl⟩ := (onto u).1 hu
    have member : k ∈ equality_coordinate_set (D := D) a (equality_m9_line t) := by
      rw [full]; exact Finset.mem_univ _
    exact (Finset.mem_filter.1 member).2
  let X := (Finset.univ.erase t).image equality_m9_line
  have hx : ∀ x ∈ X, x ∈ eligSet 14 D ∧ x ≠ equality_m9_line t ∧
      (∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → equality_m9_line t ∈ supp 14 D u.1) ∧
      ∃ w, x ∈ supp 14 D w ∧ equality_m9_line t ∈ supp 14 D w := by
    intro x hx
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨u,hu⟩ := Finset.card_pos.1 (equality_m9_positive h hD b hb pos hpos hI s)
    obtain ⟨hur,hux⟩ := mem_ru.1 hu
    exact ⟨equality_m9_eligible hI s,
      fun eq => (Finset.mem_erase.1 hs).1 (equality_m9_line_injective eq),
      fun u hu _ => hall u hu,u.1,hux,hall u hur⟩
  have bound := cf_six h hD b hb (equality_m9_cf_good t) (equality_m9_eligible hI t) X hx
  have Xcard : X.card = 5 := by
    rw [Finset.card_image_of_injective _ equality_m9_line_injective]
    simp
  have card := equality_coordinate_card a injective onto (equality_m9_line t)
  rw [full,Finset.card_univ,Fintype.card_fin] at card
  rw [Xcard] at bound
  omega

theorem equality_m9_forced_mem {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (a : Fin 3 → (Σ _ : ℕ, ℕ))
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    (α β : Fin 3)
    (extra2 : equality_m9_line (m9_extra2 α) ∈ supp 14 D (src D (pos 2)))
    (extra5 : equality_m9_line (m9_extra5 β) ∈ supp 14 D (src D (pos 5)))
    (i : Fin 4) (t : Fin 6)
    (ht : t ∈ m9_forced (fun s => equality_coordinate_set (D := D) a (equality_m9_line s)) α β i) :
    equality_m9_line t ∈ supp 14 D (src D (pos (equality_m9_point i))) := by
  classical
  rcases (Finset.mem_filter.1 ht).2 with ⟨x,hx,subset⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have inclusion := (equality_coordinate_subset a onto (equality_m9_line x)
      (equality_m9_line t)).1 subset
    obtain ⟨u,hu⟩ := Finset.card_pos.1 (equality_m9_positive h hD b hb pos hpos hI x)
    obtain ⟨hur,hux⟩ := mem_ru.1 hu
    exact equality_residual_co_label h hD b hb pos hpos (equality_m9_eligible hI x)
      (equality_m9_eligible hI t) (equality_m9_ineligible hI i)
      ((hc_adjB_iff _ _).1 ((equality_m9_adjacency i x).1 hx)) inclusion
      ⟨u.1,hux,inclusion u hur hux⟩
  · exact extra2
  · exact extra5



theorem equality_m9_range : Finset.univ.image equality_m9_line = mx_L := by decide +kernel

theorem equality_m9_neighbors_image : ∀ i : Fin 4,
    (m9_neighbors i).image equality_m9_line = sem_hw_nb (equality_m9_point i) := by
  decide +kernel

theorem equality_m9_mask_image {D : Dag} (a : Fin 3 → (Σ _ : ℕ, ℕ)) (k : Fin 3) :
    (m9_unit_support (fun t => equality_coordinate_set (D := D) a (equality_m9_line t)) k).image
      equality_m9_line = supp 14 D (a k).1 ∩ mx_L := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.1 hx
    refine Finset.mem_inter.2 ⟨(Finset.mem_filter.1 ((Finset.mem_filter.1 ht).2)).2,?_⟩
    rw [← equality_m9_range]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · intro hx
    obtain ⟨hs,hp⟩ := Finset.mem_inter.1 hx
    rw [← equality_m9_range] at hp
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.1 hp
    exact Finset.mem_image.2 ⟨t,Finset.mem_filter.2 ⟨Finset.mem_univ _,
      Finset.mem_filter.2 ⟨Finset.mem_univ _,hs⟩⟩,rfl⟩

theorem equality_m9_unit_missing {D : Dag} (a : Fin 3 → (Σ _ : ℕ, ℕ))
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5)) (k : Fin 3) :
    m9_unit_support (fun t => equality_coordinate_set (D := D) a (equality_m9_line t)) k ≠
      m9_neighbors 2 ∧
    m9_unit_support (fun t => equality_coordinate_set (D := D) a (equality_m9_line t)) k ≠
      m9_neighbors 3 := by
  constructor
  · intro equal
    apply missing2
    refine ⟨(a k).1,?_⟩
    rw [← equality_m9_mask_image a k,equal,equality_m9_neighbors_image]
    rfl
  · intro equal
    apply missing5
    refine ⟨(a k).1,?_⟩
    rw [← equality_m9_mask_image a k,equal,equality_m9_neighbors_image]
    rfl

theorem equality_m9_assigned_extra {D : Dag} (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) (hI : ineligSet 14 D = {0,1,2,5,11})
    (i : Fin 4) (missing : ¬ sup_Occ 14 D mx_L (sem_hw_nb (equality_m9_point i))) :
    ∃ t : Fin 6, t ∉ m9_neighbors i ∧
      equality_m9_line t ∈ supp 14 D (src D (pos (equality_m9_point i))) := by
  classical
  by_contra hn
  apply missing
  refine ⟨src D (pos (equality_m9_point i)),?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hs,hp⟩ := Finset.mem_inter.1 hx
    rw [← equality_m9_range] at hp
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.1 hp
    have ht : t ∈ m9_neighbors i := by
      by_contra no
      exact hn ⟨t,no,hs⟩
    rw [← equality_m9_neighbors_image i]
    exact Finset.mem_image_of_mem _ ht
  · intro hx
    refine Finset.mem_inter.2 ⟨(hpos.1 _ (equality_m9_ineligible hI i)).2.2.1 x
      (hw_mem_nb.1 hx),?_⟩
    rw [← equality_m9_neighbors_image i] at hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.1 hx
    rw [← equality_m9_range]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem equality_m9_extras {D : Dag} (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) (hI : ineligSet 14 D = {0,1,2,5,11})
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5)) :
    ∃ α β : Fin 3,
      equality_m9_line (m9_extra2 α) ∈ supp 14 D (src D (pos 2)) ∧
      equality_m9_line (m9_extra5 β) ∈ supp 14 D (src D (pos 5)) := by
  obtain ⟨t,ht,hmem⟩ := equality_m9_assigned_extra pos hpos hI 2 missing2
  obtain ⟨s,hs,hmem'⟩ := equality_m9_assigned_extra pos hpos hI 3 missing5
  have g2 : ∀ t : Fin 6, t ∉ m9_neighbors 2 → ∃ α : Fin 3, m9_extra2 α = t := by decide +kernel
  have g5 : ∀ t : Fin 6, t ∉ m9_neighbors 3 → ∃ β : Fin 3, m9_extra5 β = t := by decide +kernel
  obtain ⟨α,rfl⟩ := g2 t ht
  obtain ⟨β,rfl⟩ := g5 s hs
  exact ⟨α,β,hmem,hmem'⟩



theorem equality_m9_extra_neighbor {D : Dag} (hI : ineligSet 14 D = {0,1,2,5,11})
    (t : Fin 6) : ∃ z : Fin 14, z ∈ eligSet 14 D ∧ Adj (equality_m9_line t) z := by
  have geo : ∀ t : Fin 6, ∃ z : Fin 14,
      z ∉ ({0,1,2,5,11} : Finset (Fin 14)) ∧ hc_adjB (equality_m9_line t) z = true := by
    decide +kernel
  obtain ⟨z,hz,edge⟩ := geo t
  refine ⟨z,?_,(hc_adjB_iff _ _).1 edge⟩
  by_contra hn
  exact hz (hI ▸ sem_mem_inelig.2 hn)

theorem equality_m9_consumer_budget {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    (α β : Fin 3)
    (extra2 : equality_m9_line (m9_extra2 α) ∈ supp 14 D (src D (pos 2)))
    (extra5 : equality_m9_line (m9_extra5 β) ∈ supp 14 D (src D (pos 5))) (t : Fin 6) :
    (m9_consumers (fun s => equality_coordinate_set (D := D) a (equality_m9_line s)) α β t).card ≤
      1 + (equality_coordinate_set (D := D) a (equality_m9_line t)).card := by
  classical
  let r := fun s => equality_coordinate_set (D := D) a (equality_m9_line s)
  let J := (m9_consumers r α β t).image equality_m9_point
  have hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧
      equality_m9_line t ∈ supp 14 D (src D (pos i)) := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 hi
    exact ⟨equality_m9_ineligible hI j,
      equality_m9_forced_mem h hD b hb pos hpos hI a onto α β extra2 extra5 j t
        (Finset.mem_filter.1 hj).2⟩
  obtain ⟨z,hz,edge⟩ := equality_m9_extra_neighbor hI t
  have budget := equality_assigned_budget_extra h hD b hb pos hpos J hJ hz edge
  have card : J.card = (m9_consumers r α β t).card :=
    Finset.card_image_of_injective _ equality_m9_point_injective
  have rcard := equality_coordinate_card a injective onto (equality_m9_line t)
  rw [card,← rcard] at budget
  dsimp [r] at budget
  omega

theorem equality_m9_saturated_full {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (hprotected : ∀ i ∈ ({0,1} : Finset (Fin 14)), ∀ w,
      Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1)
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    (α β : Fin 3)
    (extra2 : equality_m9_line (m9_extra2 α) ∈ supp 14 D (src D (pos 2)))
    (extra5 : equality_m9_line (m9_extra5 β) ∈ supp 14 D (src D (pos 5)))
    (i : Fin 2)
    (saturated : m9_saturated (fun s => equality_coordinate_set (D := D) a (equality_m9_line s)) α β i) :
    ∀ v, v ∈ supp 14 D (src D (pos (equality_m9_point (m9_protected i)))) ↔
      Adj (equality_m9_point (m9_protected i)) v := by
  classical
  let r := fun s => equality_coordinate_set (D := D) a (equality_m9_line s)
  obtain ⟨x,hx,sat⟩ := saturated
  let J := (m9_consumers r α β x).image equality_m9_point
  have hJ : ∀ j ∈ J, j ∈ ineligSet 14 D ∧
      equality_m9_line x ∈ supp 14 D (src D (pos j)) := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 hj
    exact ⟨equality_m9_ineligible hI k,
      equality_m9_forced_mem h hD b hb pos hpos hI a onto α β extra2 extra5 k x
        (Finset.mem_filter.1 hk).2⟩
  have hiJ : equality_m9_point (m9_protected i) ∈ J := by
    refine Finset.mem_image.2 ⟨m9_protected i,Finset.mem_filter.2 ⟨Finset.mem_univ _,?_⟩,rfl⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,Or.inl ⟨x,hx,Finset.Subset.refl _⟩⟩
  have card : J.card = (m9_consumers r α β x).card :=
    Finset.card_image_of_injective _ equality_m9_point_injective
  have rcard := equality_coordinate_card a injective onto (equality_m9_line x)
  obtain ⟨z,hz,edge⟩ := equality_m9_extra_neighbor hI x
  apply equality_saturated_slot_full h hD b hb pos hpos J hJ hiJ
    ((hc_adjB_iff _ _).1 ((equality_m9_adjacency (m9_protected i) x).1 hx)) hz edge
  · rw [card]
    change (m9_consumers r α β x).card = 1 + (r x).card at sat
    change (r x).card = (ru D b (equality_m9_line x)).card at rcard
    omega
  · exact hprotected _ ((by decide +kernel : ∀ i : Fin 2,
      equality_m9_point (m9_protected i) ∈ ({0,1} : Finset (Fin 14))) i)

theorem equality_m9_constraints {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14) (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5))
    (hprotected : ∀ i ∈ ({0,1} : Finset (Fin 14)), ∀ w,
      Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1)
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    (α β : Fin 3)
    (extra2 : equality_m9_line (m9_extra2 α) ∈ supp 14 D (src D (pos 2)))
    (extra5 : equality_m9_line (m9_extra5 β) ∈ supp 14 D (src D (pos 5))) :
    m9_constraints (fun t => equality_coordinate_set (D := D) a (equality_m9_line t)) α β := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · intro t
    refine ⟨Finset.card_pos.1 ?_,equality_m9_coordinate_proper h hD h14 b hb pos hpos hI a injective onto t⟩
    rw [equality_coordinate_card a injective onto]
    exact equality_m9_positive h hD b hb pos hpos hI t
  · exact equality_m9_unit_missing a missing2 missing5
  · exact equality_m9_consumer_budget h hD b hb pos hpos hI a injective onto α β extra2 extra5
  · intro i saturated t ht
    have full := equality_m9_saturated_full h hD b hb pos hpos hI hprotected a injective onto
      α β extra2 extra5 i saturated
    have mem := equality_m9_forced_mem h hD b hb pos hpos hI a onto α β extra2 extra5
      (m9_protected i) t ht
    exact (equality_m9_adjacency _ _).2 ((hc_adjB_iff _ _).2 ((full _).1 mem))



theorem equality_m9_point_eligible {D : Dag} (hI : ineligSet 14 D = {0,1,2,5,11})
    {z : Fin 14} (hz : z ∈ ({3,4,6} : Finset (Fin 14))) : z ∈ eligSet 14 D := by
  by_contra hn
  exact Finset.disjoint_left.1
    (by decide : Disjoint ({3,4,6} : Finset (Fin 14)) {0,1,2,5,11}) hz
    (hI ▸ sem_mem_inelig.2 hn)

theorem equality_m9_point_forced_mem {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (a : Fin 3 → (Σ _ : ℕ, ℕ))
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    {z : Fin 14} (hz : z ∈ ({3,4,6} : Finset (Fin 14))) (i : Fin 4)
    (hi : i ∈ m9_point_forced (fun s => equality_coordinate_set (D := D) a (equality_m9_line s))
      (equality_coordinate_set (D := D) a z)) :
    z ∈ supp 14 D (src D (pos (equality_m9_point i))) := by
  classical
  obtain ⟨x,hx,subset⟩ := (Finset.mem_filter.1 hi).2
  have inclusion := (equality_coordinate_subset a onto (equality_m9_line x) z).1 subset
  obtain ⟨u,hu⟩ := Finset.card_pos.1 (equality_m9_positive h hD b hb pos hpos hI x)
  obtain ⟨hur,hux⟩ := mem_ru.1 hu
  exact equality_residual_co_label h hD b hb pos hpos (equality_m9_eligible hI x)
    (equality_m9_point_eligible hI hz) (equality_m9_ineligible hI i)
    ((hc_adjB_iff _ _).1 ((equality_m9_adjacency i x).1 hx)) inclusion
    ⟨u.1,hux,inclusion u hur hux⟩

theorem equality_m9_point_constraints {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (hprotected : ∀ i ∈ ({0,1} : Finset (Fin 14)), ∀ w,
      Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1)
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    (α β : Fin 3)
    (extra2 : equality_m9_line (m9_extra2 α) ∈ supp 14 D (src D (pos 2)))
    (extra5 : equality_m9_line (m9_extra5 β) ∈ supp 14 D (src D (pos 5)))
    {z : Fin 14} (hz : z ∈ ({3,4,6} : Finset (Fin 14)))
    (positive : (equality_coordinate_set (D := D) a z).Nonempty) :
    m9_point_constraints (fun t => equality_coordinate_set (D := D) a (equality_m9_line t))
      α β (equality_coordinate_set (D := D) a z) := by
  classical
  let r := fun t => equality_coordinate_set (D := D) a (equality_m9_line t)
  let T := equality_coordinate_set (D := D) a z
  have hi11 : (11 : Fin 14) ∈ ineligSet 14 D := by rw [hI]; decide
  have edge11 : Adj 11 z := (hc_adjB_iff _ _).1
    ((by decide +kernel : ∀ z ∈ ({3,4,6} : Finset (Fin 14)), hc_adjB 11 z = true) z hz)
  have no11 : ∀ J : Finset (Fin 4), (11 : Fin 14) ∉ J.image equality_m9_point := by
    intro J member
    obtain ⟨i,_,eq⟩ := Finset.mem_image.1 member
    exact (by decide +kernel : ∀ i : Fin 4, equality_m9_point i ≠ (11 : Fin 14)) i eq
  refine ⟨positive,?_,?_,?_⟩
  · intro i saturated forced
    have full := equality_m9_saturated_full h hD b hb pos hpos hI hprotected a injective onto
      α β extra2 extra5 i saturated
    have mem := equality_m9_point_forced_mem h hD b hb pos hpos hI a onto hz (m9_protected i) forced
    have edge := (full z).1 mem
    have no := (by decide +kernel : ∀ i : Fin 2, ∀ z ∈ ({3,4,6} : Finset (Fin 14)),
      hc_adjB (equality_m9_point (m9_protected i)) z = false) i z hz
    have yes := (hc_adjB_iff _ _).2 edge
    rw [no] at yes
    exact Bool.false_ne_true yes
  · let J := (m9_point_forced r T).image equality_m9_point
    have hJ : ∀ i ∈ insert 11 J, i ∈ ineligSet 14 D ∧ z ∈ supp 14 D (src D (pos i)) := by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact ⟨hi11,(hpos.1 11 hi11).2.2.1 z edge11⟩
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 hi
        exact ⟨equality_m9_ineligible hI j,
          equality_m9_point_forced_mem h hD b hb pos hpos hI a onto hz j hj⟩
    have geo : ∀ z ∈ ({3,4,6} : Finset (Fin 14)), ∃ t : Fin 6,
        hc_adjB z (equality_m9_line t) = true := by decide +kernel
    obtain ⟨t,edge⟩ := geo z hz
    have bound := equality_assigned_budget_extra h hD b hb pos hpos (insert 11 J) hJ
      (equality_m9_eligible hI t) ((hc_adjB_iff _ _).1 edge)
    have card : J.card = (m9_point_forced r T).card :=
      Finset.card_image_of_injective _ equality_m9_point_injective
    rw [Finset.card_insert_of_notMem (no11 _),card] at bound
    have tc := equality_coordinate_card a injective onto z
    change T.card = (ru D b z).card at tc
    change (m9_point_forced r T).card ≤ T.card
    omega
  · intro t
    by_cases inclusion : T ⊆ r t
    · let J := (m9_consumers r α β t).image equality_m9_point
      have inc := (equality_coordinate_subset a onto z (equality_m9_line t)).1 inclusion
      obtain ⟨k,hk⟩ := positive
      have huz : z ∈ supp 14 D (a k).1 := (Finset.mem_filter.1 hk).2
      have hur : a k ∈ residualUnits 14 D b := (onto _).2 ⟨k,rfl⟩
      have line11 := equality_residual_co_label h hD b hb pos hpos
        (equality_m9_point_eligible hI hz) (equality_m9_eligible hI t) hi11 edge11 inc
        ⟨(a k).1,huz,inc (a k) hur huz⟩
      have hJ : ∀ i ∈ insert 11 J, i ∈ ineligSet 14 D ∧
          equality_m9_line t ∈ supp 14 D (src D (pos i)) := by
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact ⟨hi11,line11⟩
        · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 hi
          exact ⟨equality_m9_ineligible hI j,
            equality_m9_forced_mem h hD b hb pos hpos hI a onto α β extra2 extra5 j t
              (Finset.mem_filter.1 hj).2⟩
      obtain ⟨z',hz',edge⟩ := equality_m9_extra_neighbor hI t
      have bound := equality_assigned_budget_extra h hD b hb pos hpos (insert 11 J) hJ hz' edge
      have card : J.card = (m9_consumers r α β t).card :=
        Finset.card_image_of_injective _ equality_m9_point_injective
      rw [Finset.card_insert_of_notMem (no11 _),card] at bound
      have rc := equality_coordinate_card a injective onto (equality_m9_line t)
      change (r t).card = (ru D b (equality_m9_line t)).card at rc
      change (m9_consumers r α β t).card + (if T ⊆ r t then 1 else 0) ≤ 1 + (r t).card
      rw [ite_eq_left inclusion]
      omega
    · have bound := equality_m9_consumer_budget h hD b hb pos hpos hI a injective onto
        α β extra2 extra5 t
      change (m9_consumers r α β t).card + (if T ⊆ r t then 1 else 0) ≤ 1 + (r t).card
      rw [ite_eq_right inclusion,Nat.add_zero]
      exact bound



theorem equality_m9_all_constraints {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14) (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5))
    (hprotected : ∀ i ∈ ({0,1} : Finset (Fin 14)), ∀ w,
      Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1)
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) :
    ∃ α β : Fin 3,
      m9_constraints (fun t => equality_coordinate_set (D := D) a (equality_m9_line t)) α β ∧
      ∀ z ∈ ({3,4,6} : Finset (Fin 14)), (equality_coordinate_set (D := D) a z).Nonempty →
        m9_point_constraints (fun t => equality_coordinate_set (D := D) a (equality_m9_line t))
          α β (equality_coordinate_set (D := D) a z) := by
  obtain ⟨pos,hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  obtain ⟨α,β,e2,e5⟩ := equality_m9_extras pos hpos hI missing2 missing5
  refine ⟨α,β,equality_m9_constraints h hD h14 b hb pos hpos hI missing2 missing5
    hprotected a injective onto α β e2 e5,?_⟩
  intro z hz positive
  exact equality_m9_point_constraints h hD b hb pos hpos hI hprotected a injective onto
    α β e2 e5 hz positive



lemma single_reader_path_le {n : ℕ} {D : Dag} (hS : Strict n D) {a b : ℕ}
    (path : Relation.ReflTransGen (sem_step n D) a b) : a ≤ b := by
  induction path with
  | refl => rfl
  | tail path step ih => exact Nat.le_trans ih (Nat.le_of_lt (sem_step_lt hS step))

lemma single_reader_chain_le {n : ℕ} {D : Dag} (hS : Strict n D) {a b : ℕ}
    (path : sem_Chain n D a b) : a ≤ b :=
  single_reader_path_le hS (sem_rtg_mono (fun _ _ h => h.1) path)

lemma single_reader_other_unreachable {n : ℕ} {D : Dag} (hS : Strict n D)
    {v a b c : ℕ} (chain : sem_Chain n D v a)
    (last : sem_step n D a b) (one : fanout D a = 1)
    (other : sem_step n D c b) (different : c ≠ a) :
    ¬ Relation.ReflTransGen (sem_step n D) v c := by
  induction chain using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro reach
    rcases Relation.ReflTransGen.cases_head reach with equal | ⟨z,first,rest⟩
    · exact different equal.symm
    · have same : b = z := sem_step_unique last first one
      have le := single_reader_path_le hS rest
      have lt := sem_step_lt hS other
      omega
  | @head start next first rest ih =>
    intro reach
    rcases Relation.ReflTransGen.cases_head reach with equal | ⟨z,initial,remaining⟩
    · have direct : sem_step n D start b := by simpa [equal] using other
      have same : next = b := sem_step_unique first.1 direct first.2
      have le := single_reader_chain_le hS rest
      have lt := sem_step_lt hS last
      omega
    · have same : next = z := sem_step_unique first.1 initial first.2
      subst z
      exact ih remaining

lemma single_reader_chain_hits {n : ℕ} {D : Dag} (hS : Strict n D)
    {a b : ℕ} (chain : sem_Chain n D a b) (P : ℕ → Prop) :
    ∀ w, Relation.ReflTransGen (fun u v => sem_step n D u v ∧ P v) a w →
      P a → b ≤ w → P b := by
  induction chain using Relation.ReflTransGen.head_induction_on with
  | refl => intro w path start bound; exact start
  | @head a next step rest ih =>
    intro w path start bound
    rcases Relation.ReflTransGen.cases_head path with equal | ⟨z,first,remaining⟩
    · have increasing := sem_step_lt hS step.1
      have restLe := single_reader_chain_le hS rest
      omega
    · have same : next = z := sem_step_unique step.1 first.1 step.2
      subst z
      exact ih w remaining first.2 bound

lemma single_reader_chain_agreement {n : ℕ} {D : Dag} (hS : Strict n D)
    (x y : Fin n → Bool) (i : Fin n) (agree : ∀ k, k ≠ i → x k = y k)
    {a w : ℕ} (chain : sem_Chain n D i.val a) (bound : a ≤ w)
    (same : val D x a = val D y a) : val D x w = val D y w := by
  by_contra changed
  have inputChanged : x i ≠ y i := by
    intro hi
    have equal : x = y := by
      funext k
      by_cases hk : k = i
      · simpa only [hk] using hi
      · exact agree k hk
    exact changed (congrArg (fun z => val D z w) equal)
  have firstChanged : val D x i.val ≠ val D y i.val := by
    simpa only [val_input D x i.val i.isLt,val_input D y i.val i.isLt] using inputChanged
  exact (single_reader_chain_hits hS chain (fun z => val D x z ≠ val D y z)
    w (sem_changed_path hS x y i agree w changed) firstChanged bound) same

lemma ineligible_consumption_insert_false {n : ℕ} {D : Dag} (hS : Strict n D)
    (i c : Fin n) (hi : i ∈ ineligSet n D) (e : ℕ × Bool)
    (he : e ∈ sem_W n D i) (absent : c ∉ supp n D (src D (sem_bar e)))
    (w : ℕ) (bound : n + e.1 ≤ w) (absentW : c ∉ supp n D w) :
    val D (sem_ins i (single c)) w = false := by
  obtain ⟨hj,carrier,_⟩ := sem_mem_W.mp he
  have chain : sem_Chain n D i.val (src D e) := sem_inelig_chain hS hi carrier
  have step : sem_step n D (src D e) (n+e.1) := sem_step_src hj e.2
  have one : fanout D (src D e) = 1 := by
    have lower := sem_step_fanout step
    have upper := mem_ineligSet.mp hi (src D e) carrier
    omega
  have otherSame : val D (single c) (src D (sem_bar e)) =
      val D (sem_ins i (single c)) (src D (sem_bar e)) := by
    by_contra changed
    have reach := sem_rtg_mono (fun _ _ h => h.1)
      (sem_changed_path hS (single c) (sem_ins i (single c)) i
        (sem_ins_agree i (single c)) _ changed)
    exact single_reader_other_unreachable hS chain step one
      (sem_step_src hj (!e.2)) (sem_src_ne hS hj e.2).symm reach
  have otherFalse : val D (single c) (src D (sem_bar e)) = false := by
    cases hv : val D (single c) (src D (sem_bar e)) with
    | false => rfl
    | true => exact False.elim (absent (mem_supp.mpr hv))
  have gateFalse (z : Fin n → Bool) (hz : val D z (src D (sem_bar e)) = false) :
      val D z (n+e.1) = false := by
    rw [val_gate hS z e.1 hj,sem_W_and hS he]
    cases hs : e.2 <;> simp [sem_bar,src,hs] at hz <;> simp [gop,hz]
  have sameGate : val D (single c) (n+e.1) = val D (sem_ins i (single c)) (n+e.1) :=
    (gateFalse _ otherFalse).trans (gateFalse _ (otherSame.symm.trans otherFalse)).symm
  have sameW := single_reader_chain_agreement hS (single c) (sem_ins i (single c)) i
    (sem_ins_agree i (single c)) (Relation.ReflTransGen.tail chain ⟨step,one⟩) bound sameGate
  have baseFalse : val D (single c) w = false := by
    cases hv : val D (single c) w with
    | false => rfl
    | true => exact False.elim (absentW (mem_supp.mpr hv))
  exact sameW.symm.trans baseFalse

theorem pilot_nonedge_extension :
    ∀ u v i : Fin 14, hc_adjB u v = false → i ≠ u → i ≠ v →
      ∃ z : Fin 14, hc_adjB i z = true ∧ hc_adjB u z = false ∧ hc_adjB v z = false := by
  decide +kernel

theorem pilot_chain_nonedge_pair_false {D : Dag} (hS : Strict 14 D) (hD : Correct D)
    {i u v : Fin 14} {w : ℕ} (chain : sem_Chain 14 D i.val w)
    (huv : ¬ Adj u v) (hiu : i ≠ u) (hiv : i ≠ v) :
    val D (sem_ind ({u,v} : Finset (Fin 14))) w = false := by
  obtain ⟨z,hiz,huz,hvz⟩ := pilot_nonedge_extension u v i
    (sem_adjB_false.2 huv) hiu hiv
  have hiz' := (hc_adjB_iff _ _).1 hiz
  have huz' := sem_adjB_false.1 huz
  have hvz' := sem_adjB_false.1 hvz
  have independent : ∀ a ∈ ({u,v,z} : Finset (Fin 14)),
      ∀ b ∈ ({u,v,z} : Finset (Fin 14)), ¬ Adj a b := by
    intro a ha b hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact adj_irrefl _
    · exact huv
    · exact huz'
    · exact fun h => huv (adj_symm h)
    · exact adj_irrefl _
    · exact hvz'
    · exact fun h => huz' (adj_symm h)
    · exact fun h => hvz' (adj_symm h)
    · exact adj_irrefl _
  have negative := sem_ind_no_edge independent
  have positive : sem_Edge Adj (sem_ins i (sem_ind ({u,v,z} : Finset (Fin 14)))) := by
    refine ⟨i,z,hiz',sem_ins_self _ _,sem_ins_ge _ _ z ?_⟩
    simp [sem_ind]
  have branch_false := (sem_dom_split hS (sem_heawood_comp hD)
    (sem_ind ({u,v,z} : Finset (Fin 14))) i w (sem_chain_dom hS chain)
    negative positive).1
  have monotone : ∀ k : Fin 14, sem_ind ({u,v} : Finset (Fin 14)) k = true →
      sem_ind ({u,v,z} : Finset (Fin 14)) k = true := by
    intro k hk
    simp only [sem_ind,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] at hk ⊢
    rcases hk with rfl | rfl <;> simp
  cases value : val D (sem_ind ({u,v} : Finset (Fin 14))) w with
  | false => rfl
  | true =>
    have bad := val_mono hS _ _ monotone w value
    rw [branch_false] at bad
    exact Bool.noConfusion bad

theorem equality_consumption_before_branch {n : ℕ} {D : Dag} (hS : Strict n D)
    {i : Fin n} (hi : i ∈ ineligSet n D) {e : ℕ × Bool} (he : e ∈ sem_W n D i)
    {b : ℕ} (chain : sem_Chain n D i.val b) (branch : 2 ≤ fanout D b) : n+e.1 ≤ b := by
  obtain ⟨hj,carrier,_⟩ := sem_mem_W.1 he
  have first := sem_inelig_chain hS hi carrier
  have step : sem_step n D (src D e) (n+e.1) := sem_step_src hj e.2
  have one : fanout D (src D e) = 1 := by
    have lower := sem_step_fanout step
    have upper := mem_ineligSet.mp hi _ carrier
    omega
  rcases sem_chain_fork hS first (sem_rtg_mono (fun _ _ h => h.1) chain) with path | ⟨path,ne⟩
  · rcases Relation.ReflTransGen.cases_head path with equal | ⟨w,initial,rest⟩
    · have same := congrArg (fanout D) equal
      omega
    · have equal : n+e.1 = w := sem_step_unique step initial one
      subst w
      exact sem_rtg_le hS (fun _ _ h => h) rest
  · rcases Relation.ReflTransGen.cases_head path with equal | ⟨w,initial,rest⟩
    · exact False.elim (ne equal)
    · have := initial.2
      omega

theorem equality_cf_singleton_pair {c : Fin 14} {l : List ℕ} (hgood : cf_good c l)
    (k : Fin 10) : cof_ext (cf_rho c) (cf_iota l) (single k) =
      sem_ind ({c,cf_iota l k} : Finset (Fin 14)) := by
  have hok : cof_Ok (cf_rho c) (cf_iota l) := ⟨hgood.1,hgood.2.1⟩
  funext u
  have fixed : cf_rho c u = some true ↔ u = c := by
    by_cases equal : u = c <;> simp [cf_rho,equal]
  have support := cof_ext_single hok k u
  rw [fixed] at support
  have other : sem_ind ({c,cf_iota l k} : Finset (Fin 14)) u = true ↔
      u = cf_iota l k ∨ u = c := by simp [sem_ind,or_comm]
  cases first : cof_ext (cf_rho c) (cf_iota l) (single k) u <;>
    cases second : sem_ind ({c,cf_iota l k} : Finset (Fin 14)) u <;> simp_all

theorem equality_cofactor_empty_branch_empty {D : Dag} (hS : Strict 14 D)
    (hD : Correct D) {c i : Fin 14} {l : List ℕ} (hgood : cf_good c l)
    (hi : i ∈ ineligSet 14 D) (hic : i ≠ c) {e : ℕ × Bool} (he : e ∈ sem_W 14 D i)
    (absent : c ∉ supp 14 D (src D (sem_bar e))) {b : ℕ}
    (chain : sem_Chain 14 D i.val b) (branch : 2 ≤ fanout D b) (empty : supp 14 D b = ∅) :
    cof_supp D (cf_rho c) (cf_iota l) b = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.2
  intro k member
  have value := cof_mem_supp.1 member
  rw [equality_cf_singleton_pair hgood k] at value
  by_cases equal : cf_iota l k = i
  · rw [equal] at value
    have assignment : sem_ind ({c,i} : Finset (Fin 14)) = sem_ins i (single c) := by
      funext u
      by_cases hu : u = i <;> simp [sem_ind,sem_ins,single,hu]
    rw [assignment] at value
    have zero := ineligible_consumption_insert_false hS i c hi e he absent b
      (equality_consumption_before_branch hS hi he chain branch) (by rw [empty]; simp)
    rw [zero] at value
    exact Bool.false_ne_true value
  · have free : cf_rho c (cf_iota l k) = none := (hgood.2.1 _).2 ⟨k,rfl⟩
    have distinct : cf_iota l k ≠ c := by
      intro same
      simpa [same,cf_rho] using free
    have nonedge : ¬ Adj c (cf_iota l k) := by
      intro adjacent
      rw [cf_rho,if_neg distinct,if_pos ((hc_adjB_iff _ _).2 adjacent)] at free
      cases free
    have zero := pilot_chain_nonedge_pair_false hS hD chain nonedge hic (Ne.symm equal)
    rw [zero] at value
    exact Bool.false_ne_true value



theorem equality_critical_branch_false {n : ℕ} {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (v : Fin n) {b : ℕ}
    (chain : sem_Chain n D v.val b)
    (hfalse : val D x (outW n D) = false)
    (htrue : val D (sem_ins v x) (outW n D) = true) : val D x b = false := by
  cases hb : val D x b with
  | false => rfl
  | true =>
    have hb' : val D (sem_ins v x) b = true :=
      val_mono hS x (sem_ins v x)
        (by intro i hi; by_cases h : i = v <;> simp_all [sem_ins]) b hb
    have same := sem_dom_eq hS x (sem_ins v x) v
      (fun k hk => by simp [sem_ins,hk]) b (sem_chain_dom hS chain) (hb.trans hb'.symm)
    rw [hfalse,htrue] at same
    exact Bool.noConfusion same

theorem equality_cofactor_neighbor_branch_empty {D : Dag} (h : StrictLive 14 D)
    (hD : Correct D) {c z : Fin 14} {l : List ℕ} (hgood : cf_good c l)
    (edge : Adj c z) {b : ℕ} (chain : sem_Chain 14 D z.val b) :
    cof_supp D (cf_rho c) (cf_iota l) b = ∅ := by
  classical
  have hC := sem_heawood_comp hD
  have hok : cof_Ok (cf_rho c) (cf_iota l) := ⟨hgood.1,hgood.2.1⟩
  have truefixed (u : Fin 14) : cf_rho c u = some true ↔ u = c := by
    by_cases equal : u = c
    · simp [cf_rho,equal]
    · simp [cf_rho,equal]
  apply Finset.eq_empty_iff_forall_notMem.2
  intro i member
  let base := cof_ext (cf_rho c) (cf_iota l) (single i)
  have supported (u : Fin 14) : base u = true ↔ u = cf_iota l i ∨ u = c := by
    rw [show base u = cof_ext (cf_rho c) (cf_iota l) (single i) u from rfl,
      cof_ext_single hok,truefixed]
  have free : cf_rho c (cf_iota l i) = none := (hgood.2.1 _).2 ⟨i,rfl⟩
  have distinct : cf_iota l i ≠ c := by
    intro equal
    simpa [equal,cf_rho] using free
  have nonedge : ¬ Adj c (cf_iota l i) := by
    intro adjacent
    rw [cf_rho,if_neg distinct,if_pos ((hc_adjB_iff _ _).2 adjacent)] at free
    cases free
  have zero : val D base (outW 14 D) = false := by
    cases value : val D base (outW 14 D) with
    | false => rfl
    | true =>
      obtain ⟨u,v,adjacent,hu,hv⟩ := (hC base).1 value
      rcases (supported u).1 hu with rfl | rfl <;>
        rcases (supported v).1 hv with rfl | rfl
      · exact (adj_irrefl _ adjacent).elim
      · exact (nonedge (adj_symm adjacent)).elim
      · exact (nonedge adjacent).elim
      · exact (adj_irrefl _ adjacent).elim
  have after : val D (sem_ins z base) (outW 14 D) = true := by
    apply (hC _).2
    refine ⟨c,z,edge,?_,?_⟩
    · have basec : base c = true := (supported c).2 (Or.inr rfl)
      have unequal : c ≠ z := fun equal => adj_irrefl z (equal ▸ edge)
      simpa [sem_ins,unequal] using basec
    · simp [sem_ins]
  have falsebranch := equality_critical_branch_false h.1 base z chain zero after
  have truebranch := cof_mem_supp.1 member
  rw [falsebranch] at truebranch
  exact Bool.false_ne_true truebranch


theorem equality_cofactor_supported_loss {n m : ℕ} {D : Dag} (hS : Strict n D)
    (ρ : Fin n → Option Bool) (ι : Fin m → Fin n)
    (b : Fin n → ℕ) (hb : PureBranch n D b)
    (J : Finset (Fin n)) (Z : Finset ℕ)
    (hJ : ∀ x ∈ J, x ∈ eligSet n D ∧ (⟨b x,0⟩ : Σ _ : ℕ, ℕ) ∉ cof_keptP D ρ ι)
    (hZ : ∀ w ∈ Z, 2 ≤ fanout D w ∧ supp n D w = ∅ ∧ cof_supp D ρ ι w = ∅) :
    cof_surP D ρ ι + J.card + Z.card ≤ totalSurplus n D := by
  classical
  let R := J.image (fun x => (⟨b x,0⟩ : Σ _ : ℕ, ℕ))
  let E := Z.image (fun w => (⟨w,0⟩ : Σ _ : ℕ, ℕ))
  have branch_unit : ∀ w, 2 ≤ fanout D w → (⟨w,0⟩ : Σ _ : ℕ, ℕ) ∈ units n D := by
    intro w hw
    exact mem_units.2 ⟨sb_mem_inner.2 (lt_of_fanout_pos hS (w := w) (by omega)),by change 0+1 < fanout D w; omega⟩
  have injR : Set.InjOn (fun x => (⟨b x,0⟩ : Σ _ : ℕ, ℕ)) (J : Set (Fin n)) := by
    intro x hx y hy eq
    have wires : b x = b y := congrArg Sigma.fst eq
    have same := (hb x (hJ x hx).1).2
    rw [wires,(hb y (hJ y hy).1).2] at same
    exact (Finset.singleton_injective same).symm
  have injE : Function.Injective (fun w => (⟨w,0⟩ : Σ _ : ℕ, ℕ)) :=
    fun _ _ eq => congrArg Sigma.fst eq
  have disjoint : Disjoint R E := by
    apply Finset.disjoint_left.2
    intro u hu hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨w,hw,eq⟩ := Finset.mem_image.1 hv
    have wires : w = b x := congrArg Sigma.fst eq
    have empty := (hZ w hw).2.1
    rw [wires,(hb x (hJ x hx).1).2] at empty
    have : x ∈ (∅ : Finset (Fin n)) := empty ▸ Finset.mem_singleton_self x
    exact Finset.notMem_empty x this
  have sub : R ∪ E ⊆ units n D := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.1 hu
      exact branch_unit _ (hb x (hJ x hx).1).1
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.1 hu
      exact branch_unit _ (hZ w hw).1
  have lost : ∀ u ∈ R ∪ E, u ∉ cof_keptP D ρ ι := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.1 hu
      exact (hJ x hx).2
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.1 hu
      exact cof_lostP_of_supp (hZ w hw).2.2
  have bound := cof_surP_add_lost (R ∪ E) sub lost
  have cardR : R.card = J.card := Finset.card_image_of_injOn injR
  have cardE : E.card = Z.card := Finset.card_image_of_injective _ injE
  rw [Finset.card_union_of_disjoint disjoint,cardR,cardE] at bound
  omega

theorem equality_cofactor_reserved_depleted {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) {c x : Fin 14} {l : List ℕ}
    (hx : x ∈ eligSet 14 D) (hne : x ≠ c)
    (inc : ∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → c ∈ supp 14 D u.1)
    (common : ∃ w, x ∈ supp 14 D w ∧ c ∈ supp 14 D w) :
    (⟨b x,0⟩ : Σ _ : ℕ, ℕ) ∉ cof_kept D (cf_rho c) (cf_iota l) := by
  obtain ⟨w,hw⟩ := common
  obtain ⟨z,hxz,hcz⟩ := sem_heawood_gr.2.2.1 x c hne
  obtain ⟨hs1,_,_,e,he,_,hec⟩ :=
    sem_diff_two_exits sem_heawood_gr h (sem_heawood_comp hD) b hb hne hx inc hw hxz hcz
  have hbx : b x ∈ carrierDiff 14 D x c := sem_mem_diff.2 (by
    rw [(hb x hx).2]
    exact ⟨Finset.mem_singleton_self x,fun hcx => hne (Finset.mem_singleton.1 hcx).symm⟩)
  exact cof_lost_of_deg (cof_diff_deplete h.1 (by simp [cf_rho]) hbx (hb x hx).1 hs1 he hec)

theorem equality_missing_branches_distinct {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (P : Finset (Fin 14)) (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b)
    {i j : Fin 14} (hne : i ≠ j)
    (hNj : sem_hw_nb j ⊆ P) (missing : ¬ sup_Occ 14 D P (sem_hw_nb i))
    (hNi : sem_hw_nb i ⊆ P) {u v : ℕ}
    (chaini : sem_Chain 14 D i.val u) (chainj : sem_Chain 14 D j.val v) : u ≠ v := by
  intro eq
  obtain ⟨a,ha1,ha2⟩ := nbr_diff_exists j i (Ne.symm hne)
  obtain ⟨k,s,_,_,_,_,hq⟩ := sem_shared_exact sem_heawood_gr h.1 (sem_heawood_comp hD) P hP
    chaini (sem_chain_dom h.1 (eq.symm ▸ chainj)) ⟨a,hNj (hw_mem_nb.2 ha1),ha1,ha2⟩
  apply missing
  refine ⟨src D (k,s),?_⟩
  ext x
  rw [Finset.mem_inter,hw_mem_nb]
  exact ⟨fun hx => (hq x hx.2).1 hx.1,
    fun hx => ⟨(hq x (hNi (hw_mem_nb.2 hx))).2 hx,hNi (hw_mem_nb.2 hx)⟩⟩



theorem equality_missing_empty_branch {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (P : Finset (Fin 14)) (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b) {i : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hNi : sem_hw_nb i ⊆ P)
    (missing : ¬ sup_Occ 14 D P (sem_hw_nb i)) :
    ∃ w, sem_Chain 14 D i.val w ∧ 2 ≤ fanout D w ∧ supp 14 D w = ∅ := by
  rcases sem_inelig_reach sem_heawood_gr h (sem_heawood_comp hD) hi with chain | branch
  · obtain ⟨j,s,_,_,_,hq⟩ := sem_exact_nbhd sem_heawood_gr h.1 (sem_heawood_comp hD) P hP chain
    apply False.elim
    apply missing
    refine ⟨src D (j,s),?_⟩
    ext x
    rw [Finset.mem_inter,hw_mem_nb]
    exact ⟨fun hx => (hq x hx.2).1 hx.1,
      fun hx => ⟨(hq x (hNi (hw_mem_nb.2 hx))).2 hx,hNi (hw_mem_nb.2 hx)⟩⟩
  · exact branch

theorem equality_m9_center_absent {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11}) (zero : ru D b 3 = ∅)
    {i : Fin 14} (hi : i ∈ ({0,1,2,5} : Finset (Fin 14))) :
    (3 : Fin 14) ∉ supp 14 D (src D (pos i)) := by
  intro member
  have hi' : i ∈ ineligSet 14 D := by
    rw [hI]
    exact (by decide : ({0,1,2,5} : Finset (Fin 14)) ⊆ {0,1,2,5,11}) hi
  have h11 : (11 : Fin 14) ∈ ineligSet 14 D := by rw [hI]; decide
  have hel7 : (7 : Fin 14) ∈ eligSet 14 D := by
    by_contra hn
    have := hI ▸ sem_mem_inelig.2 hn
    exact (by decide : (7 : Fin 14) ∉ ({0,1,2,5,11} : Finset (Fin 14))) this
  have hj : ∀ j ∈ ({11,i} : Finset (Fin 14)),
      j ∈ ineligSet 14 D ∧ (3 : Fin 14) ∈ supp 14 D (src D (pos j)) := by
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact ⟨h11,(hpos.1 11 h11).2.2.1 3 (by decide)⟩
    · have eq := Finset.mem_singleton.1 hj
      subst j
      exact ⟨hi',member⟩
  have bound := equality_assigned_budget_extra h hD b hb pos hpos {11,i} hj hel7 (by decide : Adj 3 7)
  have ne : (11 : Fin 14) ≠ i := by
    intro eq
    rw [← eq] at hi
    exact (by decide : (11 : Fin 14) ∉ ({0,1,2,5} : Finset (Fin 14))) hi
  rw [Finset.card_pair ne,zero,Finset.card_empty] at bound
  omega

theorem equality_m9_cofactor_supported_upper {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14) (b : Fin 14 → ℕ) (first : sem_FirstBranch 14 D b)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (zeros : ∀ x ∈ ({3,4,6} : Finset (Fin 14)), ru D b x = ∅)
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5)) :
    cof_surP D (cf_rho 3) (cf_iota cfL3) ≤ 7 := by
  classical
  have hb := sem_firstBranch_pure first
  obtain ⟨pos,hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  have eligible : ∀ x ∈ ({3,4,6,7,12} : Finset (Fin 14)), x ∈ eligSet 14 D := by
    intro x hx
    by_contra hn
    exact Finset.disjoint_left.1
      (by decide : Disjoint ({3,4,6,7,12} : Finset (Fin 14)) {0,1,2,5,11}) hx
      (hI ▸ sem_mem_inelig.2 hn)
  have ineligible : ∀ x ∈ ({2,5,11} : Finset (Fin 14)), x ∈ ineligSet 14 D := by
    intro x hx
    rw [hI]
    exact (by decide : ({2,5,11} : Finset (Fin 14)) ⊆ {0,1,2,5,11}) hx
  have Pind : ∀ a ∈ mx_L, ∀ b ∈ mx_L, ¬ Adj a b := by decide +kernel
  have n2 : sem_hw_nb 2 ⊆ mx_L := by decide
  have n5 : sem_hw_nb 5 ⊆ mx_L := by decide
  obtain ⟨u,cu,bu,eu⟩ := equality_missing_empty_branch h hD mx_L Pind
    (ineligible 2 (by decide)) n2 missing2
  obtain ⟨v,cv,bv,ev⟩ := equality_missing_empty_branch h hD mx_L Pind
    (ineligible 5 (by decide)) n5 missing5
  have different : u ≠ v := equality_missing_branches_distinct h hD mx_L Pind
    (by decide : (2 : Fin 14) ≠ 5) n5 missing2 n2 cu cv
  have empty_transfer : ∀ i ∈ ({2,5} : Finset (Fin 14)), ∀ w,
      sem_Chain 14 D i.val w → 2 ≤ fanout D w → supp 14 D w = ∅ →
        cof_supp D (cf_rho 3) (cf_iota cfL3) w = ∅ := by
    intro i hi w chain branch empty
    have hii : i ∈ ineligSet 14 D := by
      rw [hI]
      exact (by decide : ({2,5} : Finset (Fin 14)) ⊆ {0,1,2,5,11}) hi
    have wi : sem_bar (pos i) ∈ sem_W 14 D i := by
      rw [as_W h hD hpos hii]
      exact Finset.mem_singleton_self _
    apply equality_cofactor_empty_branch_empty h.1 hD cf3_good hii
      ((by decide : ∀ i ∈ ({2,5} : Finset (Fin 14)), i ≠ 3) i hi) wi _ chain branch empty
    rw [sem_bar_bar]
    exact equality_m9_center_absent h hD b hb pos hpos hI (zeros 3 (by decide))
      ((by decide : ({2,5} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi)
  have lost : ∀ x ∈ ({3,4,6,7,12} : Finset (Fin 14)),
      x ∈ eligSet 14 D ∧ (⟨b x,0⟩ : Σ _ : ℕ, ℕ) ∉ cof_keptP D (cf_rho 3) (cf_iota cfL3) := by
    intro x hx
    refine ⟨eligible x hx,?_⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · intro hk
      have member : (3 : Fin 14) ∈ supp 14 D (b 3) := by
        rw [(hb 3 (eligible 3 (by decide))).2]
        exact Finset.mem_singleton_self _
      exact cof_lost_of_true h.1 (by simp [cf_rho]) member (cof_keptP_sub hk)
    · intro hk
      have depleted := equality_cofactor_reserved_depleted (l := cfL3) h hD b hb
        (eligible 4 (by decide)) (by decide : (4 : Fin 14) ≠ 3)
        (by
          intro q hq h4
          have mem := mem_ru.2 ⟨hq,h4⟩
          rw [zeros 4 (by decide)] at mem
          exact (Finset.notMem_empty _ mem).elim)
        ⟨src D (pos 11),(hpos.1 11 (ineligible 11 (by decide))).2.2.1 4 (by decide),
          (hpos.1 11 (ineligible 11 (by decide))).2.2.1 3 (by decide)⟩
      exact depleted (cof_keptP_sub hk)
    · intro hk
      have depleted := equality_cofactor_reserved_depleted (l := cfL3) h hD b hb
        (eligible 6 (by decide)) (by decide : (6 : Fin 14) ≠ 3)
        (by
          intro q hq h6
          have mem := mem_ru.2 ⟨hq,h6⟩
          rw [zeros 6 (by decide)] at mem
          exact (Finset.notMem_empty _ mem).elim)
        ⟨src D (pos 11),(hpos.1 11 (ineligible 11 (by decide))).2.2.1 6 (by decide),
          (hpos.1 11 (ineligible 11 (by decide))).2.2.1 3 (by decide)⟩
      exact depleted (cof_keptP_sub hk)
    · exact cof_lostP_of_supp (equality_cofactor_neighbor_branch_empty h hD cf3_good
        (by decide : Adj 3 7) (first 7 (eligible 7 (by decide))).2.2)
    · exact cof_lostP_of_supp (equality_cofactor_neighbor_branch_empty h hD cf3_good
        (by decide : Adj 3 12) (first 12 (eligible 12 (by decide))).2.2)
  have bound := equality_cofactor_supported_loss h.1 (cf_rho 3) (cf_iota cfL3) b hb
    {3,4,6,7,12} {u,v} lost (by
      intro w hw
      rcases Finset.mem_insert.1 hw with eq | hw
      · subst w
        exact ⟨bu,eu,empty_transfer 2 (by decide) u cu bu eu⟩
      · have eq := Finset.mem_singleton.1 hw
        subst w
        exact ⟨bv,ev,empty_transfer 5 (by decide) v cv bv ev⟩)
  rw [show ({3,4,6,7,12} : Finset (Fin 14)).card = 5 from rfl,
    Finset.card_pair different] at bound
  omega



theorem equality_m9_normal_coordinates {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14) (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (hI : ineligSet 14 D = {0,1,2,5,11}) (three : (residualUnits 14 D b).card = 3) :
    ∃ a : Fin 3 → (Σ _ : ℕ, ℕ), Function.Injective a ∧
      (∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) ∧
      (equality_coordinate_set (D := D) a 7 = {0} ∨
        equality_coordinate_set (D := D) a 7 = {0,1}) := by
  classical
  let S := residualUnits 14 D b
  let e : (↑S) ≃ Fin 3 := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact three)
  let a : Fin 3 → (Σ _ : ℕ, ℕ) := fun k => (e.symm k).val
  have injective : Function.Injective a := fun i j equal => e.symm.injective (Subtype.ext equal)
  have onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u := by
    intro u
    constructor
    · intro member
      exact ⟨e ⟨u,member⟩,by simp [a]⟩
    · rintro ⟨k,rfl⟩
      exact (e.symm k).property
  obtain ⟨pos,hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  have proper := equality_m9_coordinate_proper h hD h14 b hb pos hpos hI a injective onto 0
  change equality_coordinate_set (D := D) a 7 ≠ Finset.univ at proper
  have small := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
    ⟨Finset.subset_univ (equality_coordinate_set (D := D) a 7),proper⟩)
  have card := equality_coordinate_card a injective onto 7
  have positive := equality_m9_positive h hD b hb pos hpos hI 0
  change 0 < (ru D b 7).card at positive
  simp only [Finset.card_univ,Fintype.card_fin] at small
  obtain ⟨a',inj',onto',first⟩ := equality_residual_coordinates three (by omega)
  exact ⟨a',inj',onto',first⟩


theorem equality_m9_zero_points_of_certificate
    (certificate : ∀ (r : Fin 6 → Fin 8) (a b : Fin 3) (T : Fin 8),
      (r 0 = 1 ∨ r 0 = 3) → m9_normal r a b = true → m9_pointAllowed r a b T = false)
    {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5))
    (protects : ∀ i ∈ ({0,1} : Finset (Fin 14)), ∀ w,
      Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1)
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    (first : equality_coordinate_set (D := D) a 7 = {0} ∨
      equality_coordinate_set (D := D) a 7 = {0,1}) :
    ∀ z ∈ ({3,4,6} : Finset (Fin 14)), ru D b z = ∅ := by
  classical
  obtain ⟨α,β,normal,points⟩ := equality_m9_all_constraints h hD h14 b hb hI
    missing2 missing5 protects a injective onto
  intro z hz
  have zero : equality_coordinate_set (D := D) a z = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro k member
    have positive : (equality_coordinate_set (D := D) a z).Nonempty := ⟨k,member⟩
    exact m9_no_point_constraints_of_certificate certificate
      (fun t => equality_coordinate_set (D := D) a (equality_m9_line t)) α β
      (equality_coordinate_set (D := D) a z) first normal (points z hz positive)
  have card := equality_coordinate_card a injective onto z
  rw [zero,Finset.card_empty] at card
  exact Finset.card_eq_zero.1 card.symm


theorem equality_m9_two_missing_impossible_of_certificate
    (certificate : ∀ (r : Fin 6 → Fin 8) (a b : Fin 3) (T : Fin 8),
      (r 0 = 1 ∨ r 0 = 3) → m9_normal r a b = true → m9_pointAllowed r a b T = false)
    {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (hM : equality_missing_cap D = {2,5}) : False := by
  classical
  have missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2) := by
    have member : (2 : Fin 14) ∈ equality_missing_cap D := by rw [hM]; decide
    exact (Finset.mem_filter.1 member).2
  have missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5) := by
    have member : (5 : Fin 14) ∈ equality_missing_cap D := by rw [hM]; decide
    exact (Finset.mem_filter.1 member).2
  have protects : ∀ i ∈ ({0,1} : Finset (Fin 14)), ∀ w,
      Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1 := by
    intro i hi
    apply equality_chain_protected h.1
    apply equality_mixed_cap_occ_chain h hD h14 hI
      ((by decide : ({0,1} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi)
    by_contra missing
    have member : i ∈ equality_missing_cap D := Finset.mem_filter.2
      ⟨((by decide : ({0,1} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi),missing⟩
    rw [hM] at member
    exact Finset.disjoint_left.1 (by decide : Disjoint ({0,1} : Finset (Fin 14)) {2,5}) hi member
  obtain ⟨b,first⟩ := sem_exists_firstBranch sem_heawood_gr h.1 (sem_heawood_comp hD)
  have hb := sem_firstBranch_pure first
  have total := totalSurplus_split 14 D
  have zero := equality_mixed_cap_saturated h hD h14 hI
  rw [hM,show ({2,5} : Finset (Fin 14)).card = 2 from rfl] at zero
  have eligible := inelig_card_add 14 D
  rw [hI,show ({0,1,2,5,11} : Finset (Fin 14)).card = 5 from rfl] at eligible
  have lower := mx_star h hD (by rw [hI]; decide)
  have residual := card_residual h.1 b hb
  have three : (residualUnits 14 D b).card = 3 := by omega
  obtain ⟨a,injective,onto,normalized⟩ := equality_m9_normal_coordinates h hD h14 b hb hI three
  have zeros := equality_m9_zero_points_of_certificate certificate h hD h14 b hb hI missing2 missing5
    protects a injective onto normalized
  have upper := equality_m9_cofactor_supported_upper h hD h14 b first hI zeros missing2 missing5
  have lower := equality_cf_supported_eight h hD cf3_good
    (by change ∀ w, Relation.ReflTransGen (sem_step 14 D) 0 w → fanout D w ≤ 1
        exact protects 0 (by decide))
    (by change ∀ w, Relation.ReflTransGen (sem_step 14 D) 1 w → fanout D w ≤ 1
        exact protects 1 (by decide))
  omega

theorem equality_occurrence_relabel {n : ℕ} (σ : Equiv.Perm (Fin n))
    {D : Dag} (h : Strict n D) (P M : Finset (Fin n)) :
    sup_Occ n (relabel σ D) (P.image σ) (M.image σ) ↔ sup_Occ n D P M := by
  classical
  constructor
  · rintro ⟨w,hw⟩
    let v := liftP σ.symm w
    refine ⟨v,Finset.image_injective σ.injective ?_⟩
    rw [Finset.image_inter _ _ σ.injective,← relabel_supp σ h v]
    have inv : liftP σ v = w := tr_liftP_inv' σ w
    rw [inv]
    exact hw
  · rintro ⟨w,hw⟩
    refine ⟨liftP σ w,?_⟩
    rw [relabel_supp σ h w,← Finset.image_inter _ _ σ.injective,hw]

def equality_m9_pair (k : Fin 6) : Finset (Fin 14) := ![{0,1},{0,2},{0,5},{1,2},{1,5},{2,5}] k

def equality_m9_permutation (k : Fin 6) : Fin 14 → Fin 14 :=
  ![hc_ofList [2,5,0,3,4,1,6,12,8,9,13,11,7,10],
    hc_ofList [5,1,2,6,4,0,3,9,12,7,10,11,8,13],
    hc_ofList [2,1,0,4,3,5,6,13,8,9,12,11,10,7],
    hc_ofList [0,5,2,4,3,1,6,10,8,9,7,11,13,12],
    hc_ofList [0,2,1,6,4,5,3,8,7,12,10,11,9,13],
    hc_ofList [0,1,2,3,4,5,6,7,8,9,10,11,12,13]] k

def equality_m9_automorphism (k : Fin 6) : Equiv.Perm (Fin 14) :=
  ⟨equality_m9_permutation k,equality_m9_permutation k,
    by intro i; revert i k; decide +kernel,
    by intro i; revert i k; decide +kernel⟩

theorem equality_m9_automorphism_aut (k : Fin 6) : IsAut (equality_m9_automorphism k) := by
  apply hc_isAut_of
  revert k
  decide +kernel

theorem equality_m9_automorphism_geometry : ∀ k : Fin 6,
    ({0,1,2,5} : Finset (Fin 14)).image (equality_m9_automorphism k) = {0,1,2,5} ∧
    ({0,1,2,5,11} : Finset (Fin 14)).image (equality_m9_automorphism k) = {0,1,2,5,11} ∧
    mx_L.image (equality_m9_automorphism k) = mx_L ∧
    (equality_m9_pair k).image (equality_m9_automorphism k) = {2,5} ∧
    ∀ i : Fin 14, (sem_hw_nb i).image (equality_m9_automorphism k) =
      sem_hw_nb (equality_m9_automorphism k i) := by
  decide +kernel

theorem equality_m9_missing_relabel {D : Dag} (h : Strict 14 D) (k : Fin 6) :
    equality_missing_cap (relabel (equality_m9_automorphism k) D) =
      (equality_missing_cap D).image (equality_m9_automorphism k) := by
  classical
  let σ := equality_m9_automorphism k
  have geo := equality_m9_automorphism_geometry k
  have member (i : Fin 14) : σ i ∈ ({0,1,2,5} : Finset (Fin 14)) ↔
      i ∈ ({0,1,2,5} : Finset (Fin 14)) := by
    constructor
    · intro hi
      have im : σ i ∈ ({0,1,2,5} : Finset (Fin 14)).image σ := by
        rw [geo.1]
        exact hi
      obtain ⟨j,hj,equal⟩ := Finset.mem_image.1 im
      exact σ.injective equal ▸ hj
    · intro hi
      have im : σ i ∈ ({0,1,2,5} : Finset (Fin 14)).image σ :=
        Finset.mem_image.2 ⟨i,hi,rfl⟩
      rwa [geo.1] at im
  have transfer (i : Fin 14) :
      σ i ∈ equality_missing_cap (relabel σ D) ↔ i ∈ equality_missing_cap D := by
    have occurrence := equality_occurrence_relabel σ h mx_L (sem_hw_nb i)
    rw [geo.2.2.1,geo.2.2.2.2 i] at occurrence
    simp only [equality_missing_cap,Finset.mem_filter]
    exact and_congr (member i) (not_congr occurrence)
  ext j
  constructor
  · intro hj
    refine Finset.mem_image.2 ⟨σ.symm j,?_,σ.apply_symm_apply j⟩
    apply (transfer (σ.symm j)).1
    simpa only [Equiv.apply_symm_apply] using hj
  · intro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 hj
    exact (transfer i).2 hi

theorem equality_m9_any_two_missing_of_canonical
    (canonical : ∀ {D : Dag}, StrictLive 14 D → Correct D → totalSurplus 14 D ≤ 14 →
      ineligSet 14 D = {0,1,2,5,11} → equality_missing_cap D = {2,5} → False)
    {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (two : (equality_missing_cap D).card = 2) : False := by
  classical
  have sub : equality_missing_cap D ⊆ ({0,1,2,5} : Finset (Fin 14)) := Finset.filter_subset _ _
  have shapes : ∀ M : Finset (Fin 14), M ⊆ ({0,1,2,5} : Finset (Fin 14)) →
      M.card = 2 → ∃ k : Fin 6, M = equality_m9_pair k := by
    have enumeration : ({0,1,2,5} : Finset (Fin 14)).powersetCard 2 =
        Finset.univ.image equality_m9_pair := by decide +kernel
    intro M subset card
    have member := Finset.mem_powersetCard.2 ⟨subset,card⟩
    rw [enumeration] at member
    obtain ⟨k,_,equal⟩ := Finset.mem_image.1 member
    exact ⟨k,equal.symm⟩
  obtain ⟨k,hM⟩ := shapes _ sub two
  obtain ⟨h',hD',_,total,_,_,_,ineligible⟩ :=
    heawood_relabel (equality_m9_automorphism k) (equality_m9_automorphism_aut k) h hD
  apply canonical h' hD'
    (by rw [total]; exact h14)
  · rw [ineligible,hI]
    exact (equality_m9_automorphism_geometry k).2.1
  · rw [equality_m9_missing_relabel h.1 k,hM]
    exact (equality_m9_automorphism_geometry k).2.2.2.1

theorem equality_m9_two_missing_impossible {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (hM : equality_missing_cap D = {2,5}) : False :=
  equality_m9_two_missing_impossible_of_certificate m9_point_empty h hD h14 hI hM

theorem equality_m9_any_two_missing_impossible {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (two : (equality_missing_cap D).card = 2) : False :=
  equality_m9_any_two_missing_of_canonical (fun h hD h14 hI hM =>
    equality_m9_two_missing_impossible h hD h14 hI hM) h hD h14 hI two

end PEqualNP.Outside.L_meta_6659_aux
