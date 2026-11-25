import PNPAccepted6659
namespace PEqualNP.Outside.L_meta_6659_aux

lemma c6leaf_supp_out {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hirr : ∀ u, ¬ G u u) (hC : sem_Comp n G D) : supp n D (outW n D) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro v hv
  obtain ⟨a,b,edge,ha,hb⟩ := (hC (single v)).mp (mem_supp.mp hv)
  simp only [single,decide_eq_true_eq] at ha hb
  rw [ha,hb] at edge
  exact hirr v edge

lemma c6leaf_dom_pure {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hsym : ∀ u v, G u v → G v u) (hirr : ∀ u, ¬ G u u)
    {v : Fin n} (separates : ∀ w, v ≠ w → ∃ z, G v z ∧ ¬ G w z)
    (hS : Strict n D) (hC : sem_Comp n G D)
    (b : ℕ) (hdom : sem_Dom n D b v.val) : supp n D b ⊆ {v}  := by
  intro u hu
  rw [Finset.mem_singleton]
  by_contra huv
  obtain ⟨z, hvz, huz⟩ := separates u (Ne.symm huv)
  have hxb : val D (sem_two u z) b = true := sem_val_of_supp hS hu (by simp [sem_two])
  have hyb : val D (sem_ins v (sem_two u z)) b = true :=
    sem_val_of_supp hS hu (by simp [sem_ins, sem_two])
  have hout := sem_dom_eq hS _ _ v (sem_ins_agree v (sem_two u z)) b hdom (by rw [hxb, hyb])
  have h1 : ¬ sem_Edge G (sem_two u z) := by
    rintro ⟨a, c, hac, ha, hc⟩
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at ha hc
    rcases ha with ha | ha <;> rcases hc with hc | hc <;> rw [ha, hc] at hac
    · exact hirr _ hac
    · exact huz hac
    · exact huz (hsym _ _ hac)
    · exact hirr _ hac
  have h2 : sem_Edge G (sem_ins v (sem_two u z)) :=
    ⟨v, z, hvz, sem_ins_self v _, by simp [sem_ins, sem_two]⟩
  have h3 := (hC _).mpr h2
  rw [← hout] at h3
  exact h1 ((hC _).mp h3)

lemma c6leaf_inelig_pure {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hsym : ∀ u v, G u v → G v u) (hirr : ∀ u, ¬ G u u)
    {v : Fin n} (separates : ∀ w, v ≠ w → ∃ z, G v z ∧ ¬ G w z)
    (hS : Strict n D) (hC : sem_Comp n G D) (hv : v ∈ ineligSet n D) {w : ℕ}
    (hw : v ∈ supp n D w) : supp n D w = {v} :=
  Finset.Subset.antisymm
    (c6leaf_dom_pure hsym hirr separates hS hC w
      (sem_chain_dom hS (sem_inelig_chain hS hv hw)))
    (Finset.singleton_subset_iff.mpr hw)

lemma c6leaf_first_branch {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hsym : ∀ u v, G u v → G v u) (hirr : ∀ u, ¬ G u u)
    {v : Fin n} (separates : ∀ w, v ≠ w → ∃ z, G v z ∧ ¬ G w z)
    (hS : Strict n D) (hC : sem_Comp n G D) (hv : v ∈ eligSet n D) :
    ∃ b, 2 ≤ fanout D b ∧ supp n D b = {v} := by
  classical
  have hex : ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := mem_eligSet.mp hv
  obtain ⟨branch,carrier⟩ := Nat.find_spec hex
  have chain : sem_Chain n D v.val (Nat.find hex) :=
    sem_carrier_chain hS v _ carrier (fun w less carries => by
      have minimal := Nat.find_min hex less
      by_contra many
      exact minimal ⟨by omega,carries⟩)
  exact ⟨Nat.find hex,branch,Finset.Subset.antisymm
    (c6leaf_dom_pure hsym hirr separates hS hC _ (sem_chain_dom hS chain))
    (Finset.singleton_subset_iff.mpr carrier)⟩

lemma c6leaf_joint_meeting {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hirr : ∀ u, ¬ G u u) (hS : Strict n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) :
    ∃ j, j < D.length ∧ tag D j = true ∧ val D (sem_two u v) (n+j) = true ∧
      u ∉ supp n D (n+j) ∧ v ∉ supp n D (n+j) ∧
      ∃ s : Bool, u ∈ supp n D (src D (j,s)) ∧ v ∉ supp n D (src D (j,s)) ∧
        v ∈ supp n D (src D (j,!s)) ∧ u ∉ supp n D (src D (j,!s))  := by
  classical
  have hex : ∃ w, val D (sem_two u v) w = true ∧ u ∉ supp n D w ∧ v ∉ supp n D w :=
    ⟨outW n D, (hC _).2 (sem_two_edge huv), by rw [c6leaf_supp_out hirr hC]; simp,
      by rw [c6leaf_supp_out hirr hC]; simp⟩
  obtain ⟨hw1, hw2, hw3⟩ := Nat.find_spec hex
  have hmin : ∀ a, a < Nat.find hex → val D (sem_two u v) a = true →
      u ∈ supp n D a ∨ v ∈ supp n D a := by
    intro a ha hva
    by_contra hc
    rw [not_or] at hc
    exact Nat.find_min hex ha ⟨hva, hc.1, hc.2⟩
  generalize Nat.find hex = w at hw1 hw2 hw3 hmin
  have hlt : w < n + D.length := by
    by_contra hc
    rw [val_ge D _ w (by omega)] at hw1
    exact Bool.false_ne_true hw1
  have hn : n ≤ w := by
    by_contra hc
    have hc' : w < n := by omega
    rw [val_input D _ w hc'] at hw1
    have hs : supp n D w = {⟨w, hc'⟩} := supp_input D ⟨w, hc'⟩
    rw [hs, Finset.mem_singleton] at hw2 hw3
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hw1
    rcases hw1 with h | h
    · exact hw2 h.symm
    · exact hw3 h.symm
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hval := hw1
  rw [val_gate hS _ j hj] at hw1
  rw [supp_gate hS j hj] at hw2 hw3
  cases ht : tag D j
  · exfalso
    rw [ht] at hw1 hw2 hw3
    simp only [gop_false, Bool.or_eq_true] at hw1
    simp only [Bool.false_eq_true, ite_false, Finset.mem_union, not_or] at hw2 hw3
    rcases hw1 with h | h
    · rcases hmin _ ha h with h' | h'
      · exact hw2.1 h'
      · exact hw3.1 h'
    · rcases hmin _ hb h with h' | h'
      · exact hw2.2 h'
      · exact hw3.2 h'
  · rw [ht] at hw1 hw2 hw3
    simp only [gop_true, Bool.and_eq_true] at hw1
    simp only [ite_true, Finset.mem_inter, not_and] at hw2 hw3
    have hsupp : u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) := by
      rw [sem_supp_and hS hj ht]
      simp only [Finset.mem_inter, not_and]
      exact ⟨hw2, hw3⟩
    refine ⟨j, hj, ht, hval, hsupp.1, hsupp.2, ?_⟩
    rcases hmin _ ha hw1.1 with hA | hA
    · have hB : u ∉ supp n D (opB D j) := hw2 hA
      have hBv : v ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_left hB
      exact ⟨false, by simpa [src] using hA, by simpa [src] using fun h => hw3 h hBv,
        by simpa [src] using hBv, by simpa [src] using hB⟩
    · have hB : v ∉ supp n D (opB D j) := hw3 hA
      have hBu : u ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_right hB
      exact ⟨true, by simpa [src] using hBu, by simpa [src] using hB,
        by simpa [src] using hA, by simpa [src] using fun h => hw2 h hBu⟩

lemma c6leaf_inelig_consumer {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hsym : ∀ u v, G u v → G v u) (hirr : ∀ u, ¬ G u u)
    {v : Fin n} (separates : ∀ w, v ≠ w → ∃ z, G v z ∧ ¬ G w z)
    (neighbor : ∃ a, G v a) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hv : v ∈ ineligSet n D) :
    ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧ supp n D (src D e) = {v} ∧
      supp n D (n+e.1) = ∅ ∧ (∀ a, G v a → a ∈ supp n D (src D (e.1,!e.2))) ∧
      exitArcs n D (carrierT n D {v}) = {e} ∧ merges n D (carrierT n D {v}) = ∅  := by
  have hS := h.1
  have hfl := carrier_flow_union h {v} (by rw [c6leaf_supp_out hirr hC]; simp)
  rw [sem_inelig_surplus hv, Finset.card_singleton] at hfl
  have hmeet : ∀ a, G v a → ∃ j s, j < D.length ∧ tag D j = true ∧
      (j, s) ∈ exitArcs n D (carrierT n D {v}) ∧ a ∈ supp n D (src D (j, !s)) := by
    intro a hva
    obtain ⟨j, hj, ht, -, hju, -, s, h1, -, h3, -⟩ := c6leaf_joint_meeting hirr hS hC hva
    exact ⟨j, s, hj, ht, sem_mem_exit1.mpr ⟨hj, h1, hju⟩, h3⟩
  obtain ⟨a0, ha0⟩ := neighbor
  obtain ⟨j0, s0, hj0, ht0, hm0, -⟩ := hmeet a0 ha0
  have hcard : (exitArcs n D (carrierT n D {v})).card = 1 := by
    have := Finset.card_pos.mpr ⟨_, hm0⟩
    omega
  have hmer : merges n D (carrierT n D {v}) = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  rw [he, Finset.mem_singleton] at hm0
  subst hm0
  have hsrc : supp n D (src D (j0, s0)) = {v} :=
    c6leaf_inelig_pure hsym hirr separates hS hC hv
      (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.1
  have hnot : v ∉ supp n D (n + j0) :=
    (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.2
  refine ⟨(j0, s0), hj0, ht0, hsrc, ?_, ?_, he, hmer⟩
  · refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
    have hx2 := sem_supp_and_sub hS hj0 ht0 s0 hx
    rw [hsrc, Finset.mem_singleton] at hx2
    exact hnot (hx2 ▸ hx)
  · intro a hva
    obtain ⟨j, s, -, -, hm, ha⟩ := hmeet a hva
    rw [he, Finset.mem_singleton] at hm
    rw [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ha

lemma c6leaf_three_slots {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hsym : ∀ u v, G u v → G v u) (hirr : ∀ u, ¬ G u u)
    (h : StrictLive n D) (hC : sem_Comp n G D) (p u v z : Fin n)
    (hu : u ∈ ineligSet n D) (hv : v ∈ ineligSet n D)
    (sepu : ∀ w, u ≠ w → ∃ a, G u a ∧ ¬ G w a)
    (sepv : ∀ w, v ≠ w → ∃ a, G v a ∧ ¬ G w a)
    (pu : G p u) (pv : G p v) (pz : G p z)
    (uv : u ≠ v) (zu : z ≠ u) (zv : z ≠ v) :
    3 ≤ (sem_W n D p).card := by
  classical
  obtain ⟨eu,heu,_,pureu,emptyu,nbu,_,_⟩ :=
    c6leaf_inelig_consumer hsym hirr sepu ⟨p,hsym _ _ pu⟩ h hC hu
  obtain ⟨ev,hev,_,purev,emptyv,nbv,_,_⟩ :=
    c6leaf_inelig_consumer hsym hirr sepv ⟨p,hsym _ _ pv⟩ h hC hv
  have wpu : sem_bar eu ∈ sem_W n D p := sem_mem_W.mpr
    ⟨heu,nbu p (hsym _ _ pu),by change p ∉ supp n D (n+eu.1); rw [emptyu]; simp⟩
  have wpv : sem_bar ev ∈ sem_W n D p := sem_mem_W.mpr
    ⟨hev,nbv p (hsym _ _ pv),by change p ∉ supp n D (n+ev.1); rw [emptyv]; simp⟩
  have different : sem_bar eu ≠ sem_bar ev := by
    intro same
    have same' : eu = ev := by rw [← sem_bar_bar eu,same,sem_bar_bar]
    have sets : ({u} : Finset (Fin n)) = {v} := by rw [← pureu,← purev,same']
    exact uv (Finset.singleton_injective sets)
  obtain ⟨j,hj,_,_,np,_,s,hp,_,hz,_⟩ := c6leaf_joint_meeting hirr h.1 hC pz
  let e : ℕ × Bool := (j,s)
  have we : e ∈ sem_W n D p := sem_mem_W.mpr ⟨hj,hp,np⟩
  have freshu : e ≠ sem_bar eu := by
    intro same
    have source : src D (j,!s) = src D eu := by
      change src D (sem_bar e) = src D eu
      rw [same,sem_bar_bar]
    rw [source,pureu,Finset.mem_singleton] at hz
    exact zu hz
  have freshv : e ≠ sem_bar ev := by
    intro same
    have source : src D (j,!s) = src D ev := by
      change src D (sem_bar e) = src D ev
      rw [same,sem_bar_bar]
    rw [source,purev,Finset.mem_singleton] at hz
    exact zv hz
  have subset : ({e,sem_bar eu,sem_bar ev} : Finset (ℕ × Bool)) ⊆ sem_W n D p := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact we
    · exact wpu
    · exact wpv
  have cardinal : ({e,sem_bar eu,sem_bar ev} : Finset (ℕ × Bool)).card = 3 := by
    simp [freshu,freshv,different]
  rw [← cardinal]
  exact Finset.card_le_card subset

abbrev c6leafAdj (u v : Fin 9) : Prop :=
  (u,v) ∈ ({(0,3),(0,5),(0,6),(1,3),(1,4),(1,7),(2,4),(2,5),(2,8)} : Finset (Fin 9 × Fin 9)) ∨
  (v,u) ∈ ({(0,3),(0,5),(0,6),(1,3),(1,4),(1,7),(2,4),(2,5),(2,8)} : Finset (Fin 9 × Fin 9))

lemma c6leaf_shared_force_three {D : Dag} (h : StrictLive 9 D)
    (correct : sem_Comp 9 c6leafAdj D)
    (line3 : (3 : Fin 9) ∈ ineligSet 9 D) (line5 : (5 : Fin 9) ∈ ineligSet 9 D) :
    3 ≤ (sem_W 9 D 0).card := by
  apply c6leaf_three_slots (G := c6leafAdj) (by decide +kernel) (by decide +kernel)
    h correct 0 3 5 6 line3 line5 <;> decide +kernel

lemma c6leaf_small_budget_branches {D : Dag} (h : StrictLive 9 D)
    (correct : sem_Comp 9 c6leafAdj D) (size : D.length ≤ 11)
    (points : ({0,1,2} : Finset (Fin 9)) ⊆ eligSet 9 D) :
    ∃ b : Fin 9 → ℕ, PureBranch 9 D b ∧
      eligSet 9 D ⊆ ({0,1,2} : Finset (Fin 9)) := by
  classical
  have first : ∀ v ∈ ({0,1,2} : Finset (Fin 9)),
      ∃ w, 2 ≤ fanout D w ∧ supp 9 D w = {v} := by
    intro v hv
    apply c6leaf_first_branch (G := c6leafAdj) (by decide +kernel) (by decide +kernel)
      ((by decide +kernel : ∀ v ∈ ({0,1,2} : Finset (Fin 9)),
        ∀ w, v ≠ w → ∃ z, c6leafAdj v z ∧ ¬ c6leafAdj w z) v hv) h.1 correct (points hv)
  choose! b hb using first
  let R : Finset (Σ _ : ℕ, ℕ) := ({0,1,2} : Finset (Fin 9)).image (fun v => ⟨b v,0⟩)
  have subset : R ⊆ units 9 D := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    rw [mem_units]
    change b v ∈ inner 9 D ∧ 0+1 < fanout D (b v)
    exact ⟨sb_mem_inner.mpr (lt_of_fanout_pos h.1 (by have := (hb v hv).1; omega)),
      by have := (hb v hv).1; omega⟩
  have injective : Set.InjOn (fun v : Fin 9 => (⟨b v,0⟩ : Σ _ : ℕ, ℕ))
      (({0,1,2} : Finset (Fin 9)) : Set (Fin 9)) := by
    intro v hv w hw equal
    have same : b v = b w := congrArg Sigma.fst equal
    have supports := (hb v hv).2
    rw [same,(hb w hw).2] at supports
    exact (Finset.singleton_injective supports).symm
  have cardR : R.card = 3 := by
    rw [Finset.card_image_of_injOn injective]
    decide
  have total : totalSurplus 9 D ≤ 3 := by
    have identity := surplus_identity h
    omega
  have all : R = units 9 D := Finset.eq_of_subset_of_card_le subset (by
    rw [card_units,cardR]
    exact total)
  have eligible : eligSet 9 D ⊆ ({0,1,2} : Finset (Fin 9)) := by
    intro v hv
    obtain ⟨w,branch,carries⟩ := mem_eligSet.mp hv
    have unit : (⟨w,0⟩ : Σ _ : ℕ, ℕ) ∈ units 9 D := by
      rw [mem_units]
      change w ∈ inner 9 D ∧ 0+1 < fanout D w
      exact ⟨sb_mem_inner.mpr (lt_of_fanout_pos h.1 (by omega)),by omega⟩
    rw [← all] at unit
    obtain ⟨i,hi,equal⟩ := Finset.mem_image.mp unit
    have same : b i = w := congrArg Sigma.fst equal
    rw [← same,(hb i hi).2,Finset.mem_singleton] at carries
    rwa [carries]
  exact ⟨b,fun v hv => hb v (eligible hv),eligible⟩

lemma c6leaf_three_eligible_impossible {D : Dag} (h : StrictLive 9 D)
    (correct : sem_Comp 9 c6leafAdj D) (size : D.length ≤ 11)
    (points : ({0,1,2} : Finset (Fin 9)) ⊆ eligSet 9 D) : False := by
  classical
  obtain ⟨b,hb,eligible⟩ := c6leaf_small_budget_branches h correct size points
  have line3 : (3 : Fin 9) ∈ ineligSet 9 D := sem_mem_inelig.mpr (fun hv =>
    (by decide : (3 : Fin 9) ∉ ({0,1,2} : Finset (Fin 9))) (eligible hv))
  have line5 : (5 : Fin 9) ∈ ineligSet 9 D := sem_mem_inelig.mpr (fun hv =>
    (by decide : (5 : Fin 9) ∉ ({0,1,2} : Finset (Fin 9))) (eligible hv))
  have lower := c6leaf_shared_force_three h correct line3 line5
  have surplus := surplus_carrierT_le h.1 b hb ({0} : Finset (Fin 9))
  have number : 3 ≤ (eligSet 9 D).card := by
    have bound := Finset.card_le_card points
    exact bound
  have intersection : (({0} : Finset (Fin 9)) ∩ eligSet 9 D).card ≤ 1 := by
    have bound := Finset.card_le_card (Finset.inter_subset_left :
      ({0} : Finset (Fin 9)) ∩ eligSet 9 D ⊆ {0})
    simpa using bound
  have total := surplus_identity h
  have split := totalSurplus_split 9 D
  have flow := carrier_flow_union h ({0} : Finset (Fin 9)) (by
    rw [c6leaf_supp_out (G := c6leafAdj) (by decide +kernel) correct]
    simp)
  change (sem_W 9 D 0).card + (merges 9 D (carrierT 9 D {0})).card =
    ({0} : Finset (Fin 9)).card + surplusOn D (carrierT 9 D {0}) at flow
  simp only [Finset.card_singleton] at flow
  omega

end PEqualNP.Outside.L_meta_6659_aux
