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

