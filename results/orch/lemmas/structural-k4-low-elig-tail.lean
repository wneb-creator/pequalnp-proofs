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
