namespace PEqualNP.Outside.L_meta_2592_aux.Stronger.NegativeSeed

lemma lower_without_seed (i j : Fin 10) {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.pins ++ [extra i j])
    (needed : Extended.pins.getD 0 Extended.zero ∈ S) (used : extra i j ∈ S) : 17 ≤ k := by
  classical
  have ne := extra_ne_first i j
  let front := Extended.pins.getD 0 Extended.zero :: extra i j ::
    ((S.erase (Extended.pins.getD 0 Extended.zero)).erase (extra i j)).toList
  have nd : front.Nodup := by
    simp [front,ne,ne.symm,Finset.nodup_toList,-List.getD_eq_getElem?_getD]
  have eqS : front.toFinset = S := by
    ext a
    by_cases ha : a = Extended.pins.getD 0 Extended.zero <;>
      by_cases hb : a = extra i j <;> simp [front,ha,hb,needed,used,-List.getD_eq_getElem?_getD]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows embed (Extended.observe Extended.target) = observe graph := by
    rw [observe_projected]
    exact congrArg observe (by decide +kernel)
  have isZero : observe zero = fun _ => false := by funext r; simp [observe,bit,zero]
  have supplyRoots : supply true (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows embed)) := by
    intro v hv
    obtain ⟨_,hin,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hm,rfl⟩ := List.mem_map.mp hin
    have hr := raw a (eqS ▸ List.mem_toFinset.mpr hm)
    simp only [List.mem_append,List.mem_singleton] at hr
    rcases hr with hp | he
    · have hlist : List.ofFn (fun t : Fin 10 => Extended.pins.getD t.val Extended.zero) = Extended.pins := rfl
      rw [← hlist] at hp
      obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hp
      exact pin_available t
    · subst a
      rw [observe_projected,extra_projects_zero]
      exact Or.inr (Or.inl ⟨false,isZero⟩)
  have bound := projected_bound embed hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L:=15) (same ▸ nineFloor)
  have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows embed)) := by
    have firstConstant : Constant (restrictRows embed (Extended.observe (Extended.pins.getD 0 Extended.zero))) := by
      rw [observe_projected,show projected (Extended.pins.getD 0 Extended.zero) = zero by decide +kernel]
      exact ⟨false,isZero⟩
    have extraConstant : Constant (restrictRows embed (Extended.observe (extra i j))) := by
      rw [observe_projected,extra_projects_zero]
      exact ⟨false,isZero⟩
    simp only [front,List.map_cons,List.map_map,mass_cons,cost,firstConstant,extraConstant,ite_true]
    omega
  omega

end PEqualNP.Outside.L_meta_2592_aux.Stronger.NegativeSeed
