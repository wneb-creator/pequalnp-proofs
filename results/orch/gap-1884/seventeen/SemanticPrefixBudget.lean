import SemanticBudgetExtra

namespace PEqualNP.Outside.L_meta_6581

lemma prefix_projection_budget1884 {k p : Nat} {S T : Finset Extended.Sig}
    {bank : List (Wire Row)}
    (hfloor : Lower true inputs graph 15)
    (run : Extended.Live true Extended.target k S)
    (rows : Row → Extended.Row)
    (heq : restrictRows rows (Extended.observe Extended.target)=observe graph)
    (hT : T⊆S)
    (hconstant : ∀ a∈T,Constant (restrictRows rows (Extended.observe a)))
    (hreach : Reach true (inputs.map observe) p bank)
    (hsupply : ∀ a∈S,Available true bank (restrictRows rows (Extended.observe a))) :
    15+T.card≤p+k := by
  classical
  let front := T.toList ++ (S\T).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have eqS : front.toFinset=S := by
    ext a
    simp [front,Finset.union_sdiff_of_subset hT]
  have hrun := Extended.list_run run front nd eqS
  have supp : supply true bank ((front.map Extended.observe).map (restrictRows rows)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact hsupply a (eqS ▸ List.mem_toFinset.mpr ha)
  have bound := projected_bound rows hrun (heq ▸ observe_proper graph_proper)
    hreach supp (L:=15) (heq ▸ hfloor)
  have charge : T.card≤mass ((front.map Extended.observe).map (restrictRows rows)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (T.toList.map Extended.observe).map (restrictRows rows)
    have only : ∀ v∈xs,Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact hconstant a (Finset.mem_toList.mp ha)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change T.card≤mass xs+_
    rw [sz]
    omega
  omega

end PEqualNP.Outside.L_meta_6581
