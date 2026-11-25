import ExistingBinary16
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_2592_aux.Binary16
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma canonicalExtra_ne_first:∀(j:Fin 2)(d:Fin 4),
    canonicalExtra j d≠Extended.first:=by decide+kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma canonicalAndProjects:∀(j:Fin 2)(d:Fin 4),
    (d.val=0∨d.val=2)→projected(canonicalExtra j d)=zero:=by
  decide+kernel
lemma suffixSeventeenAnd(j:Fin 2)(d:Fin 4)(hd:d.val=0∨d.val=2){k S}
    (run:Extended.Live true Extended.target k S)
    (raw:∀ a∈S,a∈Extended.pins++[canonicalExtra j d])
    (hextra:canonicalExtra j d∈S):17≤k:=by
  classical
  have hfirst:=firstNeededCanonical j d run raw
  have hne:=canonicalExtra_ne_first j d
  let front:=Extended.first::canonicalExtra j d::
    ((S.erase Extended.first).erase(canonicalExtra j d)).toList
  have nd:front.Nodup:=by
    simp [front,hne,Ne.symm hne]
    exact Finset.nodup_toList _
  have eqS:front.toFinset=S:=by
    ext a
    by_cases ha:a=Extended.first<;>by_cases hb:a=canonicalExtra j d<;>
      simp [front,ha,hb,hfirst,hextra]
  have hrun:=Extended.list_run run front nd eqS
  have same:restrictRows embed(Extended.observe Extended.target)=observe graph:=by
    rw [observe_projected]
    exact congrArg observe(by decide+kernel)
  have isZero:observe zero=fun _=>false:=by funext r;simp [observe,bit,zero]
  have supplyRoots:supply true(inputs.map observe)
      ((front.map Extended.observe).map(restrictRows embed)):=by
    intro v hv
    obtain ⟨_,hin,rfl⟩:=List.mem_map.mp hv
    obtain ⟨a,hmFront,rfl⟩:=List.mem_map.mp hin
    rw [observe_projected]
    have hh:=List.all_eq_true.mp(canonicalProjects j d)a
      (raw a(eqS ▸ List.mem_toFinset.mpr hmFront))
    simp only [Bool.or_eq_true,beq_iff_eq] at hh
    rcases hh with hz|hm
    · exact Or.inr(Or.inl ⟨false,hz ▸ isZero⟩)
    · exact Or.inl(List.mem_map.mpr ⟨_,by simpa using hm,rfl⟩)
  have need:=projected_bound embed hrun(same ▸ observe_proper graph_proper)
    Reach.start supplyRoots(L:=15)(same ▸ nineFloor)
  have charge:2≤mass((front.map Extended.observe).map(restrictRows embed)):=by
    have ac:Constant(restrictRows embed(Extended.observe Extended.first)):=by
      rw [observe_projected,show projected Extended.first=zero by decide+kernel]
      exact ⟨false,isZero⟩
    have bc:Constant(restrictRows embed(Extended.observe(canonicalExtra j d))):=by
      rw [observe_projected,canonicalAndProjects j d hd]
      exact ⟨false,isZero⟩
    simp [front,mass_cons,cost,ac,bc]
    omega
  omega
end PEqualNP.Outside.L_meta_2592_aux.Binary16
