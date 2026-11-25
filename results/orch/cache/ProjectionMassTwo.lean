import FewNotBase

namespace PEqualNP.Outside.L_meta_2592.FewNot

lemma projection_seventeen {k S} (run : Extended.Live true Extended.target k S)
    (a b : Extended.Sig) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (rows : Row → Extended.Row)
    (same : restrictRows rows (Extended.observe Extended.target) = observe graph)
    (supplied : ∀ v ∈ S,
      Available true (inputs.map observe) (restrictRows rows (Extended.observe v)))
    (constantA : Constant (restrictRows rows (Extended.observe a)))
    (constantB : Constant (restrictRows rows (Extended.observe b))) : 17 ≤ k := by
  classical
  let front := a :: b :: ((S.erase a).erase b).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_cons, List.mem_cons, Finset.mem_toList,
      Finset.mem_erase, not_or]
    exact ⟨⟨hab,fun h => h.2.1 rfl⟩,⟨fun h => h.1 rfl,Finset.nodup_toList _⟩⟩
  have eqS : front.toFinset = S := by
    ext v
    by_cases hva : v = a
    · subst v
      simp [front,ha]
    by_cases hvb : v = b
    · subst v
      simp [front,hb]
    simp [front,hva,hvb]
  have hrun := Extended.list_run run front nd eqS
  have supplyRoots : supply true (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows rows)) := by
    intro v hv
    obtain ⟨_,hin,rfl⟩ := List.mem_map.mp hv
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hin
    exact supplied z (eqS ▸ List.mem_toFinset.mpr hz)
  have need := projected_bound rows hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L := 15) (same ▸ nineFloor)
  have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows rows)) := by
    simp only [front,List.map_cons,mass_cons,cost,ite_eq_left constantA,ite_eq_left constantB]
    omega
  omega

end PEqualNP.Outside.L_meta_2592.FewNot
