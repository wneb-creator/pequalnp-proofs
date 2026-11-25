import PEqualNP.Outside.L_meta_6581

namespace PEqualNP.Outside.Pilot113GlobalOr

open PEqualNP.Outside.L_meta_6581
open PEqualNP.Outside.Pilot113GlobalData

lemma restricted_or (i j : Fin 10) :
    restrictRows (embedAt i) (Extended.observe (Extended.bin 1 (pin i) (pin j))) =
      restrictRows (embedAt i) (Extended.observe (pin j)) := by
  rw [Extended.obs_bin, restrict_comb, chosen_pin_zero]
  funext r
  simp [comb, combine]

lemma first_or_tail_sixteen (hNineFloor : Lower true inputs graph 15)
    (i j : Fin 10) {k : Nat} {T : Finset Extended.Sig}
    (tailRun : Extended.Live true Extended.target k T)
    (firstPresent : pin i ∈ T)
    (raw : ∀ a ∈ T, a ∈ Extended.initial ∨ a = Extended.bin 1 (pin i) (pin j)) :
    16 ≤ k := by
  classical
  let front := pin i :: (T.erase (pin i)).toList
  have nd : front.Nodup := by
    exact List.nodup_cons.mpr ⟨by simp, Finset.nodup_toList _⟩
  have eqT : front.toFinset = T := by
    simp only [front, List.toFinset_cons, Finset.toList_toFinset]
    exact Finset.insert_erase firstPresent
  have hrun := Extended.list_run tailRun front nd eqT
  have same := target_restriction i
  have supplyRoots : supply true (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows (embedAt i))) := by
    intro v hv
    obtain ⟨_, hin, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, hmFront, rfl⟩ := List.mem_map.mp hin
    rcases raw a (eqT ▸ List.mem_toFinset.mpr hmFront) with hr | rfl
    · obtain ⟨j, rfl⟩ := Pilot113FirstStep.raw_index hr
      exact pin_available i j
    · rw [restricted_or]
      exact pin_available i j
  have need := projected_bound (embedAt i) hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L := 15) (same ▸ hNineFloor)
  have charge : 1 ≤ mass ((front.map Extended.observe).map (restrictRows (embedAt i))) := by
    have ac : Constant (restrictRows (embedAt i) (Extended.observe (pin i))) :=
      ⟨false, chosen_pin_zero i⟩
    change 1 ≤ cost (restrictRows (embedAt i) (Extended.observe (pin i))) +
      mass (((T.erase (pin i)).toList.map Extended.observe).map (restrictRows (embedAt i)))
    rw [cost, if_pos ac]
    omega
  omega

lemma first_or_seventeen (hNineFloor : Lower true inputs graph 15)
    (i j : Fin 10) (hij : i ≠ j) {k : Nat} {U : Finset Extended.Sig}
    (raw : ∀ a ∈ U, a ∈ Extended.initial)
    (tailRun : Extended.Live true Extended.target k
      (insert (Extended.bin 1 (pin i) (pin j)) U)) :
    17 ≤ k + 1 := by
  have retained := Pilot113GlobalWitness.first_pin_retained 1 i j hij raw tailRun
  have floor := first_or_tail_sixteen hNineFloor i j tailRun
    (Finset.mem_insert_of_mem retained) (by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact Or.inr rfl
      · exact Or.inl (raw a ha))
  omega

end PEqualNP.Outside.Pilot113GlobalOr
