import PEqualNP.Outside.L_meta_6581

namespace PEqualNP.Outside.Pilot113GlobalAnd

open PEqualNP.Outside.L_meta_6581
open PEqualNP.Outside.Pilot113GlobalData

lemma first_and_zero (op : Fin 3) (hop : op = 0 ∨ op = 2) (i j : Fin 10) :
    restrictRows (embedAt i) (Extended.observe (Extended.bin op.val (pin i) (pin j))) =
      fun _ => false := by
  rw [Extended.obs_bin, restrict_comb, chosen_pin_zero]
  rcases hop with rfl | rfl <;> funext r <;> simp [comb, combine]

lemma first_and_tail_seventeen (hNineFloor : Lower true inputs graph 15)
    (op : Fin 3) (hop : op = 0 ∨ op = 2)
    (i j : Fin 10) (hij : i ≠ j) {k : ℕ} {T : Finset Extended.Sig}
    (tailRun : Extended.Live true Extended.target k T)
    (firstPresent : pin i ∈ T)
    (andPresent : Extended.bin op.val (pin i) (pin j) ∈ T)
    (raw : ∀ a ∈ T, a ∈ Extended.initial ∨ a = Extended.bin op.val (pin i) (pin j)) :
    17 ≤ k := by
  classical
  let gate := Extended.bin op.val (pin i) (pin j)
  have distinct : gate ≠ pin i :=
    (PEqualNP.Outside.Pilot113GlobalWitness.witness_data i op j hij).2.2.2
  have gatePresent : gate ∈ T := andPresent
  let front := pin i :: gate :: ((T.erase (pin i)).erase gate).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, Finset.nodup_toList _⟩⟩
    · intro hm
      rcases List.mem_cons.mp hm with he | he
      · exact distinct he.symm
      · exact (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_toList.mp he)).2).1 rfl
    · intro hm
      exact (Finset.mem_erase.mp (Finset.mem_toList.mp hm)).1 rfl
  have eqT : front.toFinset = T := by
    simp only [front, List.toFinset_cons, Finset.toList_toFinset]
    have hgate : gate ∈ T.erase (pin i) := Finset.mem_erase.mpr ⟨distinct, gatePresent⟩
    rw [Finset.insert_erase hgate, Finset.insert_erase firstPresent]
  have hrun := Extended.list_run tailRun front nd eqT
  have same := target_restriction i
  have supplyRoots : supply true (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows (embedAt i))) := by
    intro v hv
    obtain ⟨_, hin, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, hmFront, rfl⟩ := List.mem_map.mp hin
    rcases raw a (eqT ▸ List.mem_toFinset.mpr hmFront) with hr | rfl
    · obtain ⟨q, rfl⟩ := PEqualNP.Outside.Pilot113FirstStep.raw_index hr
      exact pin_available i q
    · exact Or.inr (Or.inl ⟨false, first_and_zero op hop i j⟩)
  have need := projected_bound (embedAt i) hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L := 15) (same ▸ hNineFloor)
  have charge : 2 ≤ mass
      ((front.map Extended.observe).map (restrictRows (embedAt i))) := by
    have ac : Constant (restrictRows (embedAt i) (Extended.observe (pin i))) :=
      ⟨false, chosen_pin_zero i⟩
    have bc : Constant (restrictRows (embedAt i) (Extended.observe gate)) :=
      ⟨false, first_and_zero op hop i j⟩
    change 2 ≤ cost (restrictRows (embedAt i) (Extended.observe (pin i))) +
      (cost (restrictRows (embedAt i) (Extended.observe gate)) +
        mass ((((T.erase (pin i)).erase gate).toList.map Extended.observe).map
          (restrictRows (embedAt i))))
    rw [cost, if_pos ac, cost, if_pos bc]
    omega
  omega

lemma first_and_eighteen (hNineFloor : Lower true inputs graph 15)
    (op : Fin 3) (hop : op = 0 ∨ op = 2)
    (i j : Fin 10) (hij : i ≠ j) {k : ℕ} {U : Finset Extended.Sig}
    (raw : ∀ a ∈ U, a ∈ Extended.initial)
    (tailRun : Extended.Live true Extended.target k
      (insert (Extended.bin op.val (pin i) (pin j)) U)) :
    18 ≤ k + 1 := by
  have firstPresent :=
    PEqualNP.Outside.Pilot113GlobalWitness.first_pin_retained op i j hij raw tailRun
  have floor := first_and_tail_seventeen hNineFloor op hop i j hij tailRun
    (Finset.mem_insert_of_mem firstPresent) (Finset.mem_insert_self _ _) (by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact Or.inr rfl
      · exact Or.inl (raw a ha))
  omega

end PEqualNP.Outside.Pilot113GlobalAnd
