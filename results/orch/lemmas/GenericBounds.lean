import CombinedOrdinary

namespace PEqualNP.Outside.Pilot113GenericBounds

open PEqualNP.Outside.L_meta_6581
open PEqualNP.Outside.Pilot113GlobalData

lemma pin_available_mode {u : Bool} (i j : Fin 10) : Available u (inputs.map observe)
    (restrictRows (embedAt i) (Extended.observe (pin j))) := by
  rw [pin_restriction]
  by_cases h : (inputPos (vertexAut i j)).val < inputs.length
  · apply Or.inl
    apply List.mem_map.mpr
    refine ⟨_, ?_, rfl⟩
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem _
  · apply Or.inr
    apply Or.inl
    rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    refine ⟨false, ?_⟩
    funext r
    simp [observe, bit, zero]

lemma first_pin_retained {u : Bool} (op : Fin 3) (i j : Fin 10) (hij : i ≠ j)
    {k : Nat} {U : Finset Extended.Sig}
    (raw : ∀ a ∈ U, a ∈ Extended.initial)
    (tailRun : Extended.Live u Extended.target k
      (insert (Extended.bin op.val (pin i) (pin j)) U)) : pin i ∈ U := by
  obtain ⟨different, same, onlyFirst, _⟩ := Pilot113GlobalWitness.witness_data i op j hij
  obtain ⟨a, ha, changes⟩ := Extended.live_row_difference tailRun different
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact False.elim (changes same)
  · have h := List.all_eq_true.mp onlyFirst a (raw a ha)
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    have hp : a = pin i := h.resolve_right changes
    exact hp ▸ ha

lemma live_first_split {u : Bool} {k : Nat} {S : Finset Extended.Sig}
    (run : Extended.Live u Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) :
    ∃ (n : Nat) (U : Finset Extended.Sig) (i j : Fin 10) (d : Nat),
      k = n + 1 ∧ i ≠ j ∧ Extended.allowed u d ∧
      (∀ a ∈ U, a ∈ Extended.initial) ∧
      Extended.Live u Extended.target n (insert (Extended.bin d (pin i) (pin j)) U) := by
  cases k with
  | zero =>
    obtain ⟨rfl, _⟩ := run
    exact False.elim (Pilot113FirstStep.target_not_raw (raw _ (Finset.mem_singleton_self _)))
  | succ n =>
    obtain ⟨U, a, b, d, hd, rfl, _, _, hab, _, tailRun⟩ := run
    obtain ⟨i, rfl⟩ := Pilot113FirstStep.raw_index (raw a (Finset.mem_insert_self _ _))
    obtain ⟨j, rfl⟩ := Pilot113FirstStep.raw_index (raw b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
    refine ⟨n, U, i, j, d, rfl, ?_, hd, ?_, tailRun⟩
    · intro h
      exact hab (congrArg pin h)
    · intro a ha
      exact raw a (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha))


lemma restricted_or (i j : Fin 10) :
    restrictRows (embedAt i) (Extended.observe (Extended.bin 1 (pin i) (pin j))) =
      restrictRows (embedAt i) (Extended.observe (pin j)) := by
  rw [Extended.obs_bin, restrict_comb, chosen_pin_zero]
  funext r
  simp [comb, combine]

lemma first_or_tail_floor {u : Bool} {L : Nat} (hFloor : Lower u inputs graph L)
    (i j : Fin 10) {k : Nat} {T : Finset Extended.Sig}
    (tailRun : Extended.Live u Extended.target k T)
    (firstPresent : pin i ∈ T)
    (raw : ∀ a ∈ T, a ∈ Extended.initial ∨ a = Extended.bin 1 (pin i) (pin j)) :
    L + 1 ≤ k := by
  classical
  let front := pin i :: (T.erase (pin i)).toList
  have nd : front.Nodup := by
    exact List.nodup_cons.mpr ⟨by simp, Finset.nodup_toList _⟩
  have eqT : front.toFinset = T := by
    simp only [front, List.toFinset_cons, Finset.toList_toFinset]
    exact Finset.insert_erase firstPresent
  have hrun := Extended.list_run tailRun front nd eqT
  have same := target_restriction i
  have supplyRoots : supply u (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows (embedAt i))) := by
    intro v hv
    obtain ⟨_, hin, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, hmFront, rfl⟩ := List.mem_map.mp hin
    rcases raw a (eqT ▸ List.mem_toFinset.mpr hmFront) with hr | rfl
    · obtain ⟨j, rfl⟩ := Pilot113FirstStep.raw_index hr
      exact pin_available_mode i j
    · rw [restricted_or]
      exact pin_available_mode i j
  have need := projected_bound (embedAt i) hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L := L) (same ▸ hFloor)
  have charge : 1 ≤ mass ((front.map Extended.observe).map (restrictRows (embedAt i))) := by
    have ac : Constant (restrictRows (embedAt i) (Extended.observe (pin i))) :=
      ⟨false, chosen_pin_zero i⟩
    change 1 ≤ cost (restrictRows (embedAt i) (Extended.observe (pin i))) +
      mass (((T.erase (pin i)).toList.map Extended.observe).map (restrictRows (embedAt i)))
    rw [cost, if_pos ac]
    omega
  omega

lemma first_or_floor {u : Bool} {L : Nat} (hFloor : Lower u inputs graph L)
    (i j : Fin 10) (hij : i ≠ j) {k : Nat} {U : Finset Extended.Sig}
    (raw : ∀ a ∈ U, a ∈ Extended.initial)
    (tailRun : Extended.Live u Extended.target k
      (insert (Extended.bin 1 (pin i) (pin j)) U)) :
    L + 2 ≤ k + 1 := by
  have retained := first_pin_retained 1 i j hij raw tailRun
  have floor := first_or_tail_floor hFloor i j tailRun
    (Finset.mem_insert_of_mem retained) (by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact Or.inr rfl
      · exact Or.inl (raw a ha))
  omega


lemma first_and_zero (op : Fin 3) (hop : op = 0 ∨ op = 2) (i j : Fin 10) :
    restrictRows (embedAt i) (Extended.observe (Extended.bin op.val (pin i) (pin j))) =
      fun _ => false := by
  rw [Extended.obs_bin, restrict_comb, chosen_pin_zero]
  rcases hop with rfl | rfl <;> funext r <;> simp [comb, combine]

lemma first_and_tail_floor {u : Bool} {L : Nat} (hFloor : Lower u inputs graph L)
    (op : Fin 3) (hop : op = 0 ∨ op = 2)
    (i j : Fin 10) (hij : i ≠ j) {k : ℕ} {T : Finset Extended.Sig}
    (tailRun : Extended.Live u Extended.target k T)
    (firstPresent : pin i ∈ T)
    (andPresent : Extended.bin op.val (pin i) (pin j) ∈ T)
    (raw : ∀ a ∈ T, a ∈ Extended.initial ∨ a = Extended.bin op.val (pin i) (pin j)) :
    L + 2 ≤ k := by
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
  have supplyRoots : supply u (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows (embedAt i))) := by
    intro v hv
    obtain ⟨_, hin, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, hmFront, rfl⟩ := List.mem_map.mp hin
    rcases raw a (eqT ▸ List.mem_toFinset.mpr hmFront) with hr | rfl
    · obtain ⟨q, rfl⟩ := PEqualNP.Outside.Pilot113FirstStep.raw_index hr
      exact pin_available_mode i q
    · exact Or.inr (Or.inl ⟨false, first_and_zero op hop i j⟩)
  have need := projected_bound (embedAt i) hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L := L) (same ▸ hFloor)
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

lemma first_and_floor {u : Bool} {L : Nat} (hFloor : Lower u inputs graph L)
    (op : Fin 3) (hop : op = 0 ∨ op = 2)
    (i j : Fin 10) (hij : i ≠ j) {k : ℕ} {U : Finset Extended.Sig}
    (raw : ∀ a ∈ U, a ∈ Extended.initial)
    (tailRun : Extended.Live u Extended.target k
      (insert (Extended.bin op.val (pin i) (pin j)) U)) :
    L + 3 ≤ k + 1 := by
  have firstPresent :=
    first_pin_retained op i j hij raw tailRun
  have floor := first_and_tail_floor hFloor op hop i j hij tailRun
    (Finset.mem_insert_of_mem firstPresent) (Finset.mem_insert_self _ _) (by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact Or.inr rfl
      · exact Or.inl (raw a ha))
  omega


lemma two_more {u : Bool} {L : Nat} (hFloor : Lower u inputs graph L)
    {k : Nat} {S : Finset Extended.Sig}
    (run : Extended.Live u Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) : L + 2 ≤ k := by
  obtain ⟨n, U, i, j, d, rfl, hij, hd, hraw, htail⟩ := live_first_split run raw
  rcases Extended.allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · have bound := first_and_floor hFloor 0 (Or.inl rfl) i j hij hraw htail
    omega
  · exact first_or_floor hFloor i j hij hraw htail
  · have bound := first_and_floor hFloor 2 (Or.inr rfl) i j hij hraw htail
    omega
  · have flip : Extended.bin 3 (pin i) (pin j) = Extended.bin 2 (pin j) (pin i) := by
      simp [Extended.bin, BitVec.and_comm]
    rw [flip] at htail
    have bound := first_and_floor hFloor 2 (Or.inr rfl) j i (Ne.symm hij) hraw htail
    omega

lemma signed_seventeen {k : Nat} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) : 17 ≤ k :=
  two_more nineFloor run raw

lemma monotone_eighteen (hMonoFloor : Lower false inputs graph 16)
    {k : Nat} {S : Finset Extended.Sig}
    (run : Extended.Live false Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) : 18 ≤ k :=
  two_more hMonoFloor run raw

end PEqualNP.Outside.Pilot113GenericBounds
