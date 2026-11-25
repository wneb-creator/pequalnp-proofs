import GlobalData
import GlobalWitness



namespace PEqualNP.Outside.Pilot113FirstStep

open PEqualNP.Outside.L_meta_6581

abbrev pin (j : Fin 10) : Extended.Sig := Extended.pins.getD j.val Extended.zero

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma initial_eq_ofFn : Extended.initial = List.ofFn pin := by
  decide +kernel

lemma raw_index {a : Extended.Sig} (ha : a ∈ Extended.initial) :
    ∃ i : Fin 10, pin i = a := by
  rw [initial_eq_ofFn] at ha
  exact List.mem_ofFn.mp ha

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma target_not_raw : Extended.target ∉ Extended.initial := by
  decide +kernel

lemma live_first_split {k : Nat} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) :
    ∃ (n : Nat) (U : Finset Extended.Sig) (i j : Fin 10) (d : Nat),
      k = n + 1 ∧ i ≠ j ∧ Extended.allowed true d ∧
      (∀ a ∈ U, a ∈ Extended.initial) ∧
      Extended.Live true Extended.target n (insert (Extended.bin d (pin i) (pin j)) U) := by
  cases k with
  | zero =>
    obtain ⟨rfl, _⟩ := run
    exact False.elim (target_not_raw (raw _ (Finset.mem_singleton_self _)))
  | succ n =>
    obtain ⟨U, a, b, d, hd, rfl, _, _, hab, _, tailRun⟩ := run
    obtain ⟨i, rfl⟩ := raw_index (raw a (Finset.mem_insert_self _ _))
    obtain ⟨j, rfl⟩ := raw_index (raw b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
    refine ⟨n, U, i, j, d, rfl, ?_, hd, ?_, tailRun⟩
    · intro h
      exact hab (congrArg pin h)
    · intro a ha
      exact raw a (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha))

lemma all_first_steps_floor
    (firstBound : ∀ (n : Nat) (U : Finset Extended.Sig) (i j : Fin 10) (d : Nat),
      i ≠ j → Extended.allowed true d →
      (∀ a ∈ U, a ∈ Extended.initial) →
      Extended.Live true Extended.target n (insert (Extended.bin d (pin i) (pin j)) U) →
      17 ≤ n + 1)
    {k : Nat} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) : 17 ≤ k := by
  obtain ⟨n, U, i, j, d, rfl, hij, hd, hraw, htail⟩ := live_first_split run raw
  exact firstBound n U i j d hij hd hraw htail

end PEqualNP.Outside.Pilot113FirstStep


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


namespace PEqualNP.Outside.Pilot113GlobalCount

open PEqualNP.Outside.L_meta_6581 PEqualNP.CircuitLowerBounds

lemma atLeastSeventeen (hNineFloor : Lower true inputs graph 15)
    {k : Nat} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) : 17 ≤ k := by
  apply Pilot113FirstStep.all_first_steps_floor (run := run) (raw := raw)
  intro n U i j d hij hd hraw htail
  rcases Extended.allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · have bound := Pilot113GlobalAnd.first_and_eighteen hNineFloor
      0 (Or.inl rfl) i j hij hraw htail
    omega
  · exact Pilot113GlobalOr.first_or_seventeen hNineFloor i j hij hraw htail
  · have bound := Pilot113GlobalAnd.first_and_eighteen hNineFloor
      2 (Or.inr rfl) i j hij hraw htail
    omega
  · have flip : Extended.bin 3 (Pilot113FirstStep.pin i) (Pilot113FirstStep.pin j) =
        Extended.bin 2 (Pilot113FirstStep.pin j) (Pilot113FirstStep.pin i) := by
      simp [Extended.bin, BitVec.and_comm]
    rw [flip] at htail
    have bound := Pilot113GlobalAnd.first_and_eighteen hNineFloor
      2 (Or.inr rfl) j i (Ne.symm hij) hraw htail
    omega

lemma nonNot_seventeen (hNineFloor : Lower true inputs graph 15)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    17 ≤ C.gates.countP (fun g => !Extended.isNot g) := by
  obtain ⟨k, S, hk, run, raw⟩ := Extended.realize C legal computes
  exact le_trans (atLeastSeventeen hNineFloor run raw) hk

lemma three_not_impossible (hNineFloor : Lower true inputs graph 15)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (small : C.size ≤ 19) (many : 3 ≤ PEqualNP.NotBracket.notCount C) :
    ∃ x : Fin 10 → Bool, C.eval (List.ofFn x) ≠ Extended.f10 x := by
  by_contra! computes
  have floor := nonNot_seventeen hNineFloor C legal computes
  have sameNot :
      (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)) =
        Extended.isNot := by
    funext g
    obtain ⟨op, operands⟩ := g
    cases op <;> rfl
  rw [PEqualNP.NotBracket.notCount, sameNot, ← List.countP_eq_length_filter] at many
  have negSame : (fun g : Gate => decide (¬ Extended.isNot g = true)) =
      (fun g => !Extended.isNot g) := by
    funext g
    cases Extended.isNot g <;> rfl
  have count := List.length_eq_countP_add_countP Extended.isNot (l := C.gates)
  rw [negSame] at count
  change C.gates.length ≤ 19 at small
  omega

end PEqualNP.Outside.Pilot113GlobalCount
