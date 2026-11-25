namespace PEqualNP.Outside.L_meta_1886_aux.OverlappingOr

open PEqualNP.Outside.L_meta_2592_aux.Stronger
open PEqualNP.Outside.L_meta_2592_aux.Subgraphs

def seed : Extended.Sig := Extended.bin 1 (Extended.pins.getD 0 Extended.zero)
  (Extended.pins.getD 1 Extended.zero)

def bank (a p : Fin 10) : List Extended.Sig := Extended.pins ++
  [seed,Extended.bin 1 (Extended.pins.getD a.val Extended.zero) (Extended.pins.getD p.val Extended.zero)]

def low (p : Fin 10) : Extended.Row :=
  Extended.rowOfAssignment fun i => decide (i = 1 ∨ i = p)

def high (p : Fin 10) : Extended.Row :=
  Extended.rowOfAssignment fun i => decide (i = 0 ∨ i = 1 ∨ i = p)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma witness_checked : ∀ p : Fin 10, adjacent 1 p = false →
    Extended.bit (low p) Extended.target ≠ Extended.bit (high p) Extended.target ∧
      (bank 0 p).all (fun a => (Extended.bit (low p) a == Extended.bit (high p) a) ||
        (a == Extended.first)) = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma projected_bank : ∀ p : Fin 10,
    (bank 0 p).all (fun a => (projected a == zero) || inputs.contains (projected a)) = true := by
  decide +kernel

lemma shared_zero_needed (p : Fin 10) (hp : adjacent 1 p = false) {k S}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ bank 0 p) : Extended.first ∈ S := by
  obtain ⟨diff,stable⟩ := witness_checked p hp
  obtain ⟨a,ha,change⟩ := Extended.live_row_difference run diff
  have checked := List.all_eq_true.mp stable a (raw a ha)
  simp only [Bool.or_eq_true,beq_iff_eq] at checked
  exact checked.resolve_left change ▸ ha

lemma lower_zero (p : Fin 10) (hp : adjacent 1 p = false) {k S}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ bank 0 p) : 16 ≤ k := by
  classical
  have needed := shared_zero_needed p hp run raw
  let front := Extended.first :: (S.erase Extended.first).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨by simp,Finset.nodup_toList _⟩
  have eqS : front.toFinset = S := by
    ext a
    by_cases ha : a = Extended.first <;> simp [front,ha,needed]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows embed (Extended.observe Extended.target) = observe graph := by
    rw [observe_projected]
    exact congrArg observe (by decide +kernel)
  have isZero : observe zero = fun _ => false := by funext r; simp [observe,bit,zero]
  have supplyRoots : supply true (inputs.map observe) ((front.map Extended.observe).map (restrictRows embed)) := by
    intro v hv
    obtain ⟨_,hin,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmFront,rfl⟩ := List.mem_map.mp hin
    rw [observe_projected]
    have hh := List.all_eq_true.mp (projected_bank p) a (raw a (eqS ▸ List.mem_toFinset.mpr hmFront))
    simp only [Bool.or_eq_true,beq_iff_eq] at hh
    rcases hh with hz|hm
    · exact Or.inr (Or.inl ⟨false,hz ▸ isZero⟩)
    · exact Or.inl (List.mem_map.mpr ⟨_,by simpa using hm,rfl⟩)
  have need := projected_bound embed hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L:=15) (same ▸ nineFloor)
  have charge : 1 ≤ mass ((front.map Extended.observe).map (restrictRows embed)) := by
    have ac : Constant (restrictRows embed (Extended.observe Extended.first)) := by
      rw [observe_projected, show projected Extended.first=zero by decide +kernel]
      exact ⟨false,isZero⟩
    simp [front,mass_cons,cost,ac]
  omega

lemma lower_one (p : Fin 10) (hp : adjacent 0 p = false) {k S}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ bank 1 p) : 16 ≤ k := by
  classical
  let q := pairPerm 1 0
  have q0 : q 0 = 1 := pairMap_zero 1 0
  have q1 : q 1 = 0 := by change pairMap 1 0 1 = 0; decide +kernel
  have qa : ∀ a b, adjacent (q a) (q b) = adjacent a b := pairMap_adjacent 1 0
  have hq : adjacent 1 (q p) = false := by
    rw [←q0,qa]
    exact hp
  have pin0 : Extended.renameVertices q (Extended.pins.getD 0 Extended.zero) =
      Extended.pins.getD 1 Extended.zero := by
    simpa [q0] using (Extended.renameVertices_pin q (0 : Fin 10))
  have pin1 : Extended.renameVertices q (Extended.pins.getD 1 Extended.zero) =
      Extended.pins.getD 0 Extended.zero := by
    simpa [q1] using (Extended.renameVertices_pin q (1 : Fin 10))
  have seedSame : Extended.renameVertices q seed = seed := by
    unfold seed
    rw [Extended.renameVertices_bin,pin0,pin1]
    simp [Extended.bin,BitVec.or_comm]
  have extraSame : Extended.renameVertices q
      (Extended.bin 1 (Extended.pins.getD 1 Extended.zero) (Extended.pins.getD p.val Extended.zero)) =
      Extended.bin 1 (Extended.pins.getD 0 Extended.zero) (Extended.pins.getD (q p).val Extended.zero) := by
    rw [Extended.renameVertices_bin,pin1,Extended.renameVertices_pin q p]
  have tail : Extended.Live true Extended.target k (S.image (Extended.renameVertices q)) := by
    simpa only [Extended.renameVertices_target q qa] using Extended.live_renameVertices run q
  apply lower_zero (q p) hq tail
  intro v hv
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
  have hm := raw w hw
  simp only [bank,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm ⊢
  rcases hm with hpin | rfl | rfl
  · exact Or.inl (Extended.renameVertices_mem_pins q hpin)
  · exact Or.inr (Or.inl seedSame)
  · exact Or.inr (Or.inr extraSame)

end PEqualNP.Outside.L_meta_1886_aux.OverlappingOr
