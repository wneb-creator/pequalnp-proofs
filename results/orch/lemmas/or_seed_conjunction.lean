import PEqualNP.Outside.L_meta_2592

namespace PEqualNP.Outside.L_meta_2592_aux.Stronger.SeedConjunction

open Extended

def seed : Extended.Sig := Extended.bin 1 (Extended.pins.getD 0 Extended.zero)
  (Extended.pins.getD 1 Extended.zero)

def extra (q : Bool) (p : Fin 10) : Extended.Sig :=
  Extended.bin (if q then 0 else 2) seed (Extended.pins.getD p.val Extended.zero)

def bank (q : Bool) (p : Fin 10) := Extended.pins ++ [seed,extra q p]

def slice01 (r : Stronger.Row) : Extended.Row := Fin.ofNat 1024 (r.val &&& 383)

def projected01 (a : Extended.Sig) : Stronger.Sig :=
  Stronger.table fun r => Extended.bit (slice01 r) a

lemma observe_projected01 (a : Extended.Sig) :
    restrictRows slice01 (Extended.observe a) = Stronger.observe (projected01 a) := by
  funext r
  exact (Stronger.bit_table _ _).symm

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma projected_target : projected01 Extended.target = graphGoal 383 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma projected_bank : ∀ (q : Bool) (p : Fin 10),
    (bank q p).all (fun a => (projected01 a == Stronger.zero) ||
      (vars 383).contains (projected01 a)) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma projected_extra : ∀ (q : Bool) (p : Fin 10),
    projected01 (extra q p) = Stronger.zero := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma endpoint_witnesses : ∀ (q : Bool) (p : Fin 10), p ≠ 0 → p ≠ 1 →
    (bank q p).all (fun a => (Extended.bit 128 a == Extended.bit 640 a) ||
      (a == Extended.pins.getD 0 Extended.zero)) = true ∧
    (bank q p).all (fun a => (Extended.bit 512 a == Extended.bit 640 a) ||
      (a == Extended.pins.getD 1 Extended.zero)) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma extra_distinct : ∀ (q : Bool) (p : Fin 10), p ≠ 0 → p ≠ 1 →
    extra q p ≠ Extended.pins.getD 0 Extended.zero ∧
      extra q p ≠ Extended.pins.getD 1 Extended.zero := by decide +kernel

lemma endpoints_needed (q : Bool) (p : Fin 10) (h0 : p ≠ 0) (h1 : p ≠ 1) {k S}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ bank q p) :
    Extended.pins.getD 0 Extended.zero ∈ S ∧ Extended.pins.getD 1 Extended.zero ∈ S := by
  have tests := endpoint_witnesses q p h0 h1
  have firstDiff : Extended.bit 128 Extended.target ≠ Extended.bit 640 Extended.target := by decide +kernel
  have secondDiff : Extended.bit 512 Extended.target ≠ Extended.bit 640 Extended.target := by decide +kernel
  constructor
  · obtain ⟨a,ha,hd⟩ := Extended.live_row_difference run firstDiff
    have hh := List.all_eq_true.mp tests.1 a (raw a ha)
    simp only [Bool.or_eq_true,beq_iff_eq] at hh
    exact hh.resolve_left hd ▸ ha
  · obtain ⟨a,ha,hd⟩ := Extended.live_row_difference run secondDiff
    have hh := List.all_eq_true.mp tests.2 a (raw a ha)
    simp only [Bool.or_eq_true,beq_iff_eq] at hh
    exact hh.resolve_left hd ▸ ha

lemma lower (q : Bool) (p : Fin 10) (h0 : p ≠ 0) (h1 : p ≠ 1) {k S}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ bank q p) (used : extra q p ∈ S) : 16 ≤ k := by
  classical
  obtain ⟨needed0,needed1⟩ := endpoints_needed q p h0 h1 run raw
  obtain ⟨ne0,ne1⟩ := extra_distinct q p h0 h1
  have different : Extended.pins.getD 0 Extended.zero ≠ Extended.pins.getD 1 Extended.zero := by decide +kernel
  let front := Extended.pins.getD 0 Extended.zero :: Extended.pins.getD 1 Extended.zero :: extra q p ::
    (((S.erase (Extended.pins.getD 0 Extended.zero)).erase
      (Extended.pins.getD 1 Extended.zero)).erase (extra q p)).toList
  have nd : front.Nodup := by
    simp [front,different,different.symm,ne0,ne0.symm,ne1,ne1.symm,Finset.nodup_toList,-List.getD_eq_getElem?_getD]
  have eqS : front.toFinset = S := by
    ext a
    by_cases ha : a = Extended.pins.getD 0 Extended.zero <;>
      by_cases hb : a = Extended.pins.getD 1 Extended.zero <;>
      by_cases hc : a = extra q p <;> simp [front,ha,hb,hc,needed0,needed1,used,-List.getD_eq_getElem?_getD]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows slice01 (Extended.observe Extended.target) = Stronger.observe (graphGoal 383) := by
    rw [observe_projected01,projected_target]
  have properGoal : Stronger.proper (graphGoal 383) := by unfold Stronger.proper; decide +kernel
  have isZero : Stronger.observe Stronger.zero = fun _ => false := by
    funext r
    simp [Stronger.observe,Stronger.bit,Stronger.zero]
  have roots : supply true ((vars 383).map Stronger.observe)
      ((front.map Extended.observe).map (restrictRows slice01)) := by
    intro v hv
    obtain ⟨_,hin,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hm,rfl⟩ := List.mem_map.mp hin
    rw [observe_projected01]
    have hh := List.all_eq_true.mp (projected_bank q p) a
      (raw a (eqS ▸ List.mem_toFinset.mpr hm))
    simp only [Bool.or_eq_true,beq_iff_eq] at hh
    rcases hh with hz | hm
    · exact Or.inr (Or.inl ⟨false,hz ▸ isZero⟩)
    · exact Or.inl (List.mem_map.mpr ⟨_,by simpa using hm,rfl⟩)
  have need := projected_bound slice01 hrun (same ▸ Stronger.observe_proper properGoal)
    Reach.start roots (L:=13) (same ▸ low383)
  have charge : 3 ≤ mass ((front.map Extended.observe).map (restrictRows slice01)) := by
    have c0 : Constant (restrictRows slice01 (Extended.observe (Extended.pins.getD 0 Extended.zero))) := by
      rw [observe_projected01,show projected01 (Extended.pins.getD 0 Extended.zero)=Stronger.zero by decide +kernel]
      exact ⟨false,isZero⟩
    have c1 : Constant (restrictRows slice01 (Extended.observe (Extended.pins.getD 1 Extended.zero))) := by
      rw [observe_projected01,show projected01 (Extended.pins.getD 1 Extended.zero)=Stronger.zero by decide +kernel]
      exact ⟨false,isZero⟩
    have ce : Constant (restrictRows slice01 (Extended.observe (extra q p))) := by
      rw [observe_projected01,projected_extra]
      exact ⟨false,isZero⟩
    simp only [front,List.map_cons,List.map_map,mass_cons,cost,c0,c1,ce,ite_true]
    omega
  omega

end PEqualNP.Outside.L_meta_2592_aux.Stronger.SeedConjunction
