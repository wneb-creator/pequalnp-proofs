import CombinatorialStrong

namespace PEqualNP.Outside.L_meta_2592_aux

namespace Extended
def retentionMasks : List Nat :=
  [0, 0, 64, 128, 128, 96, 128, 384, 128, 64, 128, 16, 128, 68, 128, 129, 128, 136, 128, 130, 32, 512, 0, 0, 512, 32, 512, 768, 512, 96, 512, 48, 512, 4, 512, 513, 512, 520, 512, 514, 128, 768, 256, 128, 0, 0, 128, 256, 128, 192, 128, 144, 128, 260, 128, 1, 128, 136, 128, 130, 32, 544, 32, 192, 64, 32, 0, 0, 32, 64, 32, 48, 32, 36, 32, 65, 32, 8, 32, 34, 256, 512, 512, 384, 512, 544, 512, 256, 0, 0, 512, 272, 512, 516, 512, 513, 512, 520, 512, 2, 1, 512, 512, 129, 512, 544, 512, 768, 512, 65, 0, 0, 512, 516, 512, 1, 512, 8, 512, 514, 128, 520, 8, 128, 128, 40, 128, 384, 128, 192, 128, 144, 0, 0, 128, 129, 128, 8, 128, 2, 32, 544, 32, 144, 16, 32, 32, 272, 32, 96, 32, 16, 32, 36, 0, 0, 32, 40, 32, 2, 256, 768, 256, 384, 256, 48, 16, 256, 256, 80, 256, 16, 256, 4, 256, 257, 0, 0, 256, 258, 64, 516, 64, 192, 64, 96, 64, 260, 4, 64, 64, 80, 64, 4, 64, 1, 64, 72, 0, 0]

def retentionPlaces : List Nat := [9, 7, 5, 8, 6, 4, 2, 0, 3, 1]

def retentionLow (i j : Fin 10) (d : Fin 4) : Row :=
  ⟨(retentionMasks.getD (i.val * 20 + j.val * 2 + if d.val = 1 ∨ d.val = 2 then 1 else 0) 0) % 1024,
    Nat.mod_lt _ (by decide)⟩

def retentionHigh (i j : Fin 10) (d : Fin 4) : Row :=
  ⟨(retentionLow i j d + 2 ^ retentionPlaces.getD i.val 0) % 1024, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma retention_checked : ∀ (i j : Fin 10) (d : Fin 4), i ≠ j →
    bit (retentionLow i j d) target ≠ bit (retentionHigh i j d) target ∧
    bit (retentionLow i j d) (bin d.val (pins.getD i.val zero) (pins.getD j.val zero)) =
      bit (retentionHigh i j d) (bin d.val (pins.getD i.val zero) (pins.getD j.val zero)) ∧
    ∀ v : Fin 10, v ≠ i →
      bit (retentionLow i j d) (pins.getD v.val zero) =
        bit (retentionHigh i j d) (pins.getD v.val zero) := by
  decide +kernel

lemma retention_witness (i j : Fin 10) (h : i ≠ j) (d : Fin 4) :
    ∃ r s : Row, bit r target ≠ bit s target ∧
      bit r (bin d.val (pins.getD i.val zero) (pins.getD j.val zero)) =
        bit s (bin d.val (pins.getD i.val zero) (pins.getD j.val zero)) ∧
      ∀ v : Fin 10, v ≠ i → bit r (pins.getD v.val zero) = bit s (pins.getD v.val zero) :=
  ⟨retentionLow i j d, retentionHigh i j d, retention_checked i j d h⟩

end Extended

namespace Seventeen

def rowPositions : List Nat := [9,7,5,8,6,4,2,0,3,1]
def vertexPermutations : List (List Nat) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [1, 0, 5, 8, 6, 2, 4, 7, 3, 9], [9, 4, 0, 1, 6, 7, 3, 5, 2, 8], [9, 7, 5, 0, 4, 6, 2, 8, 1, 3], [1, 2, 3, 4, 0, 6, 7, 8, 9, 5], [1, 2, 3, 8, 6, 0, 7, 4, 5, 9], [9, 4, 3, 8, 6, 7, 0, 2, 5, 1], [9, 7, 5, 8, 6, 4, 2, 0, 3, 1], [9, 7, 2, 1, 6, 4, 5, 3, 0, 8], [9, 7, 2, 3, 4, 6, 5, 1, 8, 0]]
def sliceRow (i : Fin 10) (r : Row) : Extended.Row :=
  ⟨((List.range 10).foldl (fun acc j =>
    if r.val.testBit (rowPositions.getD ((vertexPermutations.getD i.val []).getD j 0) 0)
    then acc + 2 ^ (rowPositions.getD j 0) else acc) 0) % 1024,
    Nat.mod_lt _ (by decide)⟩
def projectAt (i : Fin 10) (a : Extended.Sig) : Sig :=
  table (fun r => Extended.bit (sliceRow i r) a)

lemma observe_projectAt (i : Fin 10) (a : Extended.Sig) :
    restrictRows (sliceRow i) (Extended.observe a) = observe (projectAt i a) := by
  exact (observe_table _).symm

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma slice_target : ∀ i : Fin 10, projectAt i Extended.target = graph := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma slice_inputs : ∀ i : Fin 10,
    Extended.pins.all (fun a => (projectAt i a == zero) || inputs.contains (projectAt i a)) = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma slice_self : ∀ i : Fin 10,
    projectAt i (Extended.pins.getD i.val Extended.zero) = zero := by
  decide +kernel

lemma slice_available (i : Fin 10) {a : Extended.Sig} (ha : a ∈ Extended.pins) :
    Available true (inputs.map observe) (restrictRows (sliceRow i) (Extended.observe a)) := by
  rw [observe_projectAt]
  have hh := List.all_eq_true.mp (slice_inputs i) a ha
  simp only [Bool.or_eq_true,beq_iff_eq] at hh
  rcases hh with hz | hm
  · exact Or.inr (Or.inl ⟨false, by rw [hz]; funext r; simp [observe,bit,zero]⟩)
  · exact Or.inl (List.mem_map.mpr ⟨_,by simpa using hm,rfl⟩)

lemma pin_index {a : Extended.Sig} (ha : a ∈ Extended.pins) :
    ∃ i : Fin 10, Extended.pins.getD i.val Extended.zero = a := by
  simp only [Extended.pins,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩
  · exact ⟨5,rfl⟩
  · exact ⟨6,rfl⟩
  · exact ⟨7,rfl⟩
  · exact ⟨8,rfl⟩
  · exact ⟨9,rfl⟩

lemma first_retained {k : Nat} {U : Finset Extended.Sig} {a b : Extended.Sig} {d : Nat}
    (hd : Extended.allowed true d) (hab : a ≠ b)
    (raw : ∀ v ∈ insert a (insert b U), v ∈ Extended.pins)
    (run : Extended.Live true Extended.target k (insert (Extended.bin d a b) U)) : a ∈ U := by
  obtain ⟨i,hi⟩ := pin_index (raw a (by simp))
  obtain ⟨j,hj⟩ := pin_index (raw b (by simp))
  have hij : i ≠ j := by
    intro eq
    subst j
    exact hab (hi.symm.trans hj)
  have dd : d < 4 := by rcases hd with h | ⟨_,h⟩ <;> omega
  obtain ⟨r,s,diff,same,stable⟩ := Extended.retention_witness i j hij ⟨d,dd⟩
  rw [hi,hj] at same
  by_contra absent
  obtain ⟨v,hv,change⟩ := Extended.live_row_difference run diff
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact change same
  · obtain ⟨q,hq⟩ := pin_index (raw v (by simp [hv]))
    have hqi : q ≠ i := by
      intro eq
      subst q
      exact absent ((hq.symm.trans hi) ▸ hv)
    have hs := stable q hqi
    rw [hq] at hs
    exact change hs

lemma slice_bin_available (i : Fin 10) {a b : Extended.Sig} {d : Nat}
    (ha : projectAt i a = zero) (hb : b ∈ Extended.pins) (hd : d < 4) :
    Available true (inputs.map observe)
      (restrictRows (sliceRow i) (Extended.observe (Extended.bin d a b))) := by
  rw [Extended.obs_bin,restrict_comb]
  have az : restrictRows (sliceRow i) (Extended.observe a) = (fun _ => false) := by
    rw [observe_projectAt,ha]
    funext r
    simp [observe,bit,zero]
  rw [az]
  have bb := slice_available i hb
  have zz : Available true (inputs.map observe) (fun _ : Row => false) :=
    Or.inr (Or.inl ⟨false,rfl⟩)
  interval_cases d
  all_goals first | simpa [comb,combine,inv] using zz | simpa [comb,combine,inv] using bb

lemma after_first_bound {k : Nat} {U : Finset Extended.Sig} {a b : Extended.Sig} {d : Nat}
    (hd : Extended.allowed true d) (hab : a ≠ b)
    (raw : ∀ v ∈ insert a (insert b U), v ∈ Extended.pins)
    (run : Extended.Live true Extended.target k (insert (Extended.bin d a b) U)) : 16 ≤ k := by
  classical
  have retained := first_retained hd hab raw run
  obtain ⟨i,hi⟩ := pin_index (raw a (by simp))
  let S := insert (Extended.bin d a b) U
  let front := a :: (S.erase a).toList
  have ain : a ∈ S := Finset.mem_insert_of_mem retained
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨by simp [front],Finset.nodup_toList _⟩
  have eqS : front.toFinset = S := by
    ext v
    by_cases va : v = a <;> simp [front,va,ain]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows (sliceRow i) (Extended.observe Extended.target) = observe graph := by
    rw [observe_projectAt,slice_target]
  have dd : d < 4 := by rcases hd with h | ⟨_,h⟩ <;> omega
  have supplyRoots : supply true (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows (sliceRow i))) := by
    intro v hv
    obtain ⟨_,hin,rfl⟩ := List.mem_map.mp hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hin
    have ws : w ∈ S := eqS ▸ List.mem_toFinset.mpr hw
    rcases Finset.mem_insert.mp ws with rfl | wu
    · exact slice_bin_available i (hi ▸ slice_self i) (raw b (by simp)) dd
    · exact slice_available i (raw w (by simp [wu]))
  have need := projected_bound (sliceRow i) hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L:=15) (same ▸ nineFloor)
  have constant : Constant (restrictRows (sliceRow i) (Extended.observe a)) := by
    refine ⟨false,?_⟩
    rw [observe_projectAt,←hi,slice_self]
    funext r
    simp [observe,bit,zero]
  have charge : 1 ≤ mass ((front.map Extended.observe).map (restrictRows (sliceRow i))) := by
    change 1 ≤ mass (restrictRows (sliceRow i) (Extended.observe a) :: _)
    rw [mass_cons]
    have one : cost (restrictRows (sliceRow i) (Extended.observe a)) = 1 := by
      simp [cost,constant]
    rw [one]
    omega
  omega

lemma atLeastSeventeen {k : Nat} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.pins) : 17 ≤ k := by
  cases k with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    have h := raw Extended.target (by simp)
    have hn : Extended.target ∉ Extended.pins := by decide +kernel
    exact False.elim (hn h)
  | succ k =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,_,tail⟩ := run
    have h := after_first_bound hd hab raw tail
    omega

lemma after_first_and_bound {k : Nat} {U : Finset Extended.Sig} {a b : Extended.Sig} {d : Nat}
    (hd : Extended.allowed true d) (hab : a ≠ b) (hop : d = 0 ∨ d = 2)
    (fresh : Extended.bin d a b ∉ insert a (insert b U))
    (raw : ∀ v ∈ insert a (insert b U), v ∈ Extended.pins)
    (run : Extended.Live true Extended.target k (insert (Extended.bin d a b) U)) : 17 ≤ k := by
  classical
  have retained := first_retained hd hab raw run
  obtain ⟨i,hi⟩ := pin_index (raw a (by simp))
  let g := Extended.bin d a b
  let S := insert g U
  let front := a :: g :: ((S.erase a).erase g).toList
  have ain : a ∈ S := Finset.mem_insert_of_mem retained
  have gin : g ∈ S := by simp [S]
  have ga : g ≠ a := by
    intro h
    exact fresh (by simp [g] at h; rw [h]; simp)
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · simp [front,ga,Ne.symm ga]
    · apply List.nodup_cons.mpr
      exact ⟨by simp,Finset.nodup_toList _⟩
  have eqS : front.toFinset = S := by
    ext v
    by_cases va : v = a <;> by_cases vg : v = g <;> simp [front,va,vg,ain,gin]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows (sliceRow i) (Extended.observe Extended.target) = observe graph := by
    rw [observe_projectAt,slice_target]
  have dd : d < 4 := by rcases hd with h | ⟨_,h⟩ <;> omega
  have supplyRoots : supply true (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows (sliceRow i))) := by
    intro v hv
    obtain ⟨_,hin,rfl⟩ := List.mem_map.mp hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hin
    have ws : w ∈ S := eqS ▸ List.mem_toFinset.mpr hw
    rcases Finset.mem_insert.mp ws with rfl | wu
    · exact slice_bin_available i (hi ▸ slice_self i) (raw b (by simp)) dd
    · exact slice_available i (raw w (by simp [wu]))
  have need := projected_bound (sliceRow i) hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L:=15) (same ▸ nineFloor)
  have az : restrictRows (sliceRow i) (Extended.observe a) = (fun _ => false) := by
    rw [observe_projectAt,←hi,slice_self]
    funext r
    simp [observe,bit,zero]
  have gz : restrictRows (sliceRow i) (Extended.observe g) = (fun _ => false) := by
    change restrictRows (sliceRow i) (Extended.observe (Extended.bin d a b)) = _
    rw [Extended.obs_bin,restrict_comb,az]
    rcases hop with rfl | rfl <;> simp [comb,combine,inv]
  have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows (sliceRow i))) := by
    change 2 ≤ mass (restrictRows (sliceRow i) (Extended.observe a) ::
      restrictRows (sliceRow i) (Extended.observe g) :: _)
    simp only [mass_cons]
    have ca : cost (restrictRows (sliceRow i) (Extended.observe a)) = 1 := by
      simp only [az,cost]
      split
      · rfl
      · rename_i h
        exact False.elim (h ⟨false,rfl⟩)
    have cg : cost (restrictRows (sliceRow i) (Extended.observe g)) = 1 := by
      rw [gz]
      change (if Constant (fun _ : Row => false) then 1 else 0) = 1
      exact if_pos ⟨false,rfl⟩
    rw [ca,cg]
    omega
  omega

lemma after_first_nonOr_bound
    {k : Nat} {U : Finset Extended.Sig} {a b : Extended.Sig} {d : Nat}
    (hd : Extended.allowed true d) (hab : a ≠ b) (hop : d ≠ 1)
    (fresh : Extended.bin d a b ∉ insert a (insert b U))
    (raw : ∀ v ∈ insert a (insert b U), v ∈ Extended.pins)
    (run : Extended.Live true Extended.target k (insert (Extended.bin d a b) U)) : 17 ≤ k := by
  rcases Extended.allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
  · exact after_first_and_bound hd hab (Or.inl rfl) fresh raw run
  · exact False.elim (hop rfl)
  · exact after_first_and_bound hd hab (Or.inr rfl) fresh raw run
  · have swap : Extended.bin 3 a b = Extended.bin 2 b a := by
      simp [Extended.bin,BitVec.and_comm]
    have raw' : ∀ v ∈ insert b (insert a U), v ∈ Extended.pins := by
      intro v hv
      exact raw v (by simpa only [Finset.insert_comm] using hv)
    have fresh' : Extended.bin 2 b a ∉ insert b (insert a U) := by
      rw [←swap]
      simpa only [Finset.insert_comm] using fresh
    rw [swap] at run
    exact after_first_and_bound (by simp [Extended.allowed]) hab.symm
      (Or.inr rfl) fresh' raw' run

end Seventeen
open PEqualNP.CircuitLowerBounds

lemma binaryFloorSeventeen (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  obtain ⟨k,S,hk,run,raw⟩ := Extended.realize C legal computes
  have floor := Seventeen.atLeastSeventeen run raw
  have sameNot :
      (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)) = Extended.isNot := by
    funext g
    obtain ⟨op, operands⟩ := g
    cases op <;> rfl
  rw [PEqualNP.NotBracket.notCount, sameNot, ← List.countP_eq_length_filter]
  have negSame : (fun g : Gate => decide (¬ Extended.isNot g = true)) = (fun g => !Extended.isNot g) := by
    funext g
    cases Extended.isNot g <;> rfl
  have count := List.length_eq_countP_add_countP Extended.isNot (l := C.gates)
  rw [negSame] at count
  change 17 + _ ≤ C.gates.length
  omega

lemma partial_only_three (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (small : C.size ≤ 19) (many : 3 ≤ PEqualNP.NotBracket.notCount C) :
    ¬ ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) =
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
       (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
       (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
       (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) := by
  intro correct
  have bound := binaryFloorSeventeen C fan correct
  omega

end PEqualNP.Outside.L_meta_2592_aux
