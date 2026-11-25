import PEqualNP.Outside.L_meta_2592

namespace PEqualNP.Outside.L_meta_2592
namespace Floor17

open PEqualNP.CircuitLowerBounds

def pin (i : Fin 10) : Extended.Sig := Extended.pins.getD i.val Extended.zero

def bitPositions : List ℕ := [9, 7, 5, 8, 6, 4, 2, 0, 3, 1]
def automorphisms : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [1, 0, 4, 3, 2, 6, 5, 9, 8, 7], [2, 1, 0, 4, 3, 7, 6, 5, 9, 8], [2, 3, 4, 0, 1, 7, 8, 9, 5, 6], [1, 2, 3, 4, 0, 6, 7, 8, 9, 5], [1, 2, 3, 8, 6, 0, 7, 4, 5, 9], [2, 1, 6, 8, 3, 7, 0, 9, 5, 4], [2, 3, 4, 9, 7, 1, 8, 0, 6, 5], [2, 3, 8, 5, 7, 1, 4, 6, 0, 9], [2, 3, 8, 6, 1, 7, 4, 5, 9, 0]]
def pairRows : List (ℕ × ℕ) := [(0,0),(0,0),(0,0),(0,0),(32,160),(128,640),(0,640),(0,640),(128,160),(288,768),(128,160),(128,640),(128,640),(384,640),(128,896),(128,640),(128,640),(64,576),(0,576),(0,576),(128,640),(16,528),(0,528),(0,528),(128,132),(68,576),(128,132),(128,640),(128,640),(129,640),(128,641),(128,640),(128,640),(136,640),(128,648),(128,640),(128,640),(130,640),(128,642),(128,640),(32,160),(512,640),(0,640),(0,640),(0,0),(0,0),(0,0),(0,0),(512,640),(32,160),(0,160),(0,160),(512,640),(768,640),(512,896),(512,640),(512,576),(96,160),(512,576),(512,640),(512,528),(48,160),(512,528),(512,640),(512,640),(4,132),(0,132),(0,132),(512,640),(513,640),(512,641),(512,640),(512,640),(520,640),(512,648),(512,640),(512,640),(514,640),(512,642),(512,640),(128,640),(768,288),(128,640),(128,160),(512,640),(128,160),(0,160),(0,160),(0,0),(0,0),(0,0),(0,0),(128,160),(256,288),(0,288),(0,288),(512,576),(576,544),(512,576),(512,608),(512,528),(528,544),(512,528),(512,560),(128,132),(260,288),(128,132),(128,160),(128,160),(1,33),(0,33),(0,33),(128,160),(136,160),(128,168),(128,160),(128,160),(130,160),(128,162),(128,160),(128,640),(640,384),(128,640),(128,896),(512,640),(640,768),(512,640),(512,896),(128,160),(32,288),(0,288),(0,288),(0,0),(0,0),(0,0),(0,0),(512,576),(64,320),(0,320),(0,320),(512,528),(528,768),(512,528),(512,784),(128,132),(132,384),(128,132),(128,388),(32,33),(65,320),(32,33),(32,288),(32,288),(8,264),(0,264),(0,264),(32,288),(34,288),(32,290),(32,288),(128,640),(512,576),(0,576),(0,576),(512,640),(160,96),(512,640),(512,576),(512,576),(544,576),(512,608),(512,576),(512,576),(256,320),(0,320),(0,320),(0,0),(0,0),(0,0),(0,0),(512,528),(272,320),(512,528),(512,576),(512,576),(516,576),(512,580),(512,576),(512,576),(513,576),(512,577),(512,576),(512,576),(520,576),(512,584),(512,576),(512,576),(2,66),(0,66),(0,66),(128,640),(512,528),(0,528),(0,528),(512,640),(160,48),(512,640),(512,528),(512,528),(544,528),(512,560),(512,528),(512,528),(768,528),(512,784),(512,528),(512,576),(320,272),(512,576),(512,528),(0,0),(0,0),(0,0),(0,0),(512,528),(516,528),(512,532),(512,528),(512,528),(1,17),(0,17),(0,17),(512,528),(8,24),(0,24),(0,24),(512,528),(514,528),(512,530),(512,528),(128,640),(576,68),(128,640),(128,132),(512,640),(128,132),(0,132),(0,132),(128,160),(288,260),(128,160),(128,132),(128,132),(384,132),(128,388),(128,132),(512,576),(576,516),(512,576),(512,580),(512,528),(528,516),(512,528),(512,532),(0,0),(0,0),(0,0),(0,0),(128,132),(129,132),(128,133),(128,132),(128,132),(8,12),(0,12),(0,12),(128,132),(2,6),(0,6),(0,6),(128,640),(640,129),(128,640),(128,641),(512,640),(640,513),(512,640),(512,641),(128,160),(32,33),(0,33),(0,33),(32,288),(320,65),(32,288),(32,33),(512,576),(576,513),(512,576),(512,577),(512,528),(16,17),(0,17),(0,17),(128,132),(132,129),(128,132),(128,133),(0,0),(0,0),(0,0),(0,0),(32,33),(40,33),(32,41),(32,33),(32,33),(2,3),(0,3),(0,3),(128,640),(640,136),(128,640),(128,648),(512,640),(640,520),(512,640),(512,648),(128,160),(160,136),(128,160),(128,168),(32,288),(256,264),(0,264),(0,264),(512,576),(576,520),(512,576),(512,584),(512,528),(16,24),(0,24),(0,24),(128,132),(4,12),(0,12),(0,12),(32,33),(33,40),(32,33),(32,41),(0,0),(0,0),(0,0),(0,0),(256,264),(258,264),(256,266),(256,264),(128,640),(640,130),(128,640),(128,642),(512,640),(640,514),(512,640),(512,642),(128,160),(160,130),(128,160),(128,162),(32,288),(288,34),(32,288),(32,290),(512,576),(64,66),(0,66),(0,66),(512,528),(528,514),(512,528),(512,530),(128,132),(4,6),(0,6),(0,6),(32,33),(1,3),(0,3),(0,3),(256,264),(264,258),(256,264),(256,266),(0,0),(0,0),(0,0),(0,0)]

def pairWitnessRows (i j : Fin 10) (d : Fin 4) : Extended.Row × Extended.Row :=
  let w := pairRows.getD ((i.val * 10 + j.val) * 4 + d.val) (0,0)
  (Fin.ofNat 1024 w.1, Fin.ofNat 1024 w.2)

def projection (i : Fin 10) (r : Row) : Extended.Row :=
  Fin.ofNat 1024 ((List.range 10).foldl (fun v j => v +
    if r.val.testBit (bitPositions.getD ((automorphisms.getD i.val []).getD j 0) 0)
    then 2 ^ bitPositions.getD j 0 else 0) 0)

def projected (i : Fin 10) (a : Extended.Sig) : Sig :=
  table (fun r => Extended.bit (projection i r) a)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinList : Extended.pins = List.ofFn pin := by decide +kernel

lemma pinComplete (a : Extended.Sig) (ha : a ∈ Extended.pins) :
    ∃ i : Fin 10, a = pin i := by
  rw [pinList] at ha
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp ha
  exact ⟨i,hi.symm⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pairWitness : ∀ (i j : Fin 10) (d : Fin 4), i ≠ j →
    let r := (pairWitnessRows i j d).1
    let s := (pairWitnessRows i j d).2
    Extended.bit r Extended.target ≠ Extended.bit s Extended.target ∧
    Extended.bit r (Extended.bin d.val (pin i) (pin j)) =
      Extended.bit s (Extended.bin d.val (pin i) (pin j)) ∧
    ∀ q : Fin 10, q ≠ i → q ≠ j → Extended.bit r (pin q) = Extended.bit s (pin q) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma projectionGoal : ∀ i : Fin 10, projected i Extended.target = graph := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma projectionPin : ∀ i : Fin 10, projected i (pin i) = zero := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma projectionSources : ∀ i : Fin 10, Extended.pins.all
    (fun a => (projected i a == zero) || inputs.contains (projected i a)) = true := by
  decide +kernel

lemma observe_projected (i : Fin 10) (a : Extended.Sig) :
    restrictRows (projection i) (Extended.observe a) = observe (projected i a) := by
  funext r
  exact (bit_table _ r).symm

lemma zero_wire : observe zero = fun _ => false := by
  funext r
  simp [observe,bit,zero]

lemma pin_zero_wire (i : Fin 10) :
    restrictRows (projection i) (Extended.observe (pin i)) = fun _ => false := by
  rw [observe_projected,projectionPin,zero_wire]

lemma projected_available (i : Fin 10) (a : Extended.Sig) (ha : a ∈ Extended.pins) :
    Available true (inputs.map observe) (restrictRows (projection i) (Extended.observe a)) := by
  rw [observe_projected]
  have permitted := List.all_eq_true.mp (projectionSources i) a ha
  simp only [Bool.or_eq_true,beq_iff_eq] at permitted
  rcases permitted with hz|hm
  · exact Or.inr (Or.inl ⟨false,hz ▸ zero_wire⟩)
  · exact Or.inl (List.mem_map.mpr ⟨_,by simpa using hm,rfl⟩)

lemma projected_bin_available (i : Fin 10) (b : Extended.Sig) (hb : b ∈ Extended.pins) (d : ℕ) :
    Available true (inputs.map observe)
      (restrictRows (projection i) (Extended.observe (Extended.bin d (pin i) b))) := by
  have simple : restrictRows (projection i) (Extended.observe (Extended.bin d (pin i) b)) =
      if d = 0 ∨ d = 2 then (fun _ => false)
      else restrictRows (projection i) (Extended.observe b) := by
    rw [Extended.obs_bin]
    funext r
    have hz := congrFun (pin_zero_wire i) r
    change Extended.observe (pin i) (projection i r) = false at hz
    by_cases h0 : d = 0
    · subst d
      simp [restrictRows,comb,combine,hz]
    · by_cases h1 : d = 1
      · subst d
        simp [restrictRows,comb,combine,hz]
      · by_cases h2 : d = 2
        · subst d
          simp [restrictRows,comb,combine,hz]
        · simp [restrictRows,comb,combine,inv,h0,h1,h2,hz]
  rw [simple]
  split_ifs
  · exact Or.inr (Or.inl ⟨false,rfl⟩)
  · exact projected_available i b hb

lemma mass_one {R : Type} {ws : List (Wire R)} {a : Wire R}
    (ha : a ∈ ws) (hc : Constant a) : 1 ≤ mass ws := by
  classical
  induction ws with
  | nil => simp at ha
  | cons b bs ih =>
    rcases List.mem_cons.mp ha with rfl|ha
    · simp [mass_cons,cost,hc]
    · have h := ih ha
      rw [mass_cons]
      omega

lemma keep_left {k : ℕ} {U : Finset Extended.Sig} {d : ℕ} {b : Extended.Sig}
    (i : Fin 10) (hb : b ∈ Extended.pins) (hu : ∀ a ∈ U, a ∈ Extended.pins)
    (keep : pin i ∈ U) (fresh : Extended.bin d (pin i) b ∉ U)
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d (pin i) b) U)) :
    16 ≤ k := by
  classical
  let ws := Extended.bin d (pin i) b :: U.toList
  have nd : ws.Nodup := by
    exact List.nodup_cons.mpr ⟨by simpa using fresh,Finset.nodup_toList U⟩
  have eqS : ws.toFinset = insert (Extended.bin d (pin i) b) U := by simp [ws]
  have hrun := Extended.list_run tail ws nd eqS
  have same : restrictRows (projection i) (Extended.observe Extended.target) = observe graph := by
    rw [observe_projected,projectionGoal]
  have supplyRoots : supply true (inputs.map observe)
      ((ws.map Extended.observe).map (restrictRows (projection i))) := by
    intro v hv
    obtain ⟨_,hmem,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hmem
    change a ∈ Extended.bin d (pin i) b :: U.toList at ha
    rcases List.mem_cons.mp ha with rfl|ha
    · exact projected_bin_available i b hb d
    · exact projected_available i a (hu a (by simpa using ha))
  have need := projected_bound (projection i) hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L:=15) (same ▸ nineFloor)
  have pinMem : pin i ∈ ws := by simp [ws,keep]
  have pinProjectedMem : restrictRows (projection i) (Extended.observe (pin i)) ∈
      ((ws.map Extended.observe).map (restrictRows (projection i))) :=
    List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨_,pinMem,rfl⟩,rfl⟩
  have charge := mass_one pinProjectedMem (show Constant
      (restrictRows (projection i) (Extended.observe (pin i))) from ⟨false,pin_zero_wire i⟩)
  omega

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma target_not_pin : Extended.target ∉ Extended.pins := by decide +kernel

lemma atLeastSeventeen {k : ℕ} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.pins) : 17 ≤ k := by
  classical
  cases k with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact False.elim (target_not_pin (raw _ (by simp)))
  | succ k =>
    obtain ⟨U,a,b,d,hd,rfl,pa,pb,hab,fresh,tail⟩ := run
    have ha : a ∈ Extended.pins := raw _ (by simp)
    have hb : b ∈ Extended.pins := raw _ (by simp)
    have hu : ∀ c ∈ U, c ∈ Extended.pins := fun c hc =>
      raw c (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc))
    have kept : a ∈ U ∨ b ∈ U := by
      by_contra no
      have na : a ∉ U := fun h => no (Or.inl h)
      have nb : b ∉ U := fun h => no (Or.inr h)
      obtain ⟨i,rfl⟩ := pinComplete a ha
      obtain ⟨j,rfl⟩ := pinComplete b hb
      have hij : i ≠ j := by intro h; subst j; exact hab rfl
      have hd4 : d < 4 := by rcases hd with h|⟨_,h⟩ <;> omega
      have witness := pairWitness i j ⟨d,hd4⟩ hij
      obtain ⟨c,hc,different⟩ := Extended.live_row_difference tail witness.1
      rcases Finset.mem_insert.mp hc with rfl|hc
      · exact different witness.2.1
      · obtain ⟨q,rfl⟩ := pinComplete c (hu c hc)
        have hqi : q ≠ i := by intro h; subst q; exact na hc
        have hqj : q ≠ j := by intro h; subst q; exact nb hc
        exact different (witness.2.2 q hqi hqj)
    rcases kept with kept|kept
    · obtain ⟨i,rfl⟩ := pinComplete a ha
      have bound := keep_left i hb hu kept
        (fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))) tail
      omega
    · obtain ⟨i,rfl⟩ := pinComplete b hb
      have flipped := Extended.bin_flip hd a (pin i)
      rw [flipped] at tail fresh
      have bound := keep_left i ha hu kept
        (fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))) tail
      omega

end Floor17
end PEqualNP.Outside.L_meta_2592
