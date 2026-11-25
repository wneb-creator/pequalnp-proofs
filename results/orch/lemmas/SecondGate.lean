import PEqualNP.Outside.L_meta_2592

namespace PEqualNP.Outside.L_meta_2592
namespace SecondGate

open Floor17

def orPin (a b : Fin 10) : Extended.Sig := Extended.bin 1 (pin a) (pin b)

def gate (negative : Bool) (c : Fin 10) (v : Extended.Sig) : Extended.Sig :=
  Extended.bin (if negative then 2 else 0) (pin c) v

def rawData : List Nat := [0,0,64,128,128,96,128,384,128,192,128,144,128,68,128,129,128,136,128,130,32,512,0,0,512,544,512,768,512,96,512,48,512,516,512,513,512,520,512,514,128,768,256,128,0,0,128,384,128,192,128,144,128,260,128,129,128,136,128,130,32,544,32,192,64,32,0,0,32,96,32,48,32,36,32,65,32,40,32,34,256,512,512,384,512,544,512,768,0,0,512,272,512,516,512,513,512,520,512,514,1,512,512,129,512,544,512,768,512,65,0,0,512,516,512,513,512,520,512,514,128,520,8,128,128,40,128,384,128,192,128,144,0,0,128,129,128,136,128,130,32,544,32,144,16,32,32,272,32,96,32,48,32,36,0,0,32,40,32,34,256,768,256,384,256,48,16,256,256,80,256,272,256,260,256,257,0,0,256,258,64,516,64,192,64,96,64,260,4,64,64,80,64,68,64,65,64,72,0,0]

def orData : List Nat := [0,32,128,32,256,1,128,32,256,64,0,0,256,32,256,1,8,32,256,64,0,4,0,64,256,1,128,16,256,64,0,32,128,0,2,1,128,32,16,64,0,32,128,32,0,1,128,32,256,4,0,32,128,32,256,0,128,32,256,64,0,32,128,32,256,1,0,32,256,64,0,32,128,32,256,8,128,0,256,64,0,32,128,32,256,1,128,32,0,64,0,32,128,32,256,1,128,32,256,0,0,0,256,32,256,1,8,32,256,64,64,0,256,32,512,512,8,32,256,64,64,0,0,64,512,512,8,16,256,64,64,0,1,0,512,512,8,32,16,64,16,0,256,32,0,512,8,32,256,4,64,0,256,32,512,0,8,32,256,64,64,0,256,32,512,512,0,32,256,64,64,0,256,32,512,512,8,0,256,64,64,0,256,32,512,512,2,32,0,64,64,0,256,32,512,512,8,32,256,0,0,4,0,64,256,1,128,16,256,64,64,0,0,64,512,512,8,16,256,64,128,512,0,64,512,512,128,16,256,64,128,512,0,0,512,512,128,16,16,64,128,512,0,8,0,512,128,16,256,4,128,512,0,64,512,0,128,2,256,64,128,512,0,64,512,512,0,16,256,64,128,512,0,64,512,512,128,0,256,64,128,512,0,64,512,512,128,16,0,64,128,512,0,64,512,512,128,16,256,0,0,32,128,0,2,1,128,32,16,64,64,0,1,0,512,512,8,32,16,64,128,512,0,0,512,512,128,16,16,64,128,512,128,0,512,512,128,32,16,64,128,512,128,0,0,512,128,32,16,4,128,512,128,0,512,0,128,32,4,64,128,512,128,0,512,512,0,32,16,64,128,512,128,0,512,512,128,0,16,64,128,512,128,0,512,512,128,32,0,64,128,512,128,0,512,512,128,32,16,0,0,32,128,32,0,1,128,32,256,4,16,0,256,32,0,512,8,32,256,4,128,512,0,8,0,512,128,16,256,4,128,512,128,0,0,512,128,32,16,4,128,512,128,32,0,512,128,32,256,4,128,512,128,32,0,0,128,32,256,4,128,512,128,32,0,512,0,32,256,1,128,512,128,32,0,512,128,0,256,4,128,512,128,32,0,512,128,32,0,4,128,512,128,32,0,512,128,32,256,0,0,32,128,32,256,0,128,32,256,64,64,0,256,32,512,0,8,32,256,64,128,512,0,64,512,0,128,2,256,64,128,512,128,0,512,0,128,32,4,64,128,512,128,32,0,0,128,32,256,4,128,512,128,32,512,0,128,32,256,64,128,512,128,32,512,0,0,32,256,64,128,512,128,32,512,0,128,0,256,64,128,512,128,32,512,0,128,32,0,64,128,512,128,32,512,0,128,32,256,0,0,32,128,32,256,1,0,32,256,64,64,0,256,32,512,512,0,32,256,64,128,512,0,64,512,512,0,16,256,64,128,512,128,0,512,512,0,32,16,64,128,512,128,32,0,512,0,32,256,1,128,512,128,32,512,0,0,32,256,64,128,512,128,32,512,512,0,32,256,64,128,512,128,32,512,512,0,0,256,64,128,512,128,32,512,512,0,32,0,64,128,512,128,32,512,512,0,32,256,0,0,32,128,32,256,8,128,0,256,64,64,0,256,32,512,512,8,0,256,64,128,512,0,64,512,512,128,0,256,64,128,512,128,0,512,512,128,0,16,64,128,512,128,32,0,512,128,0,256,4,128,512,128,32,512,0,128,0,256,64,128,512,128,32,512,512,0,0,256,64,128,512,128,32,512,512,128,0,256,64,128,512,128,32,512,512,128,0,0,64,128,512,128,32,512,512,128,0,256,0,0,32,128,32,256,1,128,32,0,64,64,0,256,32,512,512,2,32,0,64,128,512,0,64,512,512,128,16,0,64,128,512,128,0,512,512,128,32,0,64,128,512,128,32,0,512,128,32,0,4,128,512,128,32,512,0,128,32,0,64,128,512,128,32,512,512,0,32,0,64,128,512,128,32,512,512,128,0,0,64,128,512,128,32,512,512,128,32,0,64,128,512,128,32,512,512,128,32,0,0,0,32,128,32,256,1,128,32,256,0,64,0,256,32,512,512,8,32,256,0,128,512,0,64,512,512,128,16,256,0,128,512,128,0,512,512,128,32,16,0,128,512,128,32,0,512,128,32,256,0,128,512,128,32,512,0,128,32,256,0,128,512,128,32,512,512,0,32,256,0,128,512,128,32,512,512,128,0,256,0,128,512,128,32,512,512,128,32,0,0,128,512,128,32,512,512,128,32,256,0]

def rows (c : Fin 10) (r : Nat) : Extended.Row × Extended.Row :=
  (Fin.ofNat 1024 r, Fin.ofNat 1024 (r + 2 ^ bitPositions.getD c.val 0))

def rawRows (c j : Fin 10) (negative : Bool) : Extended.Row × Extended.Row :=
  rows c (rawData.getD ((c.val * 10 + j.val) * 2 + if negative then 1 else 0) 0)

def orRows (a b c : Fin 10) (negative : Bool) : Extended.Row × Extended.Row :=
  if negative then rawRows c a true
  else rows c (orData.getD ((a.val * 10 + b.val) * 10 + c.val) 0)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rawWitness : ∀ (c j : Fin 10) (negative : Bool), c ≠ j →
    let r := (rawRows c j negative).1
    let s := (rawRows c j negative).2
    Extended.bit r Extended.target ≠ Extended.bit s Extended.target ∧
    Extended.bit r (gate negative c (pin j)) = Extended.bit s (gate negative c (pin j)) ∧
    ∀ i : Fin 10, i ≠ c → Extended.bit r (pin i) = Extended.bit s (pin i) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma orWitness : ∀ (a b c : Fin 10) (negative : Bool), c ≠ a → c ≠ b →
    let r := (orRows a b c negative).1
    let s := (orRows a b c negative).2
    Extended.bit r Extended.target ≠ Extended.bit s Extended.target ∧
    Extended.bit r (gate negative c (orPin a b)) =
      Extended.bit s (gate negative c (orPin a b)) ∧
    ∀ i : Fin 10, i ≠ c → Extended.bit r (pin i) = Extended.bit s (pin i) := by
  decide +kernel

lemma or_same {a b c : Fin 10} {r s : Extended.Row}
    (ha : c ≠ a) (hb : c ≠ b)
    (same : ∀ i : Fin 10, i ≠ c → Extended.bit r (pin i) = Extended.bit s (pin i)) :
    Extended.bit r (orPin a b) = Extended.bit s (orPin a b) := by
  have h := congrArg₂ Bool.or (same a (Ne.symm ha)) (same b (Ne.symm hb))
  simpa [orPin, Extended.bin, Extended.bit] using h

lemma retain {a b c : Fin 10} {v : Extended.Sig} {negative : Bool}
    {k : Nat} {U : Finset Extended.Sig}
    (ha : c ≠ a) (hb : c ≠ b) (different : pin c ≠ v)
    (source : v ∈ Extended.pins ∨ v = orPin a b)
    (raw : ∀ w ∈ U, w ∈ Extended.pins ∨ w = orPin a b)
    (run : Extended.Live true Extended.target k (insert (gate negative c v) U)) :
    pin c ∈ U := by
  classical
  by_contra missing
  have witness : ∃ r s : Extended.Row,
      Extended.bit r Extended.target ≠ Extended.bit s Extended.target ∧
      Extended.bit r (gate negative c v) = Extended.bit s (gate negative c v) ∧
      ∀ i : Fin 10, i ≠ c → Extended.bit r (pin i) = Extended.bit s (pin i) := by
    rcases source with source | rfl
    · obtain ⟨j, rfl⟩ := pinComplete v source
      have hcj : c ≠ j := by intro h; subst j; exact different rfl
      exact ⟨_, _, rawWitness c j negative hcj⟩
    · exact ⟨_, _, orWitness a b c negative ha hb⟩
  obtain ⟨r, s, targetDifferent, gateSame, pinSame⟩ := witness
  obtain ⟨w, hw, wDifferent⟩ := Extended.live_row_difference run targetDifferent
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact wDifferent gateSame
  · rcases raw w hw with hpin | rfl
    · obtain ⟨i, rfl⟩ := pinComplete w hpin
      have hic : i ≠ c := by intro h; subst i; exact missing hw
      exact wDifferent (pinSame i hic)
    · exact wDifferent (or_same ha hb pinSame)

lemma pin_mem (i : Fin 10) : pin i ∈ Extended.pins := by
  rw [pinList]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

lemma gate_zero (negative : Bool) (c : Fin 10) (v : Extended.Sig) :
    restrictRows (projection c) (Extended.observe (gate negative c v)) = fun _ => false := by
  rw [gate, Extended.obs_bin, restrict_comb, pin_zero_wire]
  cases negative <;> rfl

lemma or_project (a b c : Fin 10) :
    restrictRows (projection c) (Extended.observe (orPin a b)) =
      combine true (restrictRows (projection c) (Extended.observe (pin a)))
        (restrictRows (projection c) (Extended.observe (pin b))) := by
  rw [orPin, Extended.obs_bin, restrict_comb]
  rfl

lemma available_cons {R : Type} {u : Bool} {roots : List (Wire R)}
    {v : Wire R} (h : Available u roots v) (w : Wire R) : Available u (w :: roots) v := by
  rcases h with h | h | ⟨hu, h⟩
  · exact Or.inl (List.mem_cons_of_mem w h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hu, List.mem_cons_of_mem w h⟩)

lemma or_free {a b c : Fin 10} (h : c = a ∨ c = b) :
    Available true (inputs.map observe)
      (restrictRows (projection c) (Extended.observe (orPin a b))) := by
  rcases h with ha | hb
  · subst c
    exact projected_bin_available a (pin b) (pin_mem b) 1
  · subst c
    have comm : orPin a b = orPin b a := by
      simp [orPin, Extended.bin, BitVec.or_comm]
    rw [comm]
    exact projected_bin_available b (pin a) (pin_mem a) 1

lemma tail_bound {a b c : Fin 10} {v : Extended.Sig} {negative : Bool}
    {k : Nat} {U : Finset Extended.Sig}
    (different : pin c ≠ v)
    (source : v ∈ Extended.pins ∨ v = orPin a b)
    (raw : ∀ w ∈ U, w ∈ Extended.pins ∨ w = orPin a b)
    (fresh : gate negative c v ∉ U)
    (run : Extended.Live true Extended.target k (insert (gate negative c v) U)) :
    16 ≤ k := by
  classical
  let g := gate negative c v
  let ws := g :: U.toList
  have nd : ws.Nodup := by
    exact List.nodup_cons.mpr ⟨by simpa [g] using fresh, Finset.nodup_toList U⟩
  have eqS : ws.toFinset = insert g U := by simp [ws]
  have hrun := Extended.list_run run ws nd eqS
  have same : restrictRows (projection c) (Extended.observe Extended.target) = observe graph := by
    rw [Floor17.observe_projected, projectionGoal]
  have constG : Constant (restrictRows (projection c) (Extended.observe g)) :=
    ⟨false, gate_zero negative c v⟩
  have massG : mass ((ws.map Extended.observe).map (restrictRows (projection c))) =
      1 + mass ((U.toList.map Extended.observe).map (restrictRows (projection c))) := by
    simp [ws, mass_cons, cost, constG]
  by_cases special : c = a ∨ c = b
  · have supplyRoots : supply true (inputs.map observe)
        ((ws.map Extended.observe).map (restrictRows (projection c))) := by
      intro w hw
      obtain ⟨_, hmem, rfl⟩ := List.mem_map.mp hw
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hmem
      change z ∈ g :: U.toList at hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inr (Or.inl constG)
      · rcases raw z (by simpa using hz) with hpin | rfl
        · exact projected_available c z hpin
        · exact or_free special
    have lower := projected_bound (projection c) hrun (same ▸ observe_proper graph_proper)
      Reach.start supplyRoots (L := 15) (same ▸ nineFloor)
    rw [massG] at lower
    omega
  · have ha : c ≠ a := fun h => special (Or.inl h)
    have hb : c ≠ b := fun h => special (Or.inr h)
    have kept := retain ha hb different source raw run
    let q := restrictRows (projection c) (Extended.observe (orPin a b))
    let roots := inputs.map observe
    have reachQ : Reach true roots 1 (q :: roots) := by
      have h := Reach.two true (u := true) (Reach.start (roots := roots))
        (projected_available c (pin a) (pin_mem a))
        (projected_available c (pin b) (pin_mem b))
      simpa [q, or_project] using h
    have supplyQ : supply true (q :: roots)
        ((ws.map Extended.observe).map (restrictRows (projection c))) := by
      intro w hw
      obtain ⟨_, hmem, rfl⟩ := List.mem_map.mp hw
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hmem
      change z ∈ g :: U.toList at hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inr (Or.inl constG)
      · rcases raw z (by simpa using hz) with hpin | rfl
        · exact available_cons (projected_available c z hpin) q
        · exact Or.inl (by simp [q])
    have lower := projected_bound (projection c) hrun (same ▸ observe_proper graph_proper)
      reachQ supplyQ (L := 15) (same ▸ nineFloor)
    have pinMem : restrictRows (projection c) (Extended.observe (pin c)) ∈
        ((U.toList.map Extended.observe).map (restrictRows (projection c))) :=
      List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨_, by simpa using kept, rfl⟩, rfl⟩
    have charge := mass_one pinMem (show Constant
        (restrictRows (projection c) (Extended.observe (pin c))) from ⟨false, pin_zero_wire c⟩)
    rw [massG] at lower
    omega

end SecondGate
end PEqualNP.Outside.L_meta_2592
