namespace PEqualNP.Outside.L_meta_2592_aux.Binary16

open PEqualNP.CircuitLowerBounds

def pairMask (j : Fin 2) : ℕ := if j.val = 0 then 383 else 479

def pairRows (j : Fin 2) (r : Row) : Extended.Row :=
  Fin.ofNat 1024 (r.val &&& pairMask j)

def pairProject (j : Fin 2) (a : Extended.Sig) : Sig :=
  table (fun r => Extended.bit (pairRows j r) a)

lemma bit_pairProject (j : Fin 2) (a : Extended.Sig) (r : Row) :
    bit r (pairProject j a) = Extended.bit (pairRows j r) a := bit_table _ _

lemma observe_pairProject (j : Fin 2) (a : Extended.Sig) :
    restrictRows (pairRows j) (Extended.observe a) = observe (pairProject j a) := by
  funext r
  exact (bit_pairProject j a r).symm

lemma pairProject_bin (j : Fin 2) (d : ℕ) (a b : Extended.Sig) :
    pairProject j (Extended.bin d a b) = bin d (pairProject j a) (pairProject j b) := by
  apply bit_ext
  intro r
  simp only [bit_pairProject,Extended.bit_bin,bit_bin]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma pairTarget : ∀ j : Fin 2,
    pairProject j Extended.target = graphGoal (pairMask j) := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma pairTargetProper : ∀ j : Fin 2, proper (graphGoal (pairMask j)) := by
  unfold proper
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma pairPinsSupply : ∀ j : Fin 2,
    Extended.pins.all (fun a => (pairProject j a == zero) ||
      (vars (pairMask j)).contains (pairProject j a)) = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma pairPinsZero : ∀ j : Fin 2,
    pairProject j (inputPin 0) = zero ∧
      pairProject j (inputPin ⟨j.val + 1,by have := j.isLt; omega⟩) = zero := by decide +kernel

def pairSeed (j : Fin 2) : Extended.Sig :=
  Extended.bin 1 (inputPin 0) (inputPin ⟨j.val + 1,by have := j.isLt; omega⟩)

def pairSubtract (j : Fin 2) (c : Fin 10) : Extended.Sig :=
  Extended.bin 2 (pairSeed j) (inputPin c)

lemma pairSeedZero (j : Fin 2) : pairProject j (pairSeed j) = zero := by
  rw [pairSeed,pairProject_bin,(pairPinsZero j).1,(pairPinsZero j).2]
  simp [bin,zero]

lemma pairSubtractZero (j : Fin 2) (c : Fin 10) :
    pairProject j (pairSubtract j c) = zero := by
  rw [pairSubtract,pairProject_bin,pairSeedZero]
  simp [bin,zero]

def pairFloor (j : Fin 2) : ℕ := if j.val = 0 then 13 else 12

lemma pairLower (j : Fin 2) :
    Lower true (vars (pairMask j)) (graphGoal (pairMask j)) (pairFloor j) := by
  fin_cases j
  · exact low383
  · have h := before_sound known383 valid383 479
    have hb : boundsBefore known383 479 = 12 := by decide +kernel
    rw [hb] at h
    simpa only [varsX,show (479 : ℕ) < 512 from by decide,ite_true] using h

end PEqualNP.Outside.L_meta_2592_aux.Binary16
