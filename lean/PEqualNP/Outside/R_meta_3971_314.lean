import Mathlib.Tactic
import PEqualNP.Defs

-- Formulas with at most one inverter require fifteen gates.
-- The second child retains circuits whose output unfolds beyond that range.
theorem PEqualNP.Outside.R_meta_3971_314
  (trees : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → let init : List (Nat × Nat) := List.replicate 10 (1,0)
    let ws := C.gates.foldl (fun (s : List (Nat × Nat)) g =>
      let col := fun j => (g.inputs[j]?.bind fun i => s[i]?).getD (1,0)
      let a := col 0
      let b := col 1
      s ++ [ite (g.op.eval [false]=true) (a.1,a.2+1) (a.1+b.1,a.2+b.2)]) init
    let z := ws.getD C.output (1,0)
    z.2≤1 → z.1+z.2≤15 → ∃ r : Nat, r<512 ∧ C.eval ((([1,0,4,7,5,2,8,6,3] : List Nat).map (fun i => r.testBit i)) ++ [r.testBit 1 || r.testBit 8]) ≠ (List.foldl (fun (a b : Nat) => a*1000000000000000000+b) 0 [13407807929,942597095939831376,727811673905304651,18912648022854022,873869787405066962,725179222507908767,667956533170508564,710083788841651696,458571261487544520] : Nat).testBit r)
  (sharing : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size=14 → C.gates.countP (fun g => g.op.eval [false])=1 →
    C.gates.countP (fun g => (ite (g.op.eval [false,false]=true) (g.inputs.take 1) g.inputs).any (fun i => decide (i=6))) ≤1 →
    (∃ g∈C.gates, g.op=.or ∧ 6∈g.inputs) → let init : List (Nat × Nat) := List.replicate 10 (1,0)
    let ws := C.gates.foldl (fun (s : List (Nat × Nat)) g =>
      let col := fun j => (g.inputs[j]?.bind fun i => s[i]?).getD (1,0)
      let a := col 0
      let b := col 1
      s ++ [ite (g.op.eval [false]=true) (a.1,a.2+1) (a.1+b.1,a.2+b.2)]) init
    let z := ws.getD C.output (1,0)
    (1<z.2 ∨ 15<z.1+z.2) → ∃ r : Nat, r<512 ∧ C.eval ((([1,0,4,7,5,2,8,6,3] : List Nat).map (fun i => r.testBit i)) ++ [r.testBit 1 || r.testBit 8]) ≠ (List.foldl (fun (a b : Nat) => a*1000000000000000000+b) 0 [13407807929,942597095939831376,727811673905304651,18912648022854022,873869787405066962,725179222507908767,667956533170508564,710083788841651696,458571261487544520] : Nat).testBit r) :
  have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (14 : ℕ) → List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false]) x4.gates = (1 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∃ x9 ∈ x4.gates, x9.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (6 : ℕ) ∈ x9.inputs) → (∀ (x10 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x10) = x3 x10) → ∃ (x11 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x11) ≠ (x3 x11 || x11 (0 : Fin (8 : ℕ)) || x11 (3 : Fin (8 : ℕ))) := by
  dsimp only
  intro C fit sz one rd reader lo
  by_contra! hi
  let inp (t : Bool) (x : Fin 8 → Bool) := [x 1,x 0,x 4,x 7,x 5,x 2,t,x 6,x 3,x 1 || t]
  let G (x : Fin 8 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 ||
    x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
  let mask (r : Fin 512) := (([1,0,4,7,5,2,8,6,3] : List Nat).map (fun i => r.val.testBit i)) ++ [r.val.testBit 1 || r.val.testBit 8]
  let sample (r : Fin 512) (j : Fin 8) := r.val.testBit j.val
  have inputsAgree : ∀ r : Fin 512, mask r=inp (r.val.testBit 8) (sample r) := by decide +kernel
  have outputsAgree : ∀ r : Fin 512, (List.foldl (fun (a b : Nat) => a*1000000000000000000+b) 0 [13407807929,942597095939831376,727811673905304651,18912648022854022,873869787405066962,725179222507908767,667956533170508564,710083788841651696,458571261487544520] : Nat).testBit r.val =
    (if r.val.testBit 8 then G (sample r) || sample r 0 || sample r 3 else G (sample r)) := by decide +kernel
  have exact' (r : Fin 512) : C.eval (mask r)=(List.foldl (fun (a b : Nat) => a*1000000000000000000+b) 0 [13407807929,942597095939831376,727811673905304651,18912648022854022,873869787405066962,725179222507908767,667956533170508564,710083788841651696,458571261487544520] : Nat).testBit r.val := by
    rw [inputsAgree,outputsAgree]
    cases h : r.val.testBit 8
    · exact lo (sample r)
    · exact hi (sample r)
  let cost := let init : List (Nat × Nat) := List.replicate 10 (1,0)
    let ws := C.gates.foldl (fun (s : List (Nat × Nat)) g =>
      let col := fun j => (g.inputs[j]?.bind fun i => s[i]?).getD (1,0)
      let a := col 0
      let b := col 1
      s ++ [ite (g.op.eval [false]=true) (a.1,a.2+1) (a.1+b.1,a.2+b.2)]) init
    let z := ws.getD C.output (1,0)
    z
  have mismatch : ∃ r : Nat, r<512 ∧ C.eval ((([1,0,4,7,5,2,8,6,3] : List Nat).map (fun i => r.testBit i)) ++ [r.testBit 1 || r.testBit 8]) ≠ (List.foldl (fun (a b : Nat) => a*1000000000000000000+b) 0 [13407807929,942597095939831376,727811673905304651,18912648022854022,873869787405066962,725179222507908767,667956533170508564,710083788841651696,458571261487544520] : Nat).testBit r := by
    by_cases n : cost.2≤1
    · by_cases total : cost.1+cost.2≤15
      · exact trees C fit n total
      · exact sharing C fit sz one rd reader (Or.inr (by omega : 15<cost.1+cost.2))
    · exact sharing C fit sz one rd reader (Or.inl (by omega : 1<cost.2))
  obtain ⟨r,hr,bad⟩ := mismatch
  exact bad (exact' ⟨r,hr⟩)
