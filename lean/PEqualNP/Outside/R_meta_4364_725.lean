import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4364_725
    (pin :
      let paid := fun gs : List Gate => gs.countP fun g => GateOp.rec true true false (fun _ => true) true g.op
      let neg := fun gs : List Gate => gs.countP fun g => GateOp.rec false false true (fun _ => false) false g.op
      ∀ (m : ℕ) (p : Fin (m+1)) (C : Circuit) (w : List (Fin (m+1))), FanInTwo C →
      let f := fun x : Fin (m+1) → Bool => C.eval (w.map x)
      (∃ x, f (Function.update x p true) ≠ f (Function.update x p false)) →
      (∃ y z, f (p.insertNth false y) ≠ f (p.insertNth false z)) →
      ∃ D : Circuit, FanInTwo D ∧ paid D.gates + 1 ≤ paid C.gates ∧ neg D.gates ≤ neg C.gates ∧
        circuitFun m D = fun y => f (p.insertNth false y))
    (bound : ∀ D : Circuit, FanInTwo D →
      D.gates.countP (fun g => GateOp.rec false false true (fun _ => false) false g.op) ≤ 1 →
      circuitFun 8 D = (fun y : Fin 8 → Bool => y 0 && y 1 || y 1 && y 2 || y 2 && y 3 ||
        y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 2 && y 6 || y 3 && y 7 ||
        y 5 && y 6 || y 7 && y 5) →
      13 ≤ D.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (14 : ℕ) → x1.output = (23 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x6 : ℕ) => Bool.false) Bool.false x5.op) x1.gates = (1 : ℕ) → List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => (if x6.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x6.inputs else x6.inputs).any fun (x7 : ℕ) => Decidable.decide (x7 = (6 : ℕ))) x1.gates = (1 : ℕ) → ∃ (x7 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro C fan len _ oneNeg _
  by_contra! correct
  let f := fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 ||
    x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
    x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let w := ([0,1,2,3,4,5,6,7,8,0] : List (Fin 9))
  have agrees (x : Fin 9 → Bool) (hx : x 0 = true ∨ x 6 = false) :
      C.eval (w.map x) = f x := by
    have h : (x 0 || x 6) = x 0 := by rcases hx with h | h <;> simp [h]
    have same : w.map x = List.ofFn x ++ [x 0 || x 6] := by
      rw [h]
      simp [w, List.ofFn_succ]
    rw [same]
    exact correct x
  let p : Fin 9 := 6
  have sensitive : ∃ x : Fin 9 → Bool, C.eval (w.map (Function.update x p true)) ≠
      C.eval (w.map (Function.update x p false)) := by
    let x : Fin 9 → Bool := ![true,false,false,false,false,false,false,false,true]
    refine ⟨x, ?_⟩
    rw [agrees (Function.update x p true) (Or.inl (by rfl)),
      agrees (Function.update x p false) (Or.inl (by rfl))]
    dsimp only [f, x, p]
    decide
  have proper : ∃ y z : Fin 8 → Bool, C.eval (w.map (p.insertNth false y)) ≠
      C.eval (w.map (p.insertNth false z)) := by
    let y : Fin 8 → Bool := ![true,true,false,false,false,false,false,false]
    let z : Fin 8 → Bool := fun _ => false
    refine ⟨y,z,?_⟩
    rw [agrees (p.insertNth false y) (Or.inr (by rfl)),
      agrees (p.insertNth false z) (Or.inr (by rfl))]
    dsimp only [f, y, z, p]
    decide
  obtain ⟨D, fanD, saved, negD, evalD⟩ := pin 8 p C w fan sensitive proper
  have smallNeg : D.gates.countP (fun g => GateOp.rec false false true (fun _ => false) false g.op) ≤ 1 :=
    negD.trans oneNeg.le
  have cost := bound D fanD smallNeg (by
    funext y
    rw [congrFun evalD y]
    change C.eval (w.map (p.insertNth false y)) = _
    rw [agrees (p.insertNth false y) (Or.inr (by rfl))]
    change (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 ||
      y 0 && y 5 || y 1 && false || y 2 && y 6 || y 3 && y 7 || y 5 && y 6 ||
      false && y 7 || y 7 && y 5) = _
    simp)
  let neg : Gate → Bool := fun g => GateOp.rec false false true (fun _ => false) false g.op
  let paid : Gate → Bool := fun g => GateOp.rec true true false (fun _ => true) true g.op
  have account (gs : List Gate) : gs.countP paid + gs.countP neg = gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      cases g with | mk op ins => cases op <;> simp_all [neg,paid] <;> omega
  change D.gates.countP paid + 1 ≤ C.gates.countP paid at saved
  change 13 ≤ D.gates.countP paid at cost
  change C.gates.countP neg = 1 at oneNeg
  change C.gates.length = 14 at len
  have := account C.gates
  omega
