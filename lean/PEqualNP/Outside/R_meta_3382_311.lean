import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3382_311
    (noNot :
      let f (x : Fin 7 → Bool) := ([1,12,4,15,26,35,46,36] : List ℕ).any
        (fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10)))
      ∀ C : Circuit, FanInTwo C → C.size = 11 → circuitFun 7 C = f →
        ∀ g ∈ C.gates, g.op ≠ .not)
    (readers :
      let bits (r : ℕ) := List.ofFn (fun i : Fin 7 => r.testBit i.val)
      let tests (v : ℕ → Bool) (p n : List ℕ) :=
        (p.all v && n.all (fun r => !v r)) = true
      ∀ (C D : Circuit) (a b : ℕ), Monotone2 C → C.size = 11 →
        List.Forall₂ (fun g h : Gate => g.op = h.op ∧ List.Forall₂
          (fun i j : ℕ => j = i+1 ∨ j = 0 ∧ (i = a ∨ i = b)) g.inputs h.inputs)
          C.gates D.gates →
        tests (fun r => C.eval (bits r)) [3,6,17,34,68,40,80,72] [13,26,28,37,52,66,97] →
        tests (fun r => (D.wires (true :: bits r)).getD (C.output+1) false)
          [3,4,17,34,40,72,80] [9,26,48,66,97] →
        (C.gates.filter (fun g => g.op.eval [true,false] && g.inputs.contains 2)).length < 2) :
    have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (11 : ℕ) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = x1 → List.Forall₂ (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) => x9.op = x10.op ∧ List.Forall₂ (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5)) x9.inputs x10.inputs) x2.gates x3.gates → (∀ (x10 : Fin (7 : ℕ) → Bool), (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false = (x1 x10 || x10 (2 : Fin (7 : ℕ)))) → (List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.true, Bool.false] && x11.inputs.contains (2 : ℕ)) x2.gates).length < (2 : ℕ) := by
  intro f C D a b fan size base edits modified
  have mono : Monotone2 C := by
    intro g hg
    refine ⟨?_, (fan g hg).2⟩
    change g.op = .and ∨ g.op = .or
    rcases (show g.op = .and ∨ g.op = .or ∨ g.op = .not from (fan g hg).1) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (noNot C fan size base g hg h).elim
  let x (r : ℕ) (i : Fin 7) := r.testBit i.val
  have baseRow (r : ℕ) : C.eval (List.ofFn (x r)) = f (x r) := congrFun base (x r)
  have editRow (r : ℕ) : (D.wires (true :: List.ofFn (x r))).getD (C.output+1) false =
      (f (x r) || x r 2) := modified (x r)
  apply readers C D a b mono size edits
  · change (([3,6,17,34,68,40,80,72] : List ℕ).all (fun r => C.eval (List.ofFn (x r))) &&
      ([13,26,28,37,52,66,97] : List ℕ).all (fun r => !C.eval (List.ofFn (x r)))) = true
    simp only [baseRow]
    decide +kernel
  · change (([3,4,17,34,40,72,80] : List ℕ).all
      (fun r => (D.wires (true :: List.ofFn (x r))).getD (C.output+1) false) &&
      ([9,26,48,66,97] : List ℕ).all
      (fun r => !(D.wires (true :: List.ofFn (x r))).getD (C.output+1) false)) = true
    simp only [editRow]
    decide +kernel
