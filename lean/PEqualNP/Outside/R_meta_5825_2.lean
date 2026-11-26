import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5825_2
    (hLower : ∀ (p q : Fin 10) (C : PEqualNP.CircuitLowerBounds.Circuit)
        (a b : Fin 18),
      p ≠ q → PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 17 →
      (let D : PEqualNP.CircuitLowerBounds.Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [p.val, q.val] }] ++ C.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10 + a.val, 10 + b.val] }], output := 11 + C.gates.length };
       ¬ (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) x)))
    (hGlueEval : ∀ (p q : Fin 10) (C : PEqualNP.CircuitLowerBounds.Circuit)
        (a b : Fin 18) (x : Fin 10 → Bool),
      ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [p.val, q.val] }] ++ C.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10 + a.val, 10 + b.val] }], output := 11 + C.gates.length } : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = (
        (((C.wires (({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [p.val, q.val] }], output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x))).getD (10 + a.val) false) ||
         ((C.wires (({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [p.val, q.val] }], output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x))).getD (10 + b.val) false)))) :
∀ (x1 x2 : Fin (10 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Fin (18 : ℕ)),   x1 ≠ x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (17 : ℕ) →         have x9 : PEqualNP.CircuitLowerBounds.Gate := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate };         have x10 : (Fin (10 : ℕ) → Bool) → Bool := fun (x10 : Fin (10 : ℕ) → Bool) => x10 (0 : Fin (10 : ℕ)) && x10 (1 : Fin (10 : ℕ)) || x10 (1 : Fin (10 : ℕ)) && x10 (2 : Fin (10 : ℕ)) || x10 (2 : Fin (10 : ℕ)) && x10 (3 : Fin (10 : ℕ)) || x10 (3 : Fin (10 : ℕ)) && x10 (4 : Fin (10 : ℕ)) || x10 (4 : Fin (10 : ℕ)) && x10 (0 : Fin (10 : ℕ)) || x10 (0 : Fin (10 : ℕ)) && x10 (5 : Fin (10 : ℕ)) || x10 (1 : Fin (10 : ℕ)) && x10 (6 : Fin (10 : ℕ)) || x10 (2 : Fin (10 : ℕ)) && x10 (7 : Fin (10 : ℕ)) || x10 (3 : Fin (10 : ℕ)) && x10 (8 : Fin (10 : ℕ)) || x10 (4 : Fin (10 : ℕ)) && x10 (9 : Fin (10 : ℕ)) || x10 (5 : Fin (10 : ℕ)) && x10 (7 : Fin (10 : ℕ)) || x10 (7 : Fin (10 : ℕ)) && x10 (9 : Fin (10 : ℕ)) || x10 (9 : Fin (10 : ℕ)) && x10 (6 : Fin (10 : ℕ)) || x10 (6 : Fin (10 : ℕ)) && x10 (8 : Fin (10 : ℕ)) || x10 (8 : Fin (10 : ℕ)) && x10 (5 : Fin (10 : ℕ));         have x11 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x11 : Fin (10 : ℕ) → Bool) (x12 : ℕ) => (x3.wires ({ gates := [x9], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x11))).getD x12 Bool.false;         (∃ (x12 : Fin (10 : ℕ) → Bool), x11 x12 ((10 : ℕ) + ↑x4) = Bool.true ∧ x11 x12 ((10 : ℕ) + ↑x5) = Bool.false) → (∃ (x13 : Fin (10 : ℕ) → Bool), x11 x13 ((10 : ℕ) + ↑x4) = Bool.false ∧ x11 x13 ((10 : ℕ) + ↑x5) = Bool.true) → (∀ (x14 : Fin (10 : ℕ) → Bool), x10 x14 = Bool.false → x11 x14 ((10 : ℕ) + ↑x4) = Bool.false ∧ x11 x14 ((10 : ℕ) + ↑x5) = Bool.false) → ∃ (x15 : Fin (10 : ℕ) → Bool), x10 x15 = Bool.true ∧ x11 x15 ((10 : ℕ) + ↑x4) = Bool.false ∧ x11 x15 ((10 : ℕ) + ↑x5) = Bool.false := by
  intro p q C a b hpq hFan hSize hGate edge out hEx₁ hEx₂ hOff
  by_contra hNo
  have hCover : ∀ x : Fin 10 → Bool,
      (out x (10 + a.val) || out x (10 + b.val)) = edge x := by
    intro x
    cases hf : edge x with
    | false =>
        obtain ⟨ha, hb⟩ := hOff x hf
        simp [ha, hb, hf]
    | true =>
        have hnot : ¬ (out x (10 + a.val) = false ∧ out x (10 + b.val) = false) := by
          intro hab
          exact hNo ⟨x, hf, hab.1, hab.2⟩
        cases ha : out x (10 + a.val) <;>
          cases hb : out x (10 + b.val) <;> simp_all
  let D : PEqualNP.CircuitLowerBounds.Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [p.val, q.val] }] ++ C.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10 + a.val, 10 + b.val] }], output := 11 + C.gates.length }
  have hEq : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = edge x := by
    intro x
    have hglue := hGlueEval p q C a b x
    change D.eval (List.ofFn x) = (out x (10 + a.val) || out x (10 + b.val)) at hglue
    rw [hglue]
    exact hCover x
  exact hLower p q C a b hpq hFan hSize hEq
