import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The output wire is a gate: an input wire is false at the pair of point 0 and line 0 or at
-- the pair of point 1 and line 1, and a wire past the last gate is false everywhere.
-- A gate is an AND or an OR, so two cases remain, by the operation of the output gate.
theorem PEqualNP.Outside.R_meta_5306_584
    (outAnd :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) → (∀ (x7 x8 : Fin (13 : ℕ)), x1 x7 x8 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x2.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ 26 ≤ x2.output ∧ x2.output < 26 + x2.size) → ∃ (x8 : Finset (Fin (13 : ℕ))) (x9 : Finset (Fin (13 : ℕ))), (∀ x10 ∈ x8, ∀ x12 ∈ x9, ¬x1 x10 x12) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x8 | x1 x11 x10}.card ≤ (2 : ℕ)) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x1 x10 x11}.card ≤ (2 : ℕ)) ∧ ∀ (x10 : Fin (26 : ℕ) → Bool), (∀ x11 ∈ x8, x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true) → (∀ x12 ∈ x9, x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x10 = Bool.true)
    (outOr :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) → (∀ (x7 x8 : Fin (13 : ℕ)), x1 x7 x8 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x2.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 26 ≤ x2.output ∧ x2.output < 26 + x2.size) → ∃ (x8 : Finset (Fin (13 : ℕ))) (x9 : Finset (Fin (13 : ℕ))), (∀ x10 ∈ x8, ∀ x12 ∈ x9, ¬x1 x10 x12) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x8 | x1 x11 x10}.card ≤ (2 : ℕ)) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x1 x10 x11}.card ≤ (2 : ℕ)) ∧ ∀ (x10 : Fin (26 : ℕ) → Bool), (∀ x11 ∈ x8, x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true) → (∀ x12 ∈ x9, x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x10 = Bool.true) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) → (∀ (x7 x8 : Fin (13 : ℕ)), x1 x7 x8 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) → ∃ (x8 : Finset (Fin (13 : ℕ))) (x9 : Finset (Fin (13 : ℕ))), (∀ x10 ∈ x8, ∀ x12 ∈ x9, ¬x1 x10 x12) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x8 | x1 x11 x10}.card ≤ (2 : ℕ)) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x1 x10 x11}.card ≤ (2 : ℕ)) ∧ ∀ (x10 : Fin (26 : ℕ) → Bool), (∀ x11 ∈ x8, x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true) → (∀ x12 ∈ x9, x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x10 = Bool.true := by
  dsimp only
  intro C hmono hsize hnl hnp P1
  have hpre : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      have h1 := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i
        (by rw [List.length_append]; omega)
      have h2 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false
          = w.getD i false := List.getD_append _ _ _ _ hi
      exact h1.trans h2
  have hlen : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      have h1 := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      have h2 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length = w.length + 1 := by
        rw [List.length_append]
        rfl
      have h3 : (g :: gs).length = gs.length + 1 := rfl
      rw [h2] at h1
      rw [h3]
      exact h1.trans (by omega)
  have hinput : ∀ i : ℕ, i < 26 →
      (((List.ofFn fun (k : Fin 26) => decide (k = Fin.castAdd 13 (0 : Fin 13) ∨ k = Fin.natAdd 13 (0 : Fin 13)))).getD i false && ((List.ofFn fun (k : Fin 26) => decide (k = Fin.castAdd 13 (1 : Fin 13) ∨ k = Fin.natAdd 13 (1 : Fin 13)))).getD i false) = false := by decide
  have e0 : (C.gates.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn fun (k : Fin 26) => decide (k = Fin.castAdd 13 (0 : Fin 13) ∨ k = Fin.natAdd 13 (0 : Fin 13)))).getD C.output false = true := P1 0 0 (Or.inl rfl)
  have e1 : (C.gates.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn fun (k : Fin 26) => decide (k = Fin.castAdd 13 (1 : Fin 13) ∨ k = Fin.natAdd 13 (1 : Fin 13)))).getD C.output false = true := P1 1 1 (Or.inl rfl)
  have hlo : 26 ≤ C.output := by
    by_contra hlt
    have hc26 : C.output < 26 := by omega
    rw [hpre _ _ C.output (by simp; omega)] at e0 e1
    have h := hinput C.output hc26
    rw [e0, e1] at h
    exact absurd h (by decide)
  have hhi : C.output < 26 + C.size := by
    by_contra hge
    have hl := hlen C.gates (List.ofFn fun (k : Fin 26) => decide (k = Fin.castAdd 13 (0 : Fin 13) ∨ k = Fin.natAdd 13 (0 : Fin 13)))
    have hd : (C.gates.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn fun (k : Fin 26) => decide (k = Fin.castAdd 13 (0 : Fin 13) ∨ k = Fin.natAdd 13 (0 : Fin 13)))).getD C.output false = false :=
      List.getD_eq_default _ _ (by
        rw [hl]
        have : C.size = C.gates.length := rfl
        simp
        omega)
    rw [hd] at e0
    exact absurd e0 (by decide)
  have hj : C.output - 26 < C.gates.length := by
    have : C.size = C.gates.length := rfl
    omega
  have hmem : NestedCover.gateAt C (C.output - 26) ∈ C.gates := by
    show C.gates.getD (C.output - 26) _ ∈ C.gates
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  rcases (hmono _ hmem).1 with hA | hA
  · exact outAnd C hmono hsize hnl hnp P1 ⟨hA, hlo, hhi⟩
  · exact outOr C hmono hsize hnl hnp P1 ⟨hA, hlo, hhi⟩

