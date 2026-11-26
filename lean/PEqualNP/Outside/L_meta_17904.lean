import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17904
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun (a : List Bool) (g : Gate) => a ++ [g.op.eval (g.inputs.map
      fun i => a.getD i false)]) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp
    omega

private theorem main (i : Fin 11) (C : Circuit) (a b : Fin 18) (s : ℕ)
    (hC : FanInTwo C) (hs : C.size ≤ s) (f : (Fin 10 → Bool) → Bool)
    (hf : ∀ x,
      f x = ((C.wires ((Circuit.mk [⟨GateOp.not, [i.val]⟩] 0).wires (List.ofFn x))).getD
        (10 + a.val) false ||
      (C.wires ((Circuit.mk [⟨GateOp.not, [i.val]⟩] 0).wires (List.ofFn x))).getD
        (10 + b.val) false)) :
    HasCircuitSize 10 f (s + 2) := by
  let g : Gate := ⟨GateOp.not, [i.val]⟩
  let h : Gate := ⟨GateOp.or, [10 + a.val, 10 + b.val]⟩
  refine ⟨⟨g :: (C.gates ++ [h]), 11 + C.size⟩, ?_, ?_, ?_⟩
  · intro q hq
    change q ∈ g :: (C.gates ++ [h]) at hq
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | hq | rfl
    · simp [g]
    · exact hC q hq
    · simp [h]
  · unfold Circuit.size at *
    simp
    omega
  · intro x
    let w := C.wires ((Circuit.mk [g] 0).wires (List.ofFn x))
    have hw : w.length = 11 + C.size := by
      unfold w Circuit.wires
      rw [fold_length, fold_length]
      simp [Circuit.size]
    rw [hf]
    simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_append, List.foldl_nil]
    change (w ++ [h.op.eval (h.inputs.map (fun j => w.getD j false))]).getD
      (11 + C.size) false = (w.getD (10 + a.val) false || w.getD (10 + b.val) false)
    rw [← hw]
    simp [h, GateOp.eval, List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_17904

theorem PEqualNP.Outside.L_meta_17904 : (∀ (x1 : Fin (11 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin (18 : ℕ)) (x5 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ x5 →       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [↑x1] : PEqualNP.CircuitLowerBounds.Gate }], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x8))).getD x9 Bool.false;       ∀ (x9 : (Fin (10 : ℕ) → Bool) → Bool), (∀ (x10 : Fin (10 : ℕ) → Bool), x9 x10 = (x8 x10 ((10 : ℕ) + ↑x3) || x8 x10 ((10 : ℕ) + ↑x4))) → PEqualNP.MetaComplexity.HasCircuitSize (10 : ℕ) x9 (x5 + (2 : ℕ))) := by
  exact PEqualNP.Outside.L_meta_17904.main
