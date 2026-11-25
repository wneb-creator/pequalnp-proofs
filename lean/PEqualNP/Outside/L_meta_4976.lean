import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4976 : ∀ (x1 : Finset (Fin (9 : ℕ))) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x1.card ≤ (2 : ℕ) → PEqualNP.NotBracket.notCount x2 = (0 : ℕ) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x6 ∧ PEqualNP.NotBracket.notCount x6 = (0 : ℕ) ∧ x6.size = x2.size + (2 : ℕ) ∧ ∀ (x7 : Fin (9 : ℕ) → Bool), x6.eval (List.ofFn x7) = x2.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x8 ∈ x1, x7 x8 = Bool.true)]) := by
  intro S C hC hS hn
  let g1 : Gate := ⟨GateOp.or, [0, 4]⟩
  let g2 : Gate := ⟨GateOp.or, S.toList.map Fin.val⟩
  refine ⟨⟨g1 :: g2 :: C.gates, C.output⟩, ?_, ?_, by simp [Circuit.size], fun x => ?_⟩
  · intro g hg
    rcases List.mem_cons.1 hg with h | hg
    · rw [h]; simp [g1]
    · rcases List.mem_cons.1 hg with h | hg
      · rw [h]; simpa [g2] using hS
      · exact hC g hg
  · simpa [PEqualNP.NotBracket.notCount, g1, g2] using hn
  · have get : ∀ (i : Fin 9) (l : List Bool), (List.ofFn x ++ l).getD i.val false = x i := by
      intro i l
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp),
        List.getElem?_eq_getElem (by simp), List.getElem_ofFn]
      rfl
    have e1 : g1.op.eval (g1.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 4) := by
      have h0 := get 0 []
      have h4 := get 4 []
      rw [List.append_nil] at h0 h4
      change GateOp.or.eval [(List.ofFn x).getD (0 : Fin 9).val false,
        (List.ofFn x).getD (4 : Fin 9).val false] = _
      rw [h0, h4]
      simp [GateOp.eval]
    have e2 : g2.op.eval (g2.inputs.map fun i => (List.ofFn x ++ [x 0 || x 4]).getD i false) =
        decide (∃ i ∈ S, x i = true) := by
      rw [Bool.eq_iff_iff]
      simp only [g2, GateOp.eval, List.map_map, List.any_map, List.any_eq_true, Function.comp, id,
        decide_eq_true_eq, get, Finset.mem_toList]
    change (List.foldl _ ((List.ofFn x ++ [g1.op.eval (g1.inputs.map fun i =>
      (List.ofFn x).getD i false)]) ++ [g2.op.eval (g2.inputs.map fun i => (List.ofFn x ++
      [g1.op.eval (g1.inputs.map fun i => (List.ofFn x).getD i false)]).getD i false)]) C.gates).getD
      C.output false = _
    rw [e1, e2, List.append_assoc]
    rfl
