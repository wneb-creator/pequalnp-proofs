-- Research import scope only; canonical InputReindex.lean retains the required Defs import.
import PEqualNP.Defs.MetaComplexity

-- Input transport adapted from lv1xx, R_meta_1890_1, accepted in upstream PR 7680.
-- The original proof credits R_meta_2736_91 for its wire-evaluation argument.
namespace PEqualNP.Outside.L_meta_1890_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem reindex_inputs :
    ∀ (n : ℕ) (C : Circuit) (p : Fin n → Fin n), FanInTwo C →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
        ∀ (x : Fin n → Bool) (tail : List Bool),
          D.eval (List.ofFn x ++ tail) = C.eval (List.ofFn (x ∘ p) ++ tail) := by
  intro n C p hfan
  let rename (i : ℕ) : ℕ := if hi : i < n then (p ⟨i, hi⟩).val else i
  have early (i : ℕ) (hi : i < n) : rename i < n := by simp [rename, hi]
  have late (i : ℕ) (hi : n ≤ i) : rename i = i := by simp [rename, Nat.not_lt.mpr hi]
  let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩
  let D : Circuit := ⟨C.gates.map mapGate, rename C.output⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact ⟨(hfan g' hg').1, by simpa [mapGate] using (hfan g' hg').2⟩
  · exact List.length_map mapGate
  have run (gs : List Gate) (x y : List Bool) (len : x.length = y.length)
      (lo : n ≤ x.length) (agree : ∀ i, y.getD (rename i) false = x.getD i false) :
      ∀ i, ((Circuit.mk (gs.map mapGate) 0).wires y).getD (rename i) false =
        ((Circuit.mk gs 0).wires x).getD i false := by
    induction gs generalizing x y with
    | nil => exact agree
    | cons g rest ih =>
      let b := g.op.eval (g.inputs.map fun i => x.getD i false)
      have next : (mapGate g).op.eval ((mapGate g).inputs.map fun i => y.getD i false) = b := by
        simp only [b, mapGate, List.map_map, Function.comp_def, agree]
      change ∀ i, ((Circuit.mk (rest.map mapGate) 0).wires (y ++ [_])).getD (rename i) false =
        ((Circuit.mk rest 0).wires (x ++ [b])).getD i false
      rw [next]
      apply ih _ _ (by simp [len]) (by simp; omega)
      intro i
      by_cases hi : i < x.length
      · have hy : rename i < y.length := by
          by_cases hn : i < n
          · have := early i hn
            omega
          · rw [late i (by omega)]
            omega
        rw [List.getD_append _ _ _ _ hy, List.getD_append _ _ _ _ hi]
        exact agree i
      · rw [late i (by omega), List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega), len]
  intro x tail
  apply run C.gates _ _ (by simp) (by simp) _ C.output
  intro i
  by_cases hi : i < n
  · have hx : rename i < (List.ofFn x).length := by simpa using early i hi
    have hy : i < (List.ofFn (x ∘ p)).length := by simpa using hi
    rw [List.getD_append _ _ _ _ hx, List.getD_append _ _ _ _ hy,
        List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy]
    simp only [List.getElem_ofFn, Function.comp_apply]
    congr 1
    apply Fin.ext
    exact dite_eq_left hi
  · rw [late i (by omega), List.getD_append_right _ _ _ _ (by simpa using Nat.not_lt.mp hi),
        List.getD_append_right _ _ _ _ (by simpa using Nat.not_lt.mp hi)]
    simp

end PEqualNP.Outside.L_meta_1890_aux
