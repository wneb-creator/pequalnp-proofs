import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17962

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem wires_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons]; rw [ih]; simp; omega

theorem key (n : ℕ) (C : Circuit) (a b : ℕ) (h : PEqualNP.TopForm.IsAO2 n C) (hnd : ∀ g ∈ C.gates, g.inputs.Nodup)
    (hab : a ≠ b) (ha : a < n + C.size) (hb : b < n + C.size) :
    let D : Circuit := ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], n + C.size⟩
    PEqualNP.TopForm.IsAO2 n D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
      ∀ x : Fin n → Bool, ∀ w < n + C.size, PEqualNP.BlindGate.wireValue D n x w = PEqualNP.BlindGate.wireValue C n x w := by
  intro D
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h1 g hg
    · rw [List.mem_singleton.1 hg]; left; rfl
  · intro j hj i hi
    simp only [D, List.length_append, List.length_singleton] at hj
    rcases Nat.lt_or_ge j C.gates.length with hj' | hj'
    · have e : PEqualNP.MetaComplexity.NestedCover.gateAt D j = PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, D, List.getD_eq_getElem?_getD, List.getElem?_append_left hj']
      rw [e] at hi; exact h2 j hj' i hi
    · have hjj : j = C.gates.length := by omega
      subst hjj
      have e : PEqualNP.MetaComplexity.NestedCover.gateAt D C.gates.length = ⟨GateOp.and, [a, b]⟩ := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, D, List.getD_eq_getElem?_getD]
      rw [e] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      unfold Circuit.size at ha hb
      rcases hi with rfl | rfl <;> omega
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h3 g hg
    · rw [List.mem_singleton.1 hg]; rfl
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hnd g hg
    · rw [List.mem_singleton.1 hg]; simp [hab]
  · intro x w hw
    simp only [PEqualNP.BlindGate.wireValue, Circuit.wires, D, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hl := wires_len C.gates (List.ofFn x)
    simp only [List.length_ofFn] at hl
    unfold Circuit.size at hw
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hl]; exact hw), ← List.getD_eq_getElem?_getD]

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_17962

theorem PEqualNP.Outside.L_meta_17962 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.TopForm.IsAO2 x1 x2 →     (∀ x6 ∈ x2.gates, x6.inputs.Nodup) →       x3 ≠ x4 →         x3 < x1 + x2.size →           x4 < x1 + x2.size →             have x10 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate }], output := x1 + x2.size : PEqualNP.CircuitLowerBounds.Circuit };             PEqualNP.TopForm.IsAO2 x1 x10 ∧ (∀ x11 ∈ x10.gates, x11.inputs.Nodup) ∧ ∀ (x11 : Fin x1 → Bool), ∀ x12 < x1 + x2.size, PEqualNP.BlindGate.wireValue x10 x1 x11 x12 = PEqualNP.BlindGate.wireValue x2 x1 x11 x12 := by
  intro x1 x2 x3 x4 h hnd hab ha hb
  exact L_meta_17962.key x1 x2 x3 x4 h hnd hab ha hb
