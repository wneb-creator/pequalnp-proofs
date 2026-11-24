import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5282_aux

open PEqualNP.CircuitLowerBounds PEqualNP.InvisibleWire PEqualNP.BlindGate

lemma light_set {n : ℕ} (S : Finset (Fin n)) (hS : S.card ≤ 1) :
    IsLight n (fun i => decide (i ∈ S)) := by
  simpa [IsLight] using hS

lemma invisible_iff_sets {n : ℕ} (C : Circuit) (w : ℕ) :
    IsInvisible C n w ↔
      ∀ S : Finset (Fin n), S.card ≤ 1 →
        (C.wires (List.ofFn (fun i => decide (i ∈ S)))).getD w false = false := by
  constructor
  · intro h S hS
    exact h _ (light_set S hS)
  · intro h x hx
    let S := Finset.univ.filter fun i => x i = true
    have heq : (fun i => decide (i ∈ S)) = x := by
      funext i
      simp [S]
    have hS : S.card ≤ 1 := hx
    have z := h S hS
    rw [heq] at z
    exact z

lemma edge_false_of_card_le_one {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (S : Finset (Fin n)) (hS : S.card ≤ 1) :
    decide (∃ a b, G.Adj a b ∧ decide (a ∈ S) = true ∧ decide (b ∈ S) = true) = false := by
  apply decide_eq_false
  rintro ⟨a, b, hab, ha, hb⟩
  have eq : a = b := Finset.card_le_one.mp hS a (of_decide_eq_true ha) b (of_decide_eq_true hb)
  subst b
  exact hab.ne rfl

lemma empty_graph_case {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : ∀ a b, ¬G.Adj a b) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) ∧
      (∀ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) → C.size ≤ D.size) ∧
      (∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
        ∀ S : Finset (Fin n), S.card ≤ 1 →
          (C.wires (List.ofFn (fun i => decide (i ∈ S)))).getD (n + j) false = false) := by
  refine ⟨⟨[], n⟩, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · intro x
    simp [Circuit.eval, Circuit.wires, List.getD, hG]
  · intro D _ _
    simp [Circuit.size]
  · intro j g h
    simp at h

end PEqualNP.Outside.L_meta_5282_aux
