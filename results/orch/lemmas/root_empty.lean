import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031

open PEqualNP.CircuitLowerBounds

lemma empty_graph (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hEmpty : ∀ u v : Fin n, ¬ G.Adj u v) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ (∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧ ∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[t]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false)) ∧ ∀ u v : Fin n, G.Adj u v → ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) → u = c ∨ v = c := by
  refine ⟨⟨[], n⟩, ?_, ?_, ?_, ?_⟩
  · simp
  · intro x
    simp [Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD, hEmpty]
  · intro D _ _
    exact Nat.zero_le _
  · intro t g hg
    simp at hg

end PEqualNP.Outside.L_meta_1031
