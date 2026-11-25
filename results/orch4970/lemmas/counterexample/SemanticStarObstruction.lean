import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux.SemanticStarObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : Finset (Fin 1 × Fin 2) := Finset.univ

def circuit : Circuit :=
  ⟨[⟨.and, [1, 1]⟩, ⟨.or, [3, 2]⟩, ⟨.and, [0, 4]⟩], 5⟩

lemma no_rectangle : ∀ (a a' : Fin 1) (b b' : Fin 2),
    a ≠ a' → b ≠ b' →
    ¬ ((a, b) ∈ edges ∧ (a, b') ∈ edges ∧ (a', b) ∈ edges ∧ (a', b') ∈ edges) := by
  decide +kernel

lemma circuit_ao : PEqualNP.TopForm.IsAO2 3 circuit := by decide +kernel

lemma computes : ∀ x : Fin 3 → Bool,
    circuitFun 3 circuit x = decide (∃ (a : Fin 1) (b : Fin 2),
      (a, b) ∈ edges ∧ x (Fin.castAdd 2 a) = true ∧ x (Fin.natAdd 1 b) = true) := by
  decide +kernel

lemma no_two_colour :
    PEqualNP.TwoColour.tCount 3 circuit (fun i => decide (1 ≤ i)) = 0 := by
  decide +kernel

lemma semantic_star : ∀ (a : Fin 1) (b : Fin 2), (a, b) ∈ edges →
    ∃ (j : ℕ) (Q : Finset (Fin 2)), j < circuit.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt circuit j).op = GateOp.or ∧
      2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a, b') ∈ edges) ∧
      ∀ x : Fin 3 → Bool, (circuit.wires (List.ofFn x)).getD (3+j) false =
        decide (∃ b' ∈ Q, x (Fin.natAdd 1 b') = true) := by
  intro a b _
  refine ⟨1, Finset.univ, by decide, rfl, by decide, Finset.mem_univ _, ?_, ?_⟩
  · intro b' _
    exact Finset.mem_univ _
  · decide +kernel

lemma semantic_star_or_reach :
    PEqualNP.TopForm.orIn 3 circuit 4 = ({2} : Finset (Fin 3)) := by decide +kernel

lemma repeated_edge :
    PEqualNP.ReadK.readsAtMost circuit 3 [0, 1] 1 = false := by decide +kernel

lemma not_read_one : ¬ PEqualNP.ReadK.IsReadK 3 circuit 1 := by
  intro hr
  have hp : PEqualNP.ReadK.IsPrimeImplicant 3 circuit ({0, 1} : Finset (Fin 3)) := by
    decide +kernel
  have hb : PEqualNP.ReadK.setList ({0, 1} : Finset (Fin 3)) = [0, 1] := by decide
  have h := hr {0, 1} hp
  rw [hb, repeated_edge] at h
  cases h

lemma posted_bound_holds : edges.card + ({0} : Finset (Fin 3)).card ≤ circuit.size + 1 := by
  decide

end PEqualNP.Outside.L_meta_4970_aux.SemanticStarObstruction
