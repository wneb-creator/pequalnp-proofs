import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux.UnusedStarObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : Finset (Fin 2 × Fin 2) := {(0, 0), (0, 1), (1, 1)}

def circuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 2]⟩, ⟨.or, [5, 3]⟩,
    ⟨.and, [4, 6]⟩, ⟨.or, [2, 3]⟩], 7⟩

lemma no_rectangle : ∀ (a a' b b' : Fin 2), a ≠ a' → b ≠ b' →
    ¬ ((a, b) ∈ edges ∧ (a, b') ∈ edges ∧ (a', b) ∈ edges ∧ (a', b') ∈ edges) := by
  decide +kernel

lemma circuit_ao : PEqualNP.TopForm.IsAO2 4 circuit := by decide +kernel

lemma computes : ∀ x : Fin 4 → Bool,
    circuitFun 4 circuit x = decide (∃ (a b : Fin 2),
      (a, b) ∈ edges ∧ x (Fin.castAdd 2 a) = true ∧ x (Fin.natAdd 2 b) = true) := by
  decide +kernel

lemma no_two_colour :
    PEqualNP.TwoColour.tCount 4 circuit (fun i => decide (2 ≤ i)) = 0 := by
  decide +kernel

def LineStar (a b : Fin 2) (j : ℕ) (Q : Finset (Fin 2)) : Prop :=
  j < circuit.gates.length ∧ (NestedCover.gateAt circuit j).op = GateOp.or ∧
  2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a, b') ∈ edges) ∧
  ∀ x : Fin 4 → Bool, (circuit.wires (List.ofFn x)).getD (4+j) false =
    decide (∃ b' ∈ Q, x (Fin.natAdd 2 b') = true)

def PointStar (a b : Fin 2) (j : ℕ) (P : Finset (Fin 2)) : Prop :=
  j < circuit.gates.length ∧ (NestedCover.gateAt circuit j).op = GateOp.or ∧
  2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a', b) ∈ edges) ∧
  ∀ x : Fin 4 → Bool, (circuit.wires (List.ofFn x)).getD (4+j) false =
    decide (∃ a' ∈ P, x (Fin.castAdd 2 a') = true)

lemma all_edges_have_stars : ∀ a b, (a, b) ∈ edges →
    (∃ j Q, LineStar a b j Q) ∨ (∃ j P, PointStar a b j P) := by
  have h : ∀ a b, (a, b) ∈ edges → a = 0 ∨ (a = 1 ∧ b = 1) := by decide
  intro a b he
  rcases h a b he with rfl | ⟨rfl, rfl⟩
  · left
    refine ⟨4, Finset.univ, by decide, rfl, by decide, Finset.mem_univ _, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
  · right
    refine ⟨0, Finset.univ, by decide, rfl, by decide, Finset.mem_univ _, ?_, ?_⟩
    · decide +kernel
    · decide +kernel

lemma first_edge_only_has_last_star :
    (∀ (j : Fin 5) Q, LineStar 0 0 j.val Q → j.val = 4) ∧
    (∀ (j : Fin 5) P, ¬ PointStar 0 0 j.val P) := by
  have hl : ∀ (j : Fin 5) (Q : Finset (Fin 2)), 2 ≤ Q.card →
      (∀ x : Fin 4 → Bool, (circuit.wires (List.ofFn x)).getD (4+j.val) false =
        decide (∃ b' ∈ Q, x (Fin.natAdd 2 b') = true)) → j.val = 4 := by decide +kernel
  have hp : ∀ P : Finset (Fin 2), 2 ≤ P.card → (∀ a' ∈ P, (a', 0) ∈ edges) → False := by
    decide +kernel
  constructor
  · intro j Q h
    exact hl j Q h.2.2.1 h.2.2.2.2.2
  · intro j P h
    exact hp P h.2.2.1 h.2.2.2.2.1

lemma last_star_unused : circuit.output ≠ 8 ∧ ∀ g ∈ circuit.gates, 8 ∉ g.inputs := by
  decide

lemma not_read_one : ¬ PEqualNP.ReadK.IsReadK 4 circuit 1 := by
  intro hr
  have hp : PEqualNP.ReadK.IsPrimeImplicant 4 circuit ({0, 2} : Finset (Fin 4)) := by
    decide +kernel
  have hf : PEqualNP.ReadK.readsAtMost circuit 4
      (PEqualNP.ReadK.setList ({0, 2} : Finset (Fin 4))) 1 = false := by decide +kernel
  have h := hr {0, 2} hp
  rw [hf] at h
  cases h

lemma posted_bound_holds :
    edges.card + ({0, 1} : Finset (Fin 4)).card ≤ circuit.size + 1 := by decide

end PEqualNP.Outside.L_meta_4970_aux.UnusedStarObstruction
