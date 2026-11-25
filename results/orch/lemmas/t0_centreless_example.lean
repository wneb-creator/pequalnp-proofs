import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux.TwoColourExample
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def C : Circuit where
  gates := [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.and, [0, 0]⟩,
    ⟨GateOp.or, [7, 2]⟩, ⟨GateOp.and, [6, 8]⟩]
  output := 9

def E : Finset (Fin 2 × Fin 2) := {(0, 0), (0, 1), (1, 0)}

def G : SimpleGraph (Fin 4) := SimpleGraph.fromRel
  (fun a b => (a.val, b.val) ∈ ([(0, 2), (0, 3), (1, 2)] : List (ℕ × ℕ)))

instance : DecidableRel G.Adj := by unfold G; infer_instance

set_option maxRecDepth 20000 in
lemma ao : IsAO2 4 C := by decide

set_option maxRecDepth 20000 in
lemma computes : ∀ x : Fin 4 → Bool,
    PEqualNP.MetaComplexity.circuitFun 4 C x =
      decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd 2 a) = true ∧ x (Fin.natAdd 2 b) = true) := by
  decide

set_option maxRecDepth 20000 in
lemma no_square : ∀ a a' : Fin 2, ∀ b b' : Fin 2,
    a ≠ a' → b ≠ b' → ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E) := by
  decide

set_option maxRecDepth 20000 in
lemma zero_two_colour : PEqualNP.TwoColour.tCount 4 C (fun i => decide (2 ≤ i)) = 0 := by
  decide

set_option maxRecDepth 20000 in
lemma top_form : TopForm G C := by decide

set_option maxRecDepth 20000 in
lemma all_unserved_raw : (Ustar G C).card = 3 := by decide

set_option maxRecDepth 20000 in
lemma ledger_counts : C.size = 6 ∧ (centreless G C).card = 1 ∧
    (junk G C).card = 2 ∧ (orN G C \ lam G C).card = 3 := by decide

set_option maxRecDepth 20000 in
lemma semantic_stars : ∀ a b, (a, b) ∈ E →
    (∃ (j : Fin 6) (Q : Finset (Fin 2)),
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a, b') ∈ E) ∧
      ∀ x : Fin 4 → Bool, (C.wires (List.ofFn x)).getD (4 + j) false =
        decide (∃ b' ∈ Q, x (Fin.natAdd 2 b') = true)) ∨
    (∃ (j : Fin 6) (P : Finset (Fin 2)),
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a', b) ∈ E) ∧
      ∀ x : Fin 4 → Bool, (C.wires (List.ofFn x)).getD (4 + j) false =
        decide (∃ a' ∈ P, x (Fin.castAdd 2 a') = true)) := by
  intro a b hab
  by_cases ha : a = 0
  · subst a
    left
    exact ⟨1, Finset.univ, rfl, by decide, Finset.mem_univ b, by decide, by decide⟩
  · have ha1 : a = 1 := by omega
    subst a
    have hb : b = 0 := by simpa [E] using hab
    subst b
    right
    exact ⟨0, Finset.univ, rfl, by decide, Finset.mem_univ 1, by decide, by decide⟩

end PEqualNP.Outside.L_meta_4970_aux.TwoColourExample
