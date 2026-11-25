import PEqualNP.Defs.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2602_aux.ClassificationObstruction

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.and, [1,3]⟩, ⟨.or, [0,4]⟩, ⟨.or, [2,4]⟩, ⟨.and, [5,6]⟩], 7⟩

def pairInput (p l : Fin 2) : Fin 4 → Bool :=
  fun i => decide (i.val = p.val ∨ i.val = 2 + l.val)

lemma full_semantics : ∀ x : Fin 4 → Bool,
    circuit.eval (List.ofFn x) = ((x 0 && x 2) || (x 1 && x 3)) := by
  decide

lemma side_classes :
    let P := circuit.wires (List.ofFn fun i : Fin 4 => decide (i.val < 2))
    let L := circuit.wires (List.ofFn fun i : Fin 4 => decide (2 ≤ i.val))
    P.getD 4 false = false ∧ L.getD 4 false = false ∧
    P.getD 5 false = true ∧ L.getD 5 false = false ∧
    P.getD 6 false = false ∧ L.getD 6 false = true ∧
    P.getD 7 false = false ∧ L.getD 7 false = false := by
  decide

lemma matching_pairs : ∀ p l : Fin 2,
    circuit.eval (List.ofFn (pairInput p l)) = true ↔ p = l := by
  decide

lemma final_pairs_not_rectangle :
    ¬ ∃ P L : Finset (Fin 2), ∀ p l,
      circuit.eval (List.ofFn (pairInput p l)) = true ↔ p ∈ P ∧ l ∈ L := by
  rintro ⟨P,L,h⟩
  have h0 := (h 0 0).mp ((matching_pairs 0 0).mpr rfl)
  have h1 := (h 1 1).mp ((matching_pairs 1 1).mpr rfl)
  have bad : (0 : Fin 2) = 1 := (matching_pairs 0 1).mp ((h 0 1).mpr ⟨h0.1,h1.2⟩)
  exact (by decide : (0 : Fin 2) ≠ 1) bad

lemma inherited_second_edge :
    (circuit.wires (List.ofFn (pairInput 1 1))).getD 4 false = true ∧
    (circuit.wires (List.ofFn (pairInput 0 0))).getD 4 false = false := by
  decide

end PEqualNP.Outside.L_meta_2602_aux.ClassificationObstruction
