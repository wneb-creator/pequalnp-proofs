import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

abbrev c5Graph : SimpleGraph (Fin 5) :=
  edgeGraph 5 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

def c5Circuit : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.and, [0, 5]⟩,
    ⟨.or, [1, 3]⟩, ⟨.and, [2, 7]⟩,
    ⟨.and, [3, 4]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [9, 10]⟩], 11⟩

lemma c5_size : c5Circuit.size = 7 := rfl

lemma c5_no_triangle : ∀ a b c : Fin 5,
    c5Graph.Adj a b → c5Graph.Adj b c → ¬ c5Graph.Adj c a := by
  decide

lemma c5_no_four : ∀ a b c d : Fin 5,
    c5Graph.Adj a b → c5Graph.Adj b c → c5Graph.Adj c d → c5Graph.Adj d a →
      a = c ∨ b = d := by
  decide

lemma c5_monotone : Monotone2 c5Circuit := by
  simp [Monotone2, c5Circuit]

lemma c5_computes : ∀ x : Fin 5 → Bool,
    c5Circuit.eval (List.ofFn x) =
      decide (∃ u v : Fin 5, c5Graph.Adj u v ∧ x u = true ∧ x v = true) := by
  decide

lemma c5_star : HasStarProfile 5 c5Graph c5Circuit := by
  decide

lemma c5_nonempty : ∀ j < c5Circuit.gates.length,
    (PEqualNP.MetaComplexity.NestedCover.gateAt c5Circuit j).op = GateOp.and →
      ∃ u v : Fin 5, c5Graph.Adj u v ∧ Owns 5 c5Circuit j u v := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  decide

end PEqualNP.Outside.L_meta_1031_aux
