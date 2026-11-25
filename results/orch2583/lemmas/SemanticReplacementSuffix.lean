namespace PEqualNP.Outside.L_meta_2583.SemanticReplacement

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2583.Semantic
open PEqualNP.Outside.L_meta_2583.SemanticOr

lemma triple_core_replacement (m n : Nat) (C : Circuit)
    (back : ReadsBack (m + n) C)
    (two : ∀ g ∈ C.gates, g.inputs.length = 2) (a b c : Nat)
    (P Wp : Finset (Fin m)) (L Wl : Finset (Fin n))
    (noRectangle : ∀ p ∈ P, ∀ p' ∈ P, ∀ l ∈ L, ∀ l' ∈ L,
      p ≠ p' → l ≠ l' →
      ¬ ((p ∈ Wp ∨ l ∈ Wl) ∧ (p ∈ Wp ∨ l' ∈ Wl) ∧
         (p' ∈ Wp ∨ l ∈ Wl) ∧ (p' ∈ Wp ∨ l' ∈ Wl)))
    (aSize : (orIn (m + n) C a).card = P.card)
    (bSize : (orIn (m + n) C b).card = L.card)
    (cSize : (orIn (m + n) C c).card = Wp.card + Wl.card)
    (ab : (orIn (m + n) C a ∩ orIn (m + n) C b).card ≤ 1)
    (ac : (orIn (m + n) C a ∩ orIn (m + n) C c).card ≤ 1)
    (bc : (orIn (m + n) C b ∩ orIn (m + n) C c).card ≤ 1) :
    ∃ D : Circuit, IsAO2 (m + n) D ∧
      (∀ z : Fin (m + n) → Bool, circuitFun (m + n) D z =
        decide (∃ p l, (p, l) ∈ ((P ∩ Wp) ×ˢ L) ∪ (P ×ˢ (L ∩ Wl)) ∧
          z (Fin.castAdd n p) = true ∧ z (Fin.natAdd m l) = true)) ∧
      D.size ≤ (s2234_srv (m + n) C {a, b, c}).card + 2 ∧
      PEqualNP.ReadK.IsReadK (m + n) D 1 := by
  obtain ⟨U, V, cover, cost⟩ := triple_pair_core_cover P Wp L Wl noRectangle
  obtain ⟨D, legal, size, computes, read⟩ := SemanticBuilder.build m n
    (((P ∩ Wp) ×ˢ L) ∪ (P ×ˢ (L ∩ Wl))) U V cover
  refine ⟨D, legal, computes, ?_, read⟩
  have budget := three_support_count (m + n) C back two a b c ab ac bc
  omega

end PEqualNP.Outside.L_meta_2583.SemanticReplacement
