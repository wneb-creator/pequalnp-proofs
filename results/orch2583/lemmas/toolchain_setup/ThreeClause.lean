import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.ThreeClause

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

lemma double_star_identity (a b A B : Bool) :
    (((a || A) && (b || B)) && (a || b)) =
      ((a && (b || B)) || (b && A)) := by
  cases a <;> cases b <;> cases A <;> cases B <;> rfl

def threeClauseBlock : Circuit :=
  { gates := [⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [0, 1]⟩,
      ⟨.and, [4, 5]⟩, ⟨.and, [7, 6]⟩]
    output := 8 }

def doubleStarBlock : Circuit :=
  { gates := [⟨.or, [1, 3]⟩, ⟨.and, [0, 4]⟩,
      ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩]
    output := 7 }

lemma threeClauseBlock_ao : IsAO2 4 threeClauseBlock := by decide

lemma doubleStarBlock_ao : IsAO2 4 doubleStarBlock := by decide

lemma threeClauseBlock_size : threeClauseBlock.size = 5 := rfl

lemma doubleStarBlock_size : doubleStarBlock.size = 4 := rfl

lemma block_values (z : Fin 4 → Bool) :
    circuitFun 4 threeClauseBlock z = circuitFun 4 doubleStarBlock z := by
  have all : ∀ z : Fin 4 → Bool,
      circuitFun 4 threeClauseBlock z = circuitFun 4 doubleStarBlock z := by decide
  exact all z

lemma doubleStarBlock_read_one : IsReadK 4 doubleStarBlock 1 := by decide

lemma threeClauseBlock_not_read_one : ¬ IsReadK 4 threeClauseBlock 1 := by decide

end PEqualNP.Outside.L_meta_2583_aux.ThreeClause
