import DynamicOracleTest
namespace PEqualNP.Outside.L_meta_670_aux.DynamicLeaf

open LiveCheck

def updateWithRecipe {n : Nat} (oracles : Fin n → Oracle) (v w : List Sig)
    (ctx : Context n) (r : Option Recipe) : Context n :=
  fun i => updateOne (oracles i) v w (ctx i) r

lemma updateWithRecipe_valid {n : Nat} {oracles : Fin n → Oracle} {v : List Sig}
    {ctx : Context n} (h : Valid oracles v ctx) (w : List Sig) (r : Option Recipe) :
    Valid oracles w (updateWithRecipe oracles v w ctx r) := by
  intro i
  simp only [updateWithRecipe, updateOne, compact]
  apply List.map_congr_left
  intro a ha
  rw [h i]
  split
  · rename_i he
    rw [proposedValue_map]
    exact congrArg (oracles i).project (beq_iff_eq.mp he).symm
  · exact retrieve_map _ _ _

end PEqualNP.Outside.L_meta_670_aux.DynamicLeaf
