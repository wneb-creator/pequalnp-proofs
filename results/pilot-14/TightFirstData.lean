import TightFormulaEndgameTest
namespace PEqualNP.Outside.L_meta_670_aux.TightFormula
open LiveCheck

def firstCase (i j : Fin 9) (u : Fin 4) : Bool :=
  test 3 ((ops (phase (raw.getD i.val zero)) (phase (raw.getD j.val zero))).getD u.val zero :: inputs)
end PEqualNP.Outside.L_meta_670_aux.TightFormula
