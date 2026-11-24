import TightFirstData
namespace PEqualNP.Outside.L_meta_670_aux.TightFormula
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma first4 (j : Fin 9) (u : Fin 4) : firstCase 4 j u = false := by
  fin_cases j <;> fin_cases u <;> as_aux_lemma => decide +kernel
end PEqualNP.Outside.L_meta_670_aux.TightFormula
