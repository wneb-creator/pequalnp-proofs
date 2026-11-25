import CanonicalCompilerDefs
import CanonicalCompilerStructure
import CanonicalCompilerSemantics

namespace PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

def cycleControl : Program 4 2 :=
(([⟨2, by decide⟩], [⟨0, by decide⟩]),
(([⟨1, by decide⟩, ⟨4, by decide⟩], [⟨3, by decide⟩, ⟨4, by decide⟩]),
[⟨4, by decide⟩, ⟨5, by decide⟩]))

end PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

namespace PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma cycleControl_correct (input : Fin 4 → Bool) :
    circuitFun 4 (compile 2 cycleControl 4 Fin.val) input =
      ((input 0 || input 2) && (input 1 || input 3)) := by
  rw [compile_circuitFun]
  have h : ∀ input : Fin 4 → Bool, evaluate 2 cycleControl input =
      ((input 0 || input 2) && (input 1 || input 3)) := by
    decide +kernel
  exact h input

lemma cycleControl_legal : Monotone2 (compile 2 cycleControl 4 Fin.val) :=
  compile_monotone2 2 cycleControl 4 Fin.val

lemma cycleControl_count :
    {i : Fin (compile 2 cycleControl 4 Fin.val).gates.length |
      ((compile 2 cycleControl 4 Fin.val).gates[i]).op = GateOp.or}.ncard = 2 :=
  compile_or_ncard_getElem 2 cycleControl 4 Fin.val

end PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler
