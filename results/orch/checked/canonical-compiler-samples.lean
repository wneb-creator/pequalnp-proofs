import CanonicalCompilerSemantics
import CanonicalCompilerMasks

namespace PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma compile_samples {n m : Nat} (k : Nat) (program : Program n k)
    (truthMask : Nat) (inputMasks : Fin n → Nat) (certificates : List Nat) (result : Nat)
    (samples : Fin m → Fin n → Bool)
    (htruth : ∀ r : Fin m, truthMask.testBit r.val = true)
    (hinputs : ∀ r : Fin m, ∀ i : Fin n, (inputMasks i).testBit r.val = samples r i)
    (hcheck : checkMasks k program truthMask inputMasks certificates result = true) :
    ∀ r : Fin m, circuitFun n (compile k program n Fin.val) (samples r) =
      result.testBit r.val := by
  intro r
  have hmask := checkMasks_sound k program truthMask inputMasks certificates result hcheck
  have hbit := congrArg (fun mask : Nat => mask.testBit r.val) hmask
  rw [evaluateMasks_testBit k program truthMask inputMasks r.val (htruth r)] at hbit
  have henv : (fun i => (inputMasks i).testBit r.val) = samples r := by
    funext i
    exact hinputs r i
  rw [henv] at hbit
  exact (compile_circuitFun k program (samples r)).trans hbit

end PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler
