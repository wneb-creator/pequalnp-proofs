import GeneralReaderStandalone
import RelaxedFacts
import StrongRelaxOrSafety
import PEqualNP.MetaComplexity.Helpers.PermInputs

namespace PEqualNP.Outside.L_meta_1884.RelaxationSemantics

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open StrongRelaxRows

def pins : Fin 9 → Fin 9 := ![4, 0, 1, 6, 7, 3, 5, 2, 8]

set_option maxRecDepth 10000 in
lemma target_permuted : ∀ x : Fin 9 → Bool,
    target (x ∘ pins) = GeneralReaderCertificate.edge x := by decide

theorem target_floor (D : Circuit) (hD : FanInTwo D)
    (hf : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = target x) : 16 ≤ D.size := by
  obtain ⟨C, hC, hs, hfC⟩ := Helpers.PermInputs.relabel_size pins target D.size
    ⟨D, hD, le_rfl, hf⟩
  have hc := NineGeneralFloor.nine_circuit_floor C hC (fun x => (hfC x).trans (target_permuted x))
  exact Nat.le_trans hc hs

lemma exceptional_eq : StrongRelaxOrSafety.exceptional = row 277 := by decide

theorem exceptional_accepted (D : Circuit) (hM : Monotone2 D) (hs : D.size ≤ 13)
    (hp : ∀ m ∈ positives, circuitFun 9 D (row m) = true)
    (hn : ∀ m ∈ negatives, circuitFun 9 D (row m) = false) :
    circuitFun 9 D StrongRelaxOrSafety.exceptional = true := by
  rw [exceptional_eq]
  cases he : circuitFun 9 D (row 277)
  · have hf := exact_if_exception_rejected (circuitFun 9 D)
      (ClosedOrSafety.output_mono 9 D hM) hp hn he
    have hlegal : FanInTwo D := by
      intro g hg
      have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hM g hg).1
      refine ⟨?_, (hM g hg).2⟩
      rcases hop with h | h <;> simp [h]
    have hfloor := target_floor D hlegal hf
    omega
  · rfl

end PEqualNP.Outside.L_meta_1884.RelaxationSemantics
