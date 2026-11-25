import Mono18RectangleSamples

namespace PEqualNP.Outside.L_meta_2373.Mono18Rectangle

open Live1024

def sampleLabels (m : Nat) : Bool :=
  (List.range (rowCount (matrixWeight m))).all (fun r => bit (positiveSample m r) graph) &&
  (List.range (colCount (matrixWeight m))).all (fun c => !bit (negativeSample m c) graph)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma sampleLabels_valid : ∀ m : Fin 39, sampleLabels m.val = true := by
  intro m; fin_cases m <;> decide +kernel

lemma sample_positive (m : Fin 39) (r : Fin (rowCount (matrixWeight m.val))) :
    bit (positiveSample m.val r.val) graph = true := by
  have checked := sampleLabels_valid m
  simp only [sampleLabels, Bool.and_eq_true] at checked
  exact List.all_eq_true.mp checked.1 r.val (List.mem_range.mpr r.isLt)

lemma sample_negative (m : Fin 39) (c : Fin (colCount (matrixWeight m.val))) :
    bit (negativeSample m.val c.val) graph = false := by
  have checked := sampleLabels_valid m
  simp only [sampleLabels, Bool.and_eq_true] at checked
  have h := List.all_eq_true.mp checked.2 c.val (List.mem_range.mpr c.isLt)
  cases hv : bit (negativeSample m.val c.val) graph <;> simp_all

end PEqualNP.Outside.L_meta_2373.Mono18Rectangle
