import DynamicClosedTest
namespace PEqualNP.Outside.L_meta_670_aux.DynamicLeaf
open LiveCheck PEqualNP.CircuitLowerBounds
def calibrationState : List Sig := [raw5,raw6,raw7,raw8,neg raw0,neg raw1,neg raw2,neg raw3,neg raw4]
def calibrationPrograms (i : Fin 3) : List Gate × List Nat :=
  match i.val with
  | 0 => ([⟨.not,[0]⟩,⟨.not,[1]⟩,⟨.not,[2]⟩,⟨.not,[3]⟩],[4,5,6,7,10,11,12,13,9])
  | 1 => ([⟨.not,[1]⟩,⟨.not,[0]⟩,⟨.not,[4]⟩,⟨.not,[7]⟩,⟨.not,[5]⟩],[2,8,6,3,10,11,12,13,14])
  | _ => ([⟨.not,[2]⟩,⟨.not,[1]⟩,⟨.not,[0]⟩,⟨.not,[4]⟩,⟨.not,[6]⟩],[3,5,8,7,10,11,12,13,14])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma calibration_checked :
    leafCheck originalOracle 10 2 calibrationState calibrationPrograms = true := by decide +kernel
lemma calibration_excluded
    (hbase : ∀ m ≤ 12, ∀ u, ¬ Base1007.Live m u Base1007.raw.toFinset) :
    Impossible 10 2 calibrationState :=
  leafCheck_sound originalOracle (originalOracle_sound hbase) calibration_checked
end PEqualNP.Outside.L_meta_670_aux.DynamicLeaf
