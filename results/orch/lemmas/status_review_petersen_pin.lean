import Lean
namespace PEqualNP.Outside.L_meta_2592_aux.PetersenPin
abbrev Mask := BitVec 10
def coreEdges : List Mask := [6, 12, 24, 66, 132, 264, 528, 160, 640, 576, 320, 288]
def neighborBits : List Mask := [2, 16, 32]
def minimalSupports : List Mask := coreEdges ++ [200, 772]
def independent (m : Mask) : Bool :=
  !(coreEdges.any fun e => (m &&& e) == e)
def extendsToNeighbor (m : Mask) : Bool :=
  neighborBits.any fun n => independent (m ||| n)
def supported (m : Mask) : Bool :=
  minimalSupports.any fun e => (m &&& e) == e

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem support_classification : ∀ m : Mask,
    (!extendsToNeighbor m) = supported m := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem independent_blockers : ∀ m : Mask, independent m = true →
    (!extendsToNeighbor m) = (((m &&& 200) == 200) || ((m &&& 772) == 772)) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem supports_are_minimal : ∀ i j : Fin 14,
    let a := minimalSupports.getD i.val 0
    let b := minimalSupports.getD j.val 0
    (a &&& b) = a → i = j := by
  decide +kernel
end PEqualNP.Outside.L_meta_2592_aux.PetersenPin
