import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux.PetersenBoundary

def edgeFunction (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def maskInput (r : Nat) (i : Fin 10) : Bool := r.testBit i.val

def maximalFalseMasks : List Nat :=
  [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]

def support (r : Nat) : Finset (Fin 10) :=
  Finset.univ.filter (fun i => maskInput r i = true)

theorem maximalFalseMasks_length : maximalFalseMasks.length = 15 := rfl

theorem maximalFalseMasks_nodup : maximalFalseMasks.Nodup := by decide +kernel

theorem listed_masks_false :
    ∀ r ∈ maximalFalseMasks, edgeFunction (maskInput r) = false := by
  decide +kernel

theorem listed_masks_maximal :
    ∀ r ∈ maximalFalseMasks, ∀ i : Fin 10, maskInput r i = false →
      edgeFunction (fun j => if j = i then true else maskInput r j) = true := by
  decide +kernel

theorem distinct_listed_union_true :
    ∀ r ∈ maximalFalseMasks, ∀ s ∈ maximalFalseMasks, r ≠ s →
      edgeFunction (fun i => maskInput r i || maskInput s i) = true := by
  decide +kernel

theorem listed_masks_sizes :
    ∀ r ∈ maximalFalseMasks, (support r).card = 3 ∨ (support r).card = 4 := by
  decide +kernel

theorem three_vertex_mask_count :
    (maximalFalseMasks.filter (fun r => decide ((support r).card = 3))).length = 10 := by
  decide +kernel

theorem four_vertex_mask_count :
    (maximalFalseMasks.filter (fun r => decide ((support r).card = 4))).length = 5 := by
  decide +kernel

theorem complement_sizes :
    ∀ r ∈ maximalFalseMasks, (support r)ᶜ.card = 6 ∨ (support r)ᶜ.card = 7 := by
  decide +kernel

theorem seven_vertex_complement :
    50 ∈ maximalFalseMasks ∧ (support 50)ᶜ.card = 7 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem false_boundary_complete :
    ∀ x : Fin 10 → Bool, edgeFunction x = false →
      ∃ r ∈ maximalFalseMasks, ∀ i : Fin 10, x i = true → maskInput r i = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_2590_aux.PetersenBoundary
