import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.FanoFinite

def fanoPairs : List (Nat × Nat) :=
  [(1,0), (3,0), (5,0), (0,1), (3,1), (4,1), (2,2), (3,2), (6,2),
   (0,3), (1,3), (2,3), (1,4), (4,4), (6,4), (0,5), (5,5), (6,5),
   (2,6), (4,6), (5,6)]

def fanoInc (p l : Fin 7) : Prop := (p.val, l.val) ∈ fanoPairs

instance fanoIncDecidable : DecidableRel fanoInc := fun p l =>
  inferInstanceAs (Decidable ((p.val, l.val) ∈ fanoPairs))

theorem fano_line_size :
    ∀ l : Fin 7, (Finset.univ.filter (fun p => fanoInc p l)).card = 3 := by
  decide +kernel

theorem fano_point_pair :
    ∀ p p' : Fin 7, p ≠ p' → ∃! l : Fin 7, fanoInc p l ∧ fanoInc p' l := by
  unfold ExistsUnique
  decide +kernel

def fanoFunction (z : Fin 14 → Bool) : Bool :=
  decide (∃ p l : Fin 7, fanoInc p l ∧ z (Fin.castAdd 7 p) = true ∧
    z (Fin.natAdd 7 l) = true)

def maskInput (r : Nat) (i : Fin 14) : Bool := r.testBit i.val

def maximalFalseMasks : List Nat :=
  [127, 213, 358, 452, 563, 657, 802, 1144, 1232, 1376, 1584, 2093,
   2181, 2340, 2593, 3112, 3872, 4126, 4244, 4358, 4626, 5144, 5776,
   6156, 6532, 8267, 8385, 8514, 8707, 9288, 9664, 10249, 10881,
   12298, 13058, 15368, 16256]

theorem maximalFalseMasks_length : maximalFalseMasks.length = 37 := rfl

theorem listed_masks_false :
    ∀ r ∈ maximalFalseMasks, fanoFunction (maskInput r) = false := by
  decide +kernel

theorem listed_masks_maximal :
    ∀ r ∈ maximalFalseMasks, ∀ i : Fin 14, maskInput r i = false →
      fanoFunction (fun j => if j = i then true else maskInput r j) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem point_boundary_cover :
    ∀ x : Fin 7 → Bool, ∃ m ∈ maximalFalseMasks,
      (∀ p : Fin 7, x p = true → maskInput m (Fin.castAdd 7 p) = true) ∧
      (∀ l : Fin 7, (∀ p : Fin 7, fanoInc p l → x p = false) →
        maskInput m (Fin.natAdd 7 l) = true) := by
  decide +kernel

theorem false_boundary_complete (z : Fin 14 → Bool)
    (hz : fanoFunction z = false) :
    ∃ m ∈ maximalFalseMasks, ∀ i : Fin 14,
      z i = true → maskInput m i = true := by
  obtain ⟨m, hm, hp, hl⟩ := point_boundary_cover (fun p => z (Fin.castAdd 7 p))
  refine ⟨m, hm, ?_⟩
  intro i
  refine Fin.addCases (m := 7) (n := 7)
    (motive := fun i => z i = true → maskInput m i = true) ?_ ?_ i
  · exact hp
  · intro l hzline
    apply hl l
    intro p hinc
    cases hpoint : z (Fin.castAdd 7 p) with
    | false => rfl
    | true =>
      have ht : fanoFunction z = true := by
        unfold fanoFunction
        simp only [decide_eq_true_eq]
        exact ⟨p, l, hinc, hpoint, hzline⟩
      rw [hz] at ht
      contradiction

def edgeInput (p l : Fin 7) (i : Fin 14) : Bool :=
  decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)

theorem edgeInput_true (p l : Fin 7) (hinc : fanoInc p l) :
    fanoFunction (edgeInput p l) = true := by
  unfold fanoFunction
  simp only [decide_eq_true_eq]
  refine ⟨p, l, hinc, ?_, ?_⟩ <;> simp [edgeInput]

theorem true_boundary_complete (z : Fin 14 → Bool)
    (hz : fanoFunction z = true) :
    ∃ p l : Fin 7, fanoInc p l ∧
      ∀ i : Fin 14, edgeInput p l i = true → z i = true := by
  unfold fanoFunction at hz
  simp only [decide_eq_true_eq] at hz
  obtain ⟨p, l, hinc, hp, hl⟩ := hz
  refine ⟨p, l, hinc, ?_⟩
  intro i hi
  simp only [edgeInput, decide_eq_true_eq] at hi
  rcases hi with rfl | rfl
  · exact hp
  · exact hl

end PEqualNP.Outside.L_meta_2583_aux.FanoFinite
