import PEqualNP.Defs
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

lemma supported_of_monotone_pin (A : Mask → Bool)
    (hUp : ∀ m n, A m = true → A (m ||| n) = true)
    (hPin : ∀ m n, n ∈ neighborBits → independent (m ||| n) = true →
      A (m ||| n) = false) :
    ∀ m, A m = true → supported m = true := by
  intro m hm
  cases hExt : extendsToNeighbor m with
  | false =>
    have h := support_classification m
    rw [hExt] at h
    exact h.symm
  | true =>
    obtain ⟨n, hn, hi⟩ := List.any_eq_true.mp hExt
    have hTrue := hUp m n hm
    have hFalse := hPin m n hn hi
    rw [hFalse] at hTrue
    cases hTrue

def asInput (m : Mask) : Fin 10 → Bool := fun i => m.getLsbD i.val

lemma asInput_le_extend (m n : Mask) : asInput m ≤ asInput (m ||| n) := by
  intro i
  simp only [asInput, BitVec.getLsbD_or]
  cases m.getLsbD i.val <;> cases n.getLsbD i.val <;> decide

lemma supported_of_monotone_function (A : (Fin 10 → Bool) → Bool)
    (hA : Monotone A)
    (hPin : ∀ m n, n ∈ neighborBits → independent (m ||| n) = true →
      A (asInput (m ||| n)) = false) :
    ∀ m, A (asInput m) = true → supported m = true := by
  apply supported_of_monotone_pin (fun m => A (asInput m)) ?_ hPin
  intro m n hm
  have h := hA (asInput_le_extend m n)
  rw [hm] at h
  exact le_antisymm (by cases A (asInput (m ||| n)) <;> decide) h

end PEqualNP.Outside.L_meta_2592_aux.PetersenPin
