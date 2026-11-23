import Mathlib

namespace PEqualNP.Outside.L_meta_951.CanonicalCut

theorem canonical_code_injective
    {Input Output Code Selector : Type*}
    [Preorder Input] [PartialOrder Output] [LinearOrder Selector]
    (F : Input → Output) (M : Output → Input) (hM : Monotone M)
    (hsection : ∀ y ∈ Set.range F, F (M y) = y)
    (z : Input → Selector) (hz : Antitone z)
    (code : Input → Code) (decode : Code → Selector → Output)
    (hdecode : ∀ c, Monotone (decode c))
    (hcompute : ∀ x, F x = decode (code x) (z x)) :
    Function.Injective (fun y : Set.range F => code (M y.val)) := by
  intro v w hcode
  change code (M v.val) = code (M w.val) at hcode
  have hv : v.val = decode (code (M v.val)) (z (M v.val)) := by
    exact (hsection v.val v.property).symm.trans (hcompute _)
  have hw : w.val = decode (code (M w.val)) (z (M w.val)) := by
    exact (hsection w.val w.property).symm.trans (hcompute _)
  apply Subtype.ext
  rcases le_total (z (M v.val)) (z (M w.val)) with h | h
  · have hvw : v.val ≤ w.val := by
      rw [hv, hw, hcode]
      exact hdecode _ h
    have heq : z (M v.val) = z (M w.val) :=
      le_antisymm h (hz (hM hvw))
    rw [hv, hw, hcode, heq]
  · have hwv : w.val ≤ v.val := by
      rw [hv, hw, hcode]
      exact hdecode _ h
    have heq : z (M v.val) = z (M w.val) :=
      le_antisymm (hz (hM hwv)) h
    rw [hv, hw, hcode, heq]

theorem range_card_le_code_card
    {Input Output Code Selector : Type*}
    [Preorder Input] [PartialOrder Output] [LinearOrder Selector]
    (F : Input → Output) [Fintype (Set.range F)] [Fintype Code]
    (M : Output → Input) (hM : Monotone M)
    (hsection : ∀ y ∈ Set.range F, F (M y) = y)
    (z : Input → Selector) (hz : Antitone z)
    (code : Input → Code) (decode : Code → Selector → Output)
    (hdecode : ∀ c, Monotone (decode c))
    (hcompute : ∀ x, F x = decode (code x) (z x)) :
    Fintype.card (Set.range F) ≤ Fintype.card Code := by
  exact Fintype.card_le_of_injective _
    (canonical_code_injective F M hM hsection z hz code decode hdecode hcompute)

end PEqualNP.Outside.L_meta_951.CanonicalCut
