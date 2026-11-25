import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1479.K4Equality

open Finset

lemma certificate_input_card_le (n root : Nat) (I J O W : Finset Nat)
    (source : Nat × Bool → Nat)
    (hIrange : I ⊆ range n) (hIW : I ⊆ W)
    (hJW : ∀ j ∈ J, n + j ∈ W)
    (hcover : W ⊆ insert root
      (((J ×ˢ ({false} : Finset Bool)) ∪ (O ×ˢ ({true} : Finset Bool))).image source)) :
    I.card ≤ O.card + 1 := by
  let K := J.image (fun j => n + j)
  have hKcard : K.card = J.card := by
    apply card_image_of_injective
    intro a b hab
    exact Nat.add_left_cancel hab
  have hKW : K ⊆ W := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hw
    exact hJW j hj
  have hdisj : Disjoint I K := by
    apply disjoint_left.mpr
    intro w hwI hwK
    have hwlt := mem_range.mp (hIrange hwI)
    obtain ⟨j, hj, hje⟩ := mem_image.mp hwK
    omega
  have hlower : I.card + J.card ≤ W.card := by
    rw [← hKcard, ← card_union_of_disjoint hdisj]
    exact card_le_card (union_subset hIW hKW)
  have hupper : W.card ≤ J.card + O.card + 1 := by
    calc
      W.card ≤ (insert root
          (((J ×ˢ ({false} : Finset Bool)) ∪
            (O ×ˢ ({true} : Finset Bool))).image source)).card := card_le_card hcover
      _ ≤ (((J ×ˢ ({false} : Finset Bool)) ∪
            (O ×ˢ ({true} : Finset Bool))).image source).card + 1 := card_insert_le _ _
      _ ≤ ((J ×ˢ ({false} : Finset Bool)) ∪
            (O ×ˢ ({true} : Finset Bool))).card + 1 :=
        Nat.add_le_add_right (card_image_le) 1
      _ ≤ (J ×ˢ ({false} : Finset Bool)).card +
            (O ×ˢ ({true} : Finset Bool)).card + 1 :=
        Nat.add_le_add_right (card_union_le _ _) 1
      _ = J.card + O.card + 1 := by simp
  omega

end PEqualNP.Outside.L_meta_1479.K4Equality
