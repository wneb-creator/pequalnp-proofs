import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2089

def nfInc (p l : Fin 13) : Prop :=
  ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma nf_common_lines : ∀ p q l m : Fin 13,
    p ≠ q → nfInc p l → nfInc q l → nfInc p m → nfInc q m → l = m := by
  unfold nfInc
  decide +kernel

lemma nf_rectangle (A B : Finset (Fin 13))
    (h : ∀ p ∈ A, ∀ l ∈ B, nfInc p l) : A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_cases hA : A.card ≤ 1
  · exact Or.inl hA
  · right
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    apply Finset.card_le_one.mpr
    intro l hl m hm
    exact nf_common_lines p q l m hpq (h p hp l hl) (h q hq l hl)
      (h p hp m hm) (h q hq m hm)

end PEqualNP.Outside.L_meta_2089
