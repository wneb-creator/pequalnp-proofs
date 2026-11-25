import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.LeafCount

lemma count_sum_le (S : Finset Nat) (L : List Nat) :
    (∑ i ∈ S, L.count i) ≤ L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases ha : a ∈ S
    · simpa [List.count_cons, Finset.sum_add_distrib, ha] using
        Nat.add_le_add_right ih 1
    · simpa [List.count_cons, Finset.sum_add_distrib, ha] using
        Nat.le_succ_of_le ih

end PEqualNP.Outside.L_meta_2592_aux.LeafCount
