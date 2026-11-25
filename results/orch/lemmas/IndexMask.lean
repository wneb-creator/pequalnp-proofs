import PEqualNP.Outside.L_meta_10760
namespace PEqualNP.Outside.L_meta_10760
noncomputable def indexMask (xs : List Nat) : Nat :=
  bitsOf (xs.map fun i => (0, i))

lemma indexMask_mem {xs : List Nat} {i : Nat}
    (h : (indexMask xs).testBit i = true) : i ∈ xs := by
  obtain ⟨s, hs, he⟩ := bitsOf_bit h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hs
  change j = i at he
  exact he ▸ hj

lemma mem_of_indexMask {xs : List Nat} {n i : Nat}
    (h : indexMask xs = 2 ^ n - 1) (hi : i < n) : i ∈ xs := by
  apply indexMask_mem
  rw [h, Nat.testBit_two_pow_sub_one]
  simp only [hi, decide_true]

end PEqualNP.Outside.L_meta_10760
