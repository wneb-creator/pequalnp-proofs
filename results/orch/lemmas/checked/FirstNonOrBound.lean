import Bound17
namespace PEqualNP.Outside.L_meta_2592.Projection

lemma initial_nonOr_bound {k d : Nat} {U : Finset Extended.Sig} {a b : Extended.Sig}
    (hd : Extended.allowed true d) (notOr : d ≠ 1)
    (ha : a ∈ Extended.initial) (hb : b ∈ Extended.initial) (hab : a ≠ b)
    (fresh : Extended.bin d a b ∉ insert a (insert b U))
    (raw : ∀ c ∈ U, c ∈ Extended.initial)
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d a b) U)) :
    18 ≤ k + 1 := by
  have retained := Extended.initial_retained hd ha hb hab raw tail
  obtain ⟨i, rfl⟩ := initial_pin ha
  obtain ⟨j, rfl⟩ := initial_pin hb
  have leftFresh : Extended.bin d (pin i) (pin j) ∉ insert (pin i) U := by
    intro h
    apply fresh
    rcases Finset.mem_insert.mp h with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
  rcases Extended.allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · have bound := tail_bound_two_constants (Or.inl rfl) retained.1 leftFresh raw tail
    omega
  · exact (notOr rfl).elim
  · have bound := tail_bound_two_constants (Or.inr rfl) retained.1 leftFresh raw tail
    omega
  · have same : Extended.bin 3 (pin i) (pin j) = Extended.bin 2 (pin j) (pin i) := by
      simp [Extended.bin, BitVec.and_comm]
    rw [same] at fresh tail
    have rightFresh : Extended.bin 2 (pin j) (pin i) ∉ insert (pin j) U := by
      intro h
      exact fresh (Finset.mem_insert_of_mem h)
    have bound := tail_bound_two_constants (Or.inr rfl) retained.2 rightFresh raw tail
    omega
end PEqualNP.Outside.L_meta_2592.Projection
