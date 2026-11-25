import SeventeenCoreDev

namespace PEqualNP.Outside.L_meta_2592_aux.Seventeen

lemma after_first_nonOr_bound (floorNine : Lower true inputs graph 15)
    {k : Nat} {U : Finset Extended.Sig} {a b : Extended.Sig} {d : Nat}
    (hd : Extended.allowed true d) (hab : a ≠ b) (hop : d ≠ 1)
    (fresh : Extended.bin d a b ∉ insert a (insert b U))
    (raw : ∀ v ∈ insert a (insert b U), v ∈ Extended.pins)
    (run : Extended.Live true Extended.target k (insert (Extended.bin d a b) U)) : 17 ≤ k := by
  rcases Extended.allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
  · exact after_first_and_bound floorNine hd hab (Or.inl rfl) fresh raw run
  · exact False.elim (hop rfl)
  · exact after_first_and_bound floorNine hd hab (Or.inr rfl) fresh raw run
  · have swap : Extended.bin 3 a b = Extended.bin 2 b a := by
      simp [Extended.bin,BitVec.and_comm]
    have raw' : ∀ v ∈ insert b (insert a U), v ∈ Extended.pins := by
      intro v hv
      exact raw v (by simpa only [Finset.insert_comm] using hv)
    have fresh' : Extended.bin 2 b a ∉ insert b (insert a U) := by
      rw [←swap]
      simpa only [Finset.insert_comm] using fresh
    rw [swap] at run
    exact after_first_and_bound floorNine (by simp [Extended.allowed]) hab.symm
      (Or.inr rfl) fresh' raw' run

end PEqualNP.Outside.L_meta_2592_aux.Seventeen
