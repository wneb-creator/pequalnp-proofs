namespace PEqualNP.Outside.L_meta_2592.Signed

lemma or_and_retained_floor (i j c : Fin 10) (ic : i ≠ c)
    {k : Nat} {S : Finset Extended.Sig}
    (retained : Extended.pins.getD i.val Extended.zero ∈ S)
    (kept : Extended.bin 0 (Extended.pins.getD i.val Extended.zero)
      (Extended.pins.getD c.val Extended.zero) ∈ S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ∨
      v = Extended.bin 1 (Extended.pins.getD i.val Extended.zero)
        (Extended.pins.getD j.val Extended.zero) ∨
      v = Extended.bin 0 (Extended.pins.getD i.val Extended.zero)
        (Extended.pins.getD c.val Extended.zero))
    (run : Extended.Live true Extended.target k S) : 17 ≤ k := by
  let a := Extended.pins.getD i.val Extended.zero
  let b := Extended.pins.getD j.val Extended.zero
  let cPin := Extended.pins.getD c.val Extended.zero
  have aMem : a ∈ Extended.pins := (Extended.pin_mem _).mpr ⟨i, rfl⟩
  have bMem : b ∈ Extended.pins := (Extended.pin_mem _).mpr ⟨j, rfl⟩
  obtain ⟨rows, fixed, same, supplied⟩ := pin_projection_false a aMem
  have gateZero : restrictRows rows (Extended.observe (Extended.bin 0 a cPin)) =
      (fun _ => false) := by
    rw [Extended.obs_bin, restrict_comb, fixed]
    funext r
    simp [comb, combine]
  apply live_two_constants_bound run rows same (Extended.pin_ne_and i c ic)
    retained kept ⟨false, fixed⟩ ⟨false, gateZero⟩
  intro v hv
  rcases raw v hv with ordinary | rfl | rfl
  · exact supplied v ordinary
  · rw [Extended.obs_bin, restrict_comb, fixed]
    simpa [comb, combine, b] using supplied b bMem
  · exact Or.inr (Or.inl ⟨false, gateZero⟩)

lemma or_and_floor (i j c : Fin 10) (ij : i ≠ j) (ic : i ≠ c) (jc : j ≠ c)
    {k : Nat} {S : Finset Extended.Sig}
    (kept : Extended.bin 0 (Extended.pins.getD i.val Extended.zero)
      (Extended.pins.getD c.val Extended.zero) ∈ S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ∨
      v = Extended.bin 1 (Extended.pins.getD i.val Extended.zero)
        (Extended.pins.getD j.val Extended.zero) ∨
      v = Extended.bin 0 (Extended.pins.getD i.val Extended.zero)
        (Extended.pins.getD c.val Extended.zero))
    (run : Extended.Live true Extended.target k S) : 17 ≤ k :=
  or_and_retained_floor i j c ic (Extended.or_and_keep_input i j c ij ic jc raw run)
    kept raw run

lemma pair_or_and_floor (i j : Fin 10) (ij : i ≠ j)
    {k : Nat} {S : Finset Extended.Sig}
    (kept : Extended.bin 0 (Extended.pins.getD i.val Extended.zero)
      (Extended.pins.getD j.val Extended.zero) ∈ S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ∨
      v = Extended.bin 1 (Extended.pins.getD i.val Extended.zero)
        (Extended.pins.getD j.val Extended.zero) ∨
      v = Extended.bin 0 (Extended.pins.getD i.val Extended.zero)
        (Extended.pins.getD j.val Extended.zero))
    (run : Extended.Live true Extended.target k S) : 17 ≤ k := by
  obtain retained | retained := Extended.pair_or_and_keep_input i j ij raw run
  · exact or_and_retained_floor i j j ij retained kept raw run
  · have andSwap : Extended.bin 0 (Extended.pins.getD j.val Extended.zero)
        (Extended.pins.getD i.val Extended.zero) =
        Extended.bin 0 (Extended.pins.getD i.val Extended.zero)
          (Extended.pins.getD j.val Extended.zero) := by
      simp [Extended.bin, BitVec.and_comm]
    have orSwap : Extended.bin 1 (Extended.pins.getD j.val Extended.zero)
        (Extended.pins.getD i.val Extended.zero) =
        Extended.bin 1 (Extended.pins.getD i.val Extended.zero)
          (Extended.pins.getD j.val Extended.zero) := by
      simp [Extended.bin, BitVec.or_comm]
    apply or_and_retained_floor j i i (Ne.symm ij) retained (andSwap.symm ▸ kept) ?_ run
    intro v hv
    simpa only [orSwap, andSwap] using raw v hv

end PEqualNP.Outside.L_meta_2592.Signed
