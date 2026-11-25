import PEqualNP.Outside.L_meta_2592
namespace PEqualNP.Outside.L_meta_2592.Signed

lemma or_then_positive_and_floor {a b c : Extended.Sig} (aPin : a ∈ Extended.pins)
    (bPin : b ∈ Extended.pins) (cPin : c ∈ Extended.pins) (d : Nat) (hd : d = 0 ∨ d = 2)
    {k : Nat} {S : Finset Extended.Sig}
    (kept : Extended.bin d a c ∈ S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ∨ v = Extended.bin 1 a b ∨
      v = Extended.bin d a c)
    (run : Extended.Live true Extended.target k S) : 16 ≤ k := by
  obtain ⟨rows, fixed, same, supplied⟩ := pin_projection_false a aPin
  have gateZero : restrictRows rows (Extended.observe (Extended.bin d a c)) =
      (fun _ => false) := by
    rw [Extended.obs_bin, restrict_comb, fixed]
    rcases hd with rfl | rfl <;> funext r <;> simp [comb, combine]
  apply live_one_constant_bound run rows same kept ⟨false, gateZero⟩
  intro v hv
  rcases raw v hv with ordinary | rfl | rfl
  · exact supplied v ordinary
  · rw [Extended.obs_bin, restrict_comb, fixed]
    simpa [comb, combine] using supplied b bPin
  · exact Or.inr (Or.inl ⟨false, gateZero⟩)

lemma or_then_opposite_and_floor {a b c : Extended.Sig} (aPin : a ∈ Extended.pins)
    (bPin : b ∈ Extended.pins) (cPin : c ∈ Extended.pins)
    {k : Nat} {S : Finset Extended.Sig}
    (kept : Extended.bin 3 c a ∈ S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ∨ v = Extended.bin 1 a b ∨
      v = Extended.bin 3 c a)
    (run : Extended.Live true Extended.target k S) : 16 ≤ k := by
  obtain ⟨rows, fixed, same, supplied⟩ := pin_projection_false a aPin
  have gateZero : restrictRows rows (Extended.observe (Extended.bin 3 c a)) =
      (fun _ => false) := by
    rw [Extended.obs_bin, restrict_comb, fixed]
    funext r
    simp [comb, combine]
  apply live_one_constant_bound run rows same kept ⟨false, gateZero⟩
  intro v hv
  rcases raw v hv with ordinary | rfl | rfl
  · exact supplied v ordinary
  · rw [Extended.obs_bin, restrict_comb, fixed]
    simpa [comb, combine] using supplied b bPin
  · exact Or.inr (Or.inl ⟨false, gateZero⟩)

end PEqualNP.Outside.L_meta_2592.Signed
