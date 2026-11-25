import NonOrSeed

namespace PEqualNP.Outside.L_meta_2592.FewNot.Extended

lemma pin_zero_bit {a : Sig} (ha : a ∈ pins) : bit 0 a = false := by
  have all : pins.all (fun v => !(bit 0 v)) = true := by decide +kernel
  simpa using List.all_eq_true.mp all a ha

lemma negative_or_assoc (a b c : Sig) :
    bin 2 (bin 2 c a) b = bin 2 c (bin 1 a b) := by
  apply bit_ext
  intro r
  simp only [bit_bin]
  cases bit r a <;> cases bit r b <;> cases bit r c <;> decide

lemma negative_or_cube_floor {a b c : Sig}
    (ha : a ∈ pins) (hb : b ∈ pins) (hc : c ∈ pins) (hne : c ≠ a)
    {k : Nat} {S : Finset Sig} (run : Live true target k S)
    (raw : ∀ v ∈ S, v ∈ pins ∨ v = bin 2 c (bin 1 a b)) : 16 ≤ k := by
  let p := bin 2 c a
  let z := bin 2 c (bin 1 a b)
  let roots := pins ++ [p]
  have hp0 : bit 0 p = false := by
    change bit 0 (bin 2 c a) = false
    rw [bit_bin]
    simp [pin_zero_bit hc,pin_zero_bit ha]
  have hb0 : bit 0 b = false := pin_zero_bit hb
  have hp1 : p ≠ one := by
    intro h
    rw [h,bit_one] at hp0
    cases hp0
  have hb1 : b ≠ one := by
    intro h
    rw [h,bit_one] at hb0
    cases hb0
  have rep := bin_rep (u := true) (w := roots) 2 (Or.inr ⟨rfl,by decide⟩)
    (Or.inl (show p ∈ roots by simp [roots]))
    (Or.inl (show b ∈ roots by simp [roots,hb])) (fun _ => ⟨hp1,hb1⟩)
  have eq : bin 2 p b = z := negative_or_assoc a b c
  rw [eq] at rep
  obtain ⟨n,T,hn,tail,hT⟩ := pull_gate (c := 1) run
    (rep.imp id (fun h => ⟨rfl,h⟩)) (by
      intro v hv
      rcases raw v hv with hp | hz
      · simp [roots,hp]
      · simp [z,hz])
  have floor := PEqualNP.Outside.L_meta_2592.FewNot.pair_seventeen
    (Or.inr ⟨rfl,by decide⟩ : allowed true 2) (by decide : (2 : Nat) ≠ 1)
    hc ha hne tail (by
      intro v hv
      simpa [roots,p] using hT v hv)
  omega

end PEqualNP.Outside.L_meta_2592.FewNot.Extended
