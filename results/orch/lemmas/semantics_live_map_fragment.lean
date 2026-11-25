lemma map_live {u : Bool} {T : Extended.Sig} {k : ℕ} {S : Finset Extended.Sig}
    (h : Extended.Live u T k S) (φ : Extended.Sig → Extended.Sig)
    (hinj : Function.Injective φ) (hz : φ Extended.zero = Extended.zero)
    (ho : φ Extended.one = Extended.one)
    (hbin : ∀ d a b, φ (Extended.bin d a b) = Extended.bin d (φ a) (φ b)) :
    Extended.Live u (φ T) k (S.image φ) := by
  have hproper : ∀ a, Extended.proper a → Extended.proper (φ a) := by
    intro a ha
    constructor
    · intro he
      exact ha.1 (hinj (he.trans hz.symm))
    · intro he
      exact ha.2 (hinj (he.trans ho.symm))
  induction h using Extended.Live.ind with
  | stop hp =>
      simpa only [Finset.image_singleton] using Extended.Live.stop (u := u) (hproper T hp)
  | @binary k U a b d hd ha hb hab hf tail ih =>
      simp only [Finset.image_insert]
      apply Extended.Live.binary hd (hproper a ha) (hproper b hb)
        (fun he => hab (hinj he))
      · intro he
        have hm : φ (Extended.bin d a b) ∈
            (insert a (insert b U)).image φ := by
          simpa only [Finset.image_insert, hbin] using he
        obtain ⟨v, hv, hvEq⟩ := Finset.mem_image.mp hm
        exact hf (hinj hvEq ▸ hv)
      · simpa only [Finset.image_insert, hbin] using ih
