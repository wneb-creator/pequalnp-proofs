namespace PEqualNP.Outside.L_meta_2592.Signed

lemma central_or_floor (i : Fin 10) (leaves : List (Fin 10))
    {k : Nat} {S : Finset Extended.Sig}
    (retained : Extended.pins.getD i.val Extended.zero ∈ S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ∨ ∃ w ∈ leaves,
      v = Extended.bin 1 (Extended.pins.getD i.val Extended.zero)
        (Extended.pins.getD w.val Extended.zero))
    (run : Extended.Live true Extended.target k S) : 16 ≤ k := by
  obtain ⟨rows, fixed, goal, supplied⟩ := pin_projection_false
    (Extended.pins.getD i.val Extended.zero) ((Extended.pin_mem _).mpr ⟨i, rfl⟩)
  apply live_one_constant_bound run rows goal retained ⟨false, fixed⟩
  intro v hv
  rcases raw v hv with ordinary | ⟨w, hw, rfl⟩
  · exact supplied v ordinary
  · rw [Extended.obs_bin, restrict_comb, fixed]
    simpa [comb, combine] using supplied
      (Extended.pins.getD w.val Extended.zero) ((Extended.pin_mem _).mpr ⟨w, rfl⟩)

lemma triple_or_floor (i j c d : Fin 10) (nd : ([i,j,c,d] : List (Fin 10)).Nodup)
    (jc : Extended.petAdjacent j c = false) (jd : Extended.petAdjacent j d = false)
    (cd : Extended.petAdjacent c d = false)
    (neighbor : Extended.petAdjacent i j = true ∨ Extended.petAdjacent i c = true ∨
      Extended.petAdjacent i d = true) {k : Nat} {S : Finset Extended.Sig}
    (raw : ∀ v ∈ S, v ∈ Extended.pins ∨ ∃ w ∈ [j,c,d],
      v = Extended.bin 1 (Extended.pins.getD i.val Extended.zero)
        (Extended.pins.getD w.val Extended.zero))
    (run : Extended.Live true Extended.target k S) : 16 ≤ k :=
  central_or_floor i [j,c,d]
    (Extended.triple_ors_keep_input i j c d nd jc jd cd neighbor raw run) raw run

end PEqualNP.Outside.L_meta_2592.Signed
