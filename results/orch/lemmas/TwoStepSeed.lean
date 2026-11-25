import NonOrSeed

namespace PEqualNP.Outside.L_meta_2592.FewNot

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pin_proper : ∀ i : Fin 10, Extended.proper (pin i) := by
  unfold Extended.proper
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma raw_or_fresh : ∀ i j : Fin 10, i ≠ j →
    Extended.bin 1 (pin i) (pin j) ∉ Extended.pins := by decide +kernel

lemma independent_nonOr_second {d : Nat}
    (allowed : Extended.allowed true d) (nonOr : d ≠ 1)
    (i j : Fin 10) (hij : i ≠ j) (a b : Extended.Sig)
    (ha : a ∈ Extended.pins) (hb : b ∈ Extended.pins) (hab : a ≠ b)
    {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ∨
      v = Extended.bin 1 (pin i) (pin j) ∨ v = Extended.bin d a b) : 16 ≤ k := by
  classical
  let first := Extended.bin 1 (pin i) (pin j)
  by_cases hm : first ∈ S
  · let U := S.erase first
    have fresh : first ∉ insert (pin i) (insert (pin j) U) := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · apply raw_or_fresh i j hij
        change first ∈ Extended.pins
        rw [h]
        exact pin_mem i
      rcases Finset.mem_insert.mp h with h | h
      · apply raw_or_fresh i j hij
        change first ∈ Extended.pins
        rw [h]
        exact pin_mem j
      · exact (Finset.mem_erase.mp h).1 rfl
    have eqS : insert first U = S := Finset.insert_erase hm
    have distinct : pin i ≠ pin j := by
      intro h
      have hfirst : first = pin i := by
        change pin i ||| pin j = pin i
        rw [h]
        simp
      apply raw_or_fresh i j hij
      change first ∈ Extended.pins
      rw [hfirst]
      exact pin_mem i
    have before : Extended.Live true Extended.target (k+1) (insert (pin i) (insert (pin j) U)) :=
      Extended.Live.binary (Or.inl (by decide)) (pin_proper i) (pin_proper j)
        distinct fresh (eqS.symm ▸ run)
    have bound := pair_seventeen allowed nonOr ha hb hab before (fun v hv => ?_)
    · omega
    · rcases Finset.mem_insert.mp hv with hv | hv
      · exact Or.inl (hv ▸ pin_mem i)
      rcases Finset.mem_insert.mp hv with hv | hv
      · exact Or.inl (hv ▸ pin_mem j)
      have hs : v ∈ S := Finset.mem_of_mem_erase hv
      rcases raw v hs with hp | ho | hb
      · exact Or.inl hp
      · exact False.elim ((Finset.mem_erase.mp hv).1 ho)
      · exact Or.inr hb
  · have bound := pair_seventeen allowed nonOr ha hb hab run (fun v hv => ?_)
    · omega
    · rcases raw v hv with hp | ho | hb
      · exact Or.inl hp
      · exfalso
        apply hm
        change Extended.bin 1 (pin i) (pin j) ∈ S
        rwa [← ho]
      · exact Or.inr hb

end PEqualNP.Outside.L_meta_2592.FewNot
