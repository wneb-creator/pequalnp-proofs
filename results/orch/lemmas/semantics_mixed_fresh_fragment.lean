set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma mixed_signal_fresh : ∀ a b c : Fin 10, a ≠ b → c ≠ a → c ≠ b →
    Extended.bin 1 (inputPin a) (inputPin b) ∉ Extended.initial ∧
    Extended.bin 2 (Extended.bin 1 (inputPin a) (inputPin b)) (inputPin c) ∉ Extended.initial ∧
    Extended.bin 1 (inputPin a) (inputPin b) ≠
      Extended.bin 2 (Extended.bin 1 (inputPin a) (inputPin b)) (inputPin c) := by
  decide +kernel

lemma initial_card_ten : Extended.initial.toFinset.card = 10 := by
  decide +kernel

lemma mixed_roots_card (a b c : Fin 10) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (keep : Bool) :
    (insert (Extended.bin 2 (Extended.bin 1 (inputPin a) (inputPin b)) (inputPin c))
      (if keep then insert (Extended.bin 1 (inputPin a) (inputPin b)) Extended.initial.toFinset
        else Extended.initial.toFinset)).card = if keep then 12 else 11 := by
  obtain ⟨hs, hz, hsz⟩ := mixed_signal_fresh a b c hab hca hcb
  cases keep with
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [Finset.card_insert_of_notMem (by simpa only [List.mem_toFinset] using hz), initial_card_ten]
  | true =>
      simp only [ite_true]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, List.mem_toFinset]
        exact not_or.mpr ⟨Ne.symm hsz, hz⟩)]
      rw [Finset.card_insert_of_notMem (by simpa only [List.mem_toFinset] using hs), initial_card_ten]
