import PackingRecordProofs

namespace PEqualNP.Outside.L_meta_1896_aux.PackingRecords

lemma mask_bits_of_finite {R : Type*} {n : Nat} (e : R ≃ Fin n)
    (mask : Nat) (predicate : R → Prop) (hbound : mask < 2 ^ n)
    (hlow : ∀ r : R, mask.testBit (e r).val = true ↔ predicate r) :
    ∀ k : Nat, mask.testBit k = true ↔
      ∃ r : R, (e r).val = k ∧ predicate r := by
  intro k
  by_cases hk : k < n
  · let r := e.symm ⟨k, hk⟩
    have he : (e r).val = k := by simp [r]
    constructor
    · intro ht
      refine ⟨r, he, (hlow r).mp ?_⟩
      simpa only [he] using ht
    · rintro ⟨r', he', hp⟩
      have ht := (hlow r').mpr hp
      simpa only [he'] using ht
  · have hb : mask < 2 ^ k :=
      lt_of_lt_of_le hbound (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : n ≤ k))
    have hz := Nat.testBit_eq_false_of_lt hb
    constructor
    · intro ht
      rw [hz] at ht
      exact Bool.noConfusion ht
    · rintro ⟨r, he, hp⟩
      have hr := (e r).isLt
      omega

end PEqualNP.Outside.L_meta_1896_aux.PackingRecords
