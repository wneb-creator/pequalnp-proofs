import GeometryRowsDefs

namespace PEqualNP.Outside.L_meta_1896_aux.GeometryComplete

def decode (m : Fin 8192) : Finset (Fin 13) :=
  Finset.univ.filter fun p => m.val.testBit p.val

lemma decode_injective : Function.Injective decode := by
  intro a b hab
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 13
  · have hm : a.val.testBit k = true ↔ b.val.testBit k = true := by
      simpa [decode] using Finset.ext_iff.mp hab (⟨k, hk⟩ : Fin 13)
    cases ha : a.val.testBit k <;> cases hb : b.val.testBit k <;> simp_all
  · have hpow : 2^13 ≤ 2^k :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 13 ≤ k)
    have ha : a.val < 2^k := lt_of_lt_of_le (show a.val < 2^13 from a.isLt) hpow
    have hb : b.val < 2^k := lt_of_lt_of_le (show b.val < 2^13 from b.isLt) hpow
    rw [Nat.testBit_eq_false_of_lt ha, Nat.testBit_eq_false_of_lt hb]

lemma decode_surjective : Function.Surjective decode := by
  classical
  have hcard : (Finset.univ.image decode).card = Fintype.card (Finset (Fin 13)) := by
    rw [Finset.card_image_of_injective _ decode_injective]
    norm_num [Fintype.card_finset]
  have hfull := (Finset.card_eq_iff_eq_univ (Finset.univ.image decode)).mp hcard
  intro X
  have hx : X ∈ Finset.univ.image decode := by
    rw [hfull]
    exact Finset.mem_univ X
  obtain ⟨m, _, hm⟩ := Finset.mem_image.mp hx
  exact ⟨m, hm⟩

end PEqualNP.Outside.L_meta_1896_aux.GeometryComplete
