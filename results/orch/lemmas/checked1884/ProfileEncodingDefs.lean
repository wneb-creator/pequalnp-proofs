import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884_aux.ProfileEncoding

def bits (k : Fin 7) : Finset (Fin 3) :=
  Finset.univ.filter fun t => (k.val + 1).testBit t.val

lemma bits_surjective : ∀ S : Finset (Fin 3), S.Nonempty → ∃ k : Fin 7, bits k = S := by
  decide +kernel

lemma encode_profiles {α : Type*} [DecidableEq α]
    (R : Finset α) (hcard : R.card = 3) (P : Fin 6 → Finset α)
    (hsub : ∀ e, P e ⊆ R) (hne : ∀ e, (P e).Nonempty) :
    ∃ f : Fin 6 → Fin 7,
      (∀ e, (bits (f e)).card = (P e).card) ∧
      (∀ e d, bits (f e) ⊆ bits (f d) ↔ P e ⊆ P d) := by
  classical
  let j : R ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using hcard)
  let Q (e : Fin 6) : Finset (Fin 3) := ((P e).subtype fun a => a ∈ R).map j.toEmbedding
  have hQcard (e : Fin 6) : (Q e).card = (P e).card := by
    simp only [Q, Finset.card_map, Finset.card_subtype]
    rw [Finset.filter_eq_self.mpr (hsub e)]
  have hQne (e : Fin 6) : (Q e).Nonempty := by
    apply Finset.card_pos.mp
    rw [hQcard]
    exact Finset.card_pos.mpr (hne e)
  have hQsub (e d : Fin 6) : Q e ⊆ Q d ↔ P e ⊆ P d := by
    dsimp [Q]
    rw [Finset.map_subset_map]
    constructor
    · intro h a ha
      have ht := h (x := ⟨a, hsub e ha⟩) (by simpa using ha)
      simpa using ht
    · intro h a ha
      simpa using h (by simpa using ha)
  choose f hf using fun e => bits_surjective (Q e) (hQne e)
  refine ⟨f, ?_, ?_⟩
  · intro e
    rw [hf e]
    exact hQcard e
  · intro e d
    rw [hf e, hf d]
    exact hQsub e d

end PEqualNP.Outside.L_meta_1884_aux.ProfileEncoding
