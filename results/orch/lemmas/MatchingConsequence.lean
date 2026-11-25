import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.MatchingConsequence

lemma cover_card_of_matching {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : Fin p → Fin l) (hf : Function.Injective f) (hE : ∀ a, (a, f a) ∈ E)
    (S : Finset (Fin (p + l)))
    (hS : ∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) :
    p ≤ S.card := by
  classical
  let pick : Fin p → Fin (p + l) :=
    fun a => if Fin.castAdd l a ∈ S then Fin.castAdd l a else Fin.natAdd p (f a)
  have hpick : Function.Injective pick := by
    intro a b he
    dsimp [pick] at he
    split_ifs at he with ha hb
    · apply Fin.ext
      have hval := congrArg Fin.val he
      simpa using hval
    · have hval := congrArg Fin.val he
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      have := a.isLt
      omega
    · have hval := congrArg Fin.val he
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      have := b.isLt
      omega
    · apply hf
      apply Fin.ext
      have hval := congrArg Fin.val he
      simpa using hval
  have hpS : ∀ a, pick a ∈ S := by
    intro a
    dsimp [pick]
    split_ifs with ha
    · exact ha
    · exact (hS a (f a) (hE a)).resolve_left ha
  calc
    p = (Finset.univ.image pick).card := by
      rw [Finset.card_image_of_injective _ hpick]
      simp
    _ ≤ S.card := Finset.card_le_card (by
      intro v hv
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
      exact hpS a)

lemma size_overhead_cancels {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : Fin p → Fin l) (hf : Function.Injective f) (hE : ∀ a, (a, f a) ∈ E)
    (s d : ℕ) (hd : d = s + p)
    (hbound : ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ d + 1) :
    E.card ≤ s + 1 := by
  obtain ⟨S, hS, hcard⟩ := hbound
  have hmatch := cover_card_of_matching E f hf hE S hS
  omega

end PEqualNP.Outside.L_meta_4675.MatchingConsequence
