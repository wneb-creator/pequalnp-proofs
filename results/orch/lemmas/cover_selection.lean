import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451

lemma decMinCover (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ T : Finset (Fin n),
      (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) ∧
      ∀ T' : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ T' ∨ j ∈ T') → T.card ≤ T'.card := by
  classical
  let P : ℕ → Prop := fun k => ∃ T : Finset (Fin n),
    (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) ∧ T.card = k
  have hex : ∃ k, P k := ⟨n, Finset.univ, by simp, by simp⟩
  obtain ⟨T, hT, hcard⟩ := Nat.find_spec hex
  refine ⟨T, hT, ?_⟩
  intro T' hT'
  rw [hcard]
  exact Nat.find_min' hex ⟨T', hT', rfl⟩

end PEqualNP.Outside.L_meta_3451
