import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2962.MatchingCoverCertificate

open PEqualNP.MetaComplexity.NestedCover

def left {m : ℕ} (i : Fin m) : Fin (2 * m) := ⟨i.val, by have := i.isLt; omega⟩
def right {m : ℕ} (i : Fin m) : Fin (2 * m) := ⟨m + i.val, by have := i.isLt; omega⟩

lemma matching_lower_bound {m : ℕ} (G : SimpleGraph (Fin (2 * m)))
    (matching : ∀ i : Fin m, G.Adj (left i) (right i))
    (S : Finset (Fin (2 * m))) (cover : G.IsVertexCover (S : Set (Fin (2 * m)))) :
    m ≤ S.card := by
  let choose : Fin m → Fin (2 * m) := fun i => if left i ∈ S then left i else right i
  have injective : Function.Injective choose := by
    intro i j hij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    have values := congrArg Fin.val hij
    dsimp only [choose] at values
    split_ifs at values <;> simp only [left, right] at values <;> omega
  have included : Finset.univ.image choose ⊆ S := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, _, rfl⟩
    by_cases hl : left i ∈ S
    · simp [choose, hl]
    · have hc := cover (matching i)
      have hr : right i ∈ S := hc.resolve_left hl
      simp [choose, hl, hr]
  have count := Finset.card_le_card included
  rw [Finset.card_image_of_injective _ injective] at count
  simpa using count

lemma minimum_of_matching {m : ℕ} (G : SimpleGraph (Fin (2 * m)))
    (matching : ∀ i : Fin m, G.Adj (left i) (right i))
    (T : Finset (Fin (2 * m))) (cover : G.IsVertexCover (T : Set (Fin (2 * m))))
    (cardinality : T.card = m) : IsMinCover G T := by
  refine ⟨cover, ?_⟩
  intro S hS
  rw [cardinality]
  exact matching_lower_bound G matching S hS

end PEqualNP.Outside.L_meta_2962.MatchingCoverCertificate
