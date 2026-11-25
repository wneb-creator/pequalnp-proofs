import Neighbourhoods
import PairDecomposition

namespace PEqualNP.Outside.L_meta_4675_aux.DegreeTwoCard

open PEqualNP.Outside.L_meta_4970_aux
open PEqualNP.Outside.L_meta_4970_aux.PairDecomposition

lemma edges_eq_vertices {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hdegree : ∀ v, (neighbours E v).card = 2) : E.card = p + l := by
  have left (a : Fin p) : (row E a).card = 2 := by
    have h := hdegree (Fin.castAdd l a)
    rw [neighbours_left, Finset.card_image_of_injective] at h
    · exact h
    · intro b c he
      apply Fin.ext
      have hh := congrArg Fin.val he
      simp only [Fin.val_natAdd] at hh
      omega
  have right (b : Fin l) : (Finset.univ.filter fun a => (a, b) ∈ E).card = 2 := by
    have h := hdegree (Fin.natAdd p b)
    rw [neighbours_right, Finset.card_image_of_injective] at h
    · exact h
    · intro a c he
      exact Fin.ext (congrArg (fun z : Fin (p + l) => z.val) he)
  have transrow (b : Fin l) : row (E.image Prod.swap) b =
      Finset.univ.filter fun a => (a, b) ∈ E := by
    ext a
    simp [row, Finset.mem_image, Prod.exists]
  have swap_inj : Function.Injective (Prod.swap : Fin p × Fin l → Fin l × Fin p) := by
    intro a b hab
    simpa using congrArg Prod.swap hab
  have hp : E.card = p * 2 := by
    rw [← row_card_sum E]
    simp_rw [left]
    simp
  have hl : E.card = l * 2 := by
    have hs := row_card_sum (E.image Prod.swap)
    rw [Finset.card_image_of_injective _ swap_inj] at hs
    simp_rw [transrow, right] at hs
    simpa using hs.symm
  omega

end PEqualNP.Outside.L_meta_4675_aux.DegreeTwoCard
