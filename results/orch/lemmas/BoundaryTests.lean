import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.BoundaryTests

def edgeValue {p l : ℕ} (E : Finset (Fin p × Fin l))
    (x : Fin (p + l) → Bool) : Bool :=
  decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧
    x (Fin.natAdd p b) = true)

def edgeInput {p l : ℕ} (a : Fin p) (b : Fin l) : Fin (p + l) → Bool :=
  fun i => decide (i = Fin.castAdd l a ∨ i = Fin.natAdd p b)

def maximalIndependent {p l : ℕ} (E : Finset (Fin p × Fin l))
    (x : Fin (p + l) → Bool) : Prop :=
  edgeValue E x = false ∧ ∀ y, x ≤ y → edgeValue E y = false → y ≤ x

lemma edgeInput_le {p l : ℕ} (a : Fin p) (b : Fin l)
    (x : Fin (p + l) → Bool) (ha : x (Fin.castAdd l a) = true)
    (hb : x (Fin.natAdd p b) = true) : edgeInput a b ≤ x := by
  intro i
  by_cases hia : i = Fin.castAdd l a
  · subst i
    simp [edgeInput, ha]
  by_cases hib : i = Fin.natAdd p b
  · subst i
    simp [edgeInput, hb]
  simp [edgeInput, hia, hib]

lemma independent_extends {p l : ℕ} (E : Finset (Fin p × Fin l))
    (x : Fin (p + l) → Bool) (hx : edgeValue E x = false) :
    ∃ y, x ≤ y ∧ maximalIndependent E y := by
  let S := Finset.univ.filter (fun y : Fin (p + l) → Bool => edgeValue E y = false)
  have hxS : x ∈ S := by simp [S, hx]
  obtain ⟨y, hxy, hy, hmax⟩ := S.exists_le_maximal hxS
  refine ⟨y, hxy, ?_, ?_⟩
  · simpa [S] using hy
  · intro z hyz hz
    exact hmax (by simp [S, hz]) hyz

theorem boundary_complete {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : (Fin (p + l) → Bool) → Bool) (hf : Monotone f)
    (hpos : ∀ a b, (a, b) ∈ E → f (edgeInput a b) = true)
    (hneg : ∀ x, maximalIndependent E x → f x = false) : f = edgeValue E := by
  funext x
  cases he : edgeValue E x with
  | false =>
      obtain ⟨y, hxy, hy⟩ := independent_extends E x he
      have h := hf hxy
      exact le_antisymm (by simpa [hneg y hy] using h) bot_le
  | true =>
      have hE : ∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧
          x (Fin.natAdd p b) = true := of_decide_eq_true he
      obtain ⟨a, b, hab, ha, hb⟩ := hE
      have h := hf (edgeInput_le a b x ha hb)
      exact le_antisymm le_top (by simpa [hpos a b hab] using h)

end PEqualNP.Outside.L_meta_4675.BoundaryTests
