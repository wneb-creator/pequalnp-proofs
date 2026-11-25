import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

lemma eq_of_boolean_boundary {α : Type*} [PartialOrder α] [Finite α]
    (f g : α → Bool) (hf : Monotone f)
    (hmin : ∀ x, Minimal (fun y => g y = true) x → f x = true)
    (hmax : ∀ x, Maximal (fun y => g y = false) x → f x = false) :
    f = g := by
  funext x
  cases hg : g x with
  | false =>
      obtain ⟨z, hxz, hz⟩ := Finite.exists_le_maximal (p := fun y => g y = false) (a := x) hg
      have hle := hf hxz
      have hzero := hmax z hz
      cases hfx : f x <;> simp_all [Bool.le_iff_imp]
  | true =>
      obtain ⟨y, hyx, hy⟩ := Finite.exists_le_maximal (α := OrderDual α) (p := fun y => g y = true) (a := x) hg
      have hle := hf hyx
      have hone := hmin y hy
      cases hfx : f x <;> simp_all [Bool.le_iff_imp]

lemma graph_boundary_complete {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (hf : Monotone f)
    (hedge : ∀ u v, G.Adj u v → f (fun w => decide (w = u ∨ w = v)) = true)
    (hind : ∀ x, Maximal
      (fun y : Fin n → Bool => ∀ u v, G.Adj u v → ¬ (y u = true ∧ y v = true)) x →
      f x = false) :
    f = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  funext x
  by_cases hx : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
  · obtain ⟨u, v, huv, hxu, hxv⟩ := hx
    have hpair : (fun w => decide (w = u ∨ w = v)) ≤ x := by
      intro w
      by_cases hw : w = u ∨ w = v
      · rcases hw with rfl | rfl <;> simp_all
      · simp [hw]
    have hle := hf hpair
    have hyes := hedge u v huv
    have hfx : f x = true := by
      cases hfx : f x <;> simp_all [Bool.le_iff_imp]
    simp only [hfx, PEqualNP.MetaComplexity.NestedCover.graphFun]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    simpa using (show (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) from ⟨u, v, huv, hxu, hxv⟩)
  · have hix : ∀ u v, G.Adj u v → ¬ (x u = true ∧ x v = true) := by
      intro u v huv h
      exact hx ⟨u, v, huv, h⟩
    obtain ⟨z, hxz, hz⟩ := Finite.exists_le_maximal (p := fun y : Fin n → Bool => ∀ u v, G.Adj u v → ¬ (y u = true ∧ y v = true)) (a := x) hix
    have hle := hf hxz
    have hzero := hind z hz
    have hfx : f x = false := by
      cases hfx : f x <;> simp_all [Bool.le_iff_imp]
    simp [hfx, PEqualNP.MetaComplexity.NestedCover.graphFun, hx]


def fanoIncidence (p l : Fin 7) : Prop :=
  (p.val, l.val) ∈ ({(0, 1), (0, 3), (0, 5), (1, 0), (1, 3), (1, 4),
    (2, 2), (2, 3), (2, 6), (3, 0), (3, 1), (3, 2), (4, 1), (4, 4),
    (4, 6), (5, 0), (5, 5), (5, 6), (6, 2), (6, 4), (6, 5)} : Finset (ℕ × ℕ))

def fano_decidable : DecidableRel fanoIncidence := by
  intro p l
  unfold fanoIncidence
  infer_instance

lemma fano_column_cardinality :
    letI := fano_decidable
    ∀ l : Fin 7, (Finset.univ.filter (fun p => fanoIncidence p l)).card = 2 + 1 := by
  decide

lemma fano_unique_line :
    ∀ p p' : Fin 7, p ≠ p' → ∃! l : Fin 7, fanoIncidence p l ∧ fanoIncidence p' l := by
  letI := fano_decidable
  unfold ExistsUnique
  decide


end PEqualNP.Outside.L_meta_2583
