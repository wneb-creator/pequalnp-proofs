import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3566

lemma monotone_graph_boundary {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f : (Fin n → Bool) → Bool) (hf : Monotone f)
    (hedge : ∀ a b, G.Adj a b →
      f (fun i => decide (i = a ∨ i = b)) = true)
    (hindep : ∀ S : Set (Fin n), Maximal G.IsIndepSet S →
      f (fun i => @decide (i ∈ S) (Classical.propDecidable _)) = false) :
    f = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  classical
  funext x
  by_cases hx : ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true
  · obtain ⟨a, b, hab, ha, hb⟩ := hx
    have hle : (fun i => decide (i = a ∨ i = b)) ≤ x := by
      intro i
      apply Bool.le_iff_imp.mpr
      intro hi
      have hi' : i = a ∨ i = b := of_decide_eq_true hi
      rcases hi' with rfl | rfl
      · exact ha
      · exact hb
    have hfx : f x = true := by
      have h := hf hle
      rw [hedge a b hab] at h
      exact Bool.le_iff_imp.mp h rfl
    simp [PEqualNP.MetaComplexity.NestedCover.graphFun, hfx,
      show ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true from ⟨a, b, hab, ha, hb⟩]
  · have hs : G.IsIndepSet {i | x i = true} := by
      intro a ha b hb hne hab
      exact hx ⟨a, b, hab, ha, hb⟩
    obtain ⟨S, hsub, hmax⟩ := Finite.exists_le_maximal hs
    have hle : x ≤ (fun i => decide (i ∈ S)) := by
      intro i
      apply Bool.le_iff_imp.mpr
      intro hi
      exact decide_eq_true (hsub hi)
    have hfx : f x = false := by
      have h := hf hle
      rw [hindep S hmax] at h
      cases heq : f x <;> simp_all [Bool.le_iff_imp]
    simp [PEqualNP.MetaComplexity.NestedCover.graphFun, hfx, hx]

end PEqualNP.Outside.L_meta_3566
