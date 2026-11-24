import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451

open PEqualNP.MetaComplexity

def ffCleanAt {n : ℕ} (z : Fin n → Bool) : DMFormula n → Prop
  | .lit _ _ => True
  | .and a b => ffCleanAt z a ∧ ffCleanAt z b ∧
      (a.eval z && b.eval z) = false
  | .or a b => ffCleanAt z a ∧ ffCleanAt z b

def ffBefore {n : ℕ} (a b c d : DMFormula n) : DMFormula n :=
  .and (.and (.or a b) (.or c d)) (.or a c)

def ffAfter {n : ℕ} (a b c d : DMFormula n) : DMFormula n :=
  .or (.and a (.or c d)) (.and b c)

lemma ff_eval {n : ℕ} (a b c d : DMFormula n) (z : Fin n → Bool) :
    (ffAfter a b c d).eval z = (ffBefore a b c d).eval z := by
  simp only [ffAfter, ffBefore, DMFormula.eval]
  cases a.eval z <;> cases b.eval z <;> cases c.eval z <;> cases d.eval z <;> decide

lemma ff_leaves {n : ℕ} (a b c d : DMFormula n) :
    (ffAfter a b c d).leaves + a.leaves = (ffBefore a b c d).leaves := by
  simp only [ffAfter, ffBefore, DMFormula.leaves]
  omega

lemma ff_preserves_clean {n : ℕ} (a b c d : DMFormula n) (z : Fin n → Bool)
    (h : ffCleanAt z (ffBefore a b c d)) : ffCleanAt z (ffAfter a b c d) := by
  obtain ⟨⟨⟨ha, hb⟩, ⟨hc, hd⟩, hab⟩, _, _⟩ := h
  refine ⟨⟨ha, ⟨hc, hd⟩, ?_⟩, ⟨hb, hc, ?_⟩⟩
  · simp only [DMFormula.eval] at hab ⊢
    cases ea : a.eval z <;> cases eb : b.eval z <;> cases ec : c.eval z <;> cases ed : d.eval z <;>
      simp_all
  · simp only [DMFormula.eval] at hab
    cases ea : a.eval z <;> cases eb : b.eval z <;> cases ec : c.eval z <;> cases ed : d.eval z <;>
      simp_all

lemma ff_new_clean {n : ℕ} (a b c d : DMFormula n) (z : Fin n → Bool)
    (ha : ffCleanAt z a) (hb : ffCleanAt z b)
    (hc : ffCleanAt z c) (hd : ffCleanAt z d)
    (ha0 : a.eval z = false) (hc0 : c.eval z = false) :
    ffCleanAt z (ffAfter a b c d) := by
  exact ⟨⟨ha, ⟨hc, hd⟩, by simp [DMFormula.eval, ha0]⟩,
    ⟨hb, hc, by simp [hc0]⟩⟩

end PEqualNP.Outside.L_meta_3451
