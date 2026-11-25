import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2583

lemma shared_mixed_or_repair (r : ℕ) (p b : Bool) (a : Fin r → Bool)
    (H : (Fin r → Bool) → Bool)
    (hsafe : b = true → (∃ i, a i = true) →
      H (fun i => (p || a i) && (p || b)) = true) :
    H (fun i => (p || a i) && (p || b)) =
      (H (fun _ => p) || (b && decide (∃ i, a i = true))) := by
  by_cases hb : b = true
  · subst b
    by_cases ha : ∃ i, a i = true
    · rw [hsafe rfl ha]
      simp [ha]
    · have hzero : ∀ i, a i = false := by
        intro i
        cases hi : a i
        · rfl
        · exact (ha ⟨i, hi⟩).elim
      simp [hzero]
  · have hb0 : b = false := by simpa using hb
    subst b
    have he : (fun i => (p || a i) && (p || false)) = fun _ => p := by
      funext i
      cases p <;> simp
    rw [he]
    simp

end PEqualNP.Outside.L_meta_2583
