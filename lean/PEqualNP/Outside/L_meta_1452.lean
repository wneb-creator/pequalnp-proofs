import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1452 : ∀ (n f k w : ℕ) (L : Finset (Fin n)) (c : Fin f → Fin n → Fin k) (T : Fin f → Fin k → (Fin n → Bool) → Bool), (∀ S : Finset (Fin n), S.card ≤ w → ∃ j0 : Fin f, Set.InjOn (c j0) (S : Set (Fin n))) → (∀ (j1 : Fin f) (a1 : Fin k) (u v : Fin n → Bool), u ≤ v → T j1 a1 u ≤ T j1 a1 v) → (∀ (j2 : Fin f) (a2 : Fin k) (z : Fin n → Bool), (∀ p2 : Fin n, z p2 = true → c j2 p2 ≠ a2) → T j2 a2 z = false) → (∀ (j3 : Fin f) (a3 : Fin k) (y : Fin n → Bool) (p3 : Fin n), y p3 = true → c j3 p3 = a3 → (∀ q3 : Fin n, y q3 = true → c j3 q3 = a3 → q3 = p3) → (T j3 a3 y = true ↔ p3 ∈ L)) → ∀ x : Fin n → Bool, (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ w → ((∀ j : Fin f, ∃ a : Fin k, T j a x = true) ↔ ∃ p : Fin n, x p = true ∧ p ∈ L) := by
  intro n f k w L c T hsplit hmono hoff hone x hx
  constructor
  · intro hall
    obtain ⟨j0, hinj⟩ := hsplit (Finset.univ.filter (fun i : Fin n => x i = true)) hx
    obtain ⟨a, ha⟩ := hall j0
    by_cases hex : ∃ p : Fin n, x p = true ∧ c j0 p = a
    · obtain ⟨p, hp, hc⟩ := hex
      refine ⟨p, hp, ?_⟩
      refine (hone j0 a x p hp hc ?_).1 ha
      intro q hq hcq
      apply hinj
      · simp [hq]
      · simp [hp]
      · rw [hcq, hc]
    · exfalso
      have := hoff j0 a x (fun p hp hc => hex ⟨p, hp, hc⟩)
      rw [this] at ha
      exact Bool.false_ne_true ha
  · rintro ⟨p, hp, hpL⟩ j
    refine ⟨c j p, ?_⟩
    have hy : T j (c j p) (fun i => decide (i = p)) = true := by
      refine (hone j (c j p) (fun i => decide (i = p)) p (by simp) rfl ?_).2 hpL
      intro q hq _
      simpa using hq
    have hle : (fun i => decide (i = p)) ≤ x := by
      intro i
      by_cases h : i = p
      · subst h; simp [hp]
      · simp [h]
    have := hmono j (c j p) _ x hle
    rw [hy] at this
    exact le_antisymm le_top this
