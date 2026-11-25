import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.StrongRelaxOrSafety

def target (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 6 ||
    x 6 && x 8 || x 8 && x 5 || x 5 && x 7 || x 7 && x 4

def put (x : Fin 9 → Bool) (t : Fin 9) (b : Bool) : Fin 9 → Bool :=
  fun i => if i = t then b else x i

def exceptional : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 2 ∨ i = 4 ∨ i = 8)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pivotal : ∀ t : Fin 9, t = 2 ∨ t = 8 → ∀ x : Fin 9 → Bool,
    x t = false → target x = false →
    x = put exceptional t false ∨
      ∃ u : Fin 9, u ≠ t ∧ target (put x u true) = false ∧
        target (put (put x u true) t true) = true := by decide

lemma exceptional_rows : ∀ t : Fin 9, t = 2 ∨ t = 8 →
    exceptional t = true ∧ target (put exceptional t false) = false := by decide

lemma monotone_target (x y : Fin 9 → Bool)
    (hle : ∀ i, x i = true → y i = true) : target x = true → target y = true := by
  simp only [target, Bool.or_eq_true, Bool.and_eq_true]
  aesop

theorem partner_safe (t : Fin 9) (ht : t = 2 ∨ t = 8)
    (G A : (Fin 9 → Bool) → Bool)
    (hcofactor : ∀ x, x t = false → G x = target x)
    (hpositive : ∀ x, target x = true → G x = true)
    (hexceptional : G exceptional = true)
    (hamono : ∀ x y, (∀ i, x i = true → y i = true) → A x = true → A y = true)
    (haindependent : ∀ x y, (∀ i, i ≠ t → x i = y i) → A x = A y)
    (hfactor : ∀ x y, (∀ i, i ≠ t → x i = y i) →
      (x t || A x) = (y t || A y) → G x = G y) :
    ∀ x, A x = true → target x = true := by
  intro x hx
  cases htarget : target x
  · let y := put x t false
    have hyt : y t = false := by simp [y, put]
    have hay : A y = true := by
      rw [← haindependent x y (by intro i hi; simp [y, put, hi])]
      exact hx
    have hnegative : target y = false := by
      cases hy : target y
      · rfl
      · have hle : ∀ i, y i = true → x i = true := by
          intro i hi
          by_cases hit : i = t
          · subst i; simp [hyt] at hi
          · simpa [y, put, hit] using hi
        have hbad := monotone_target y x hle hy
        rw [htarget] at hbad
        cases hbad
    rcases pivotal t ht y hyt hnegative with hspecial | ⟨u, hut, hneg, hpos⟩
    · have hagree : ∀ i, i ≠ t → y i = exceptional i := by
        intro i hi
        rw [hspecial]
        simp [put, hi]
      have hgate : (y t || A y) = (exceptional t || A exceptional) := by
        rw [hay, (exceptional_rows t ht).1]
        simp
      have hbad := hfactor y exceptional hagree hgate
      rw [hcofactor y hyt, hnegative, hexceptional] at hbad
      cases hbad
    · let z := put y u true
      have hzt : z t = false := by simp [z, put, Ne.symm hut, hyt]
      have haz : A z = true := by
        apply hamono y z _ hay
        intro i hi
        by_cases hiu : i = u
        · simp [z, put, hiu]
        · simpa [z, put, hiu] using hi
      have hagree : ∀ i, i ≠ t → z i = put z t true i := by
        intro i hi
        simp [put, hi]
      have hgate : (z t || A z) =
          (put z t true t || A (put z t true)) := by simp [put, haz]
      have hbad := hfactor z (put z t true) hagree hgate
      rw [hcofactor z hzt, hneg, hpositive _ hpos] at hbad
      cases hbad
  · rfl

end PEqualNP.Outside.L_meta_1884.StrongRelaxOrSafety
