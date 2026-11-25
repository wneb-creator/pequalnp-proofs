import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

def ogrG (A B K : ℂ) : ℂ :=
  9*A^4 + 9*A^3*B + 9*A^3 + 9*A^2*B^2 + 18*A^2*B - 3*A^2*K + 5*A^2 - 6*A*B*K + 3*A*B - 6*A*K + A + K^2 - K

def ogrF (A B K : ℂ) : ℂ :=
  27*A^4*B + 9*A^4 + 27*A^3*B^2 + 63*A^3*B + 6*A^3*K + 21*A^3 + 27*A^2*B^3 + 72*A^2*B^2 - 3*A^2*B*K + 42*A^2*B + 3*A^2*K + 9*A^2 + 18*A*B^3 - 12*A*B^2*K + 42*A*B^2 - 12*A*B*K + 15*A*B - A*K^2 + A - 6*B^2*K + 3*B^2 + B*K^2 - 7*B*K + B - K^2 - K

def ogrEvenRoots (A B K : ℂ) : Prop :=
  A = (-1) ∧ B = (-1) ∧ K = (-1) ∨
  A = (-1) ∧ B = (-1) ∧ K = (1) ∨
  A = (-1) ∧ B = (0) ∧ K = (-1) ∨
  A = (-1) ∧ B = (1) ∧ K = (-3) ∨
  A = (-1) ∧ B = (1) ∧ K = (-1) ∨
  A = (-2/3) ∧ B = (-1/3) ∧ K = (0) ∨
  A = (-2/3) ∧ B = (0) ∧ K = (-1) ∨
  A = (-1/3) ∧ B = (-2/3) ∧ K = (0) ∨
  A = (-1/3) ∧ B = (-1/3) ∧ K = (-1/3) ∨
  A = (-1/3) ∧ B = (-1/3) ∧ K = (1/3) ∨
  A = (-1/3) ∧ B = (0) ∧ K = (0) ∨
  A = (0) ∧ B = (-1) ∧ K = (1) ∨
  A = (0) ∧ B = (-2/3) ∧ K = (1) ∨
  A = (0) ∧ B = (-1/3) ∧ K = (0) ∨
  A = (0) ∧ B = (0) ∧ K = (0) ∨
  A = (1) ∧ B = (-1) ∧ K = (1) ∨
  A = (1) ∧ B = (-1) ∧ K = (3)

lemma ogr_even_roots_swap (A B K : ℂ) (h : ogrEvenRoots A B K) :
    ogrEvenRoots B A (-K) := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    rcases h with ⟨rfl, rfl, rfl⟩
    norm_num [ogrEvenRoots]

lemma ogr_equal_case (A K : ℂ)
    (h0 : ogrG A A K = 0) (h1 : ogrF A A K = 0)
    (h3 : ogrG A A (-K) = 0) : ogrEvenRoots A A K := by
  have hc : K * (3*A+1)^2 = 0 := by
    dsimp [ogrG] at h0 h3
    linear_combination (h3-h0)/2
  rcases mul_eq_zero.mp hc with hk | ha
  · have ha : A = 0 := by
      dsimp [ogrG,ogrF] at h0 h1
      rw [hk] at h0 h1
      linear_combination 3*(A+1)*h0-h1
    norm_num [ogrEvenRoots,ha,hk]
  · have ha' : 3*A+1 = 0 := eq_zero_of_pow_eq_zero ha
    have ha : A = -1/3 := by linear_combination ha'/3
    have hk : (3*K-1)*(3*K+1) = 0 := by
      rw [ha] at h0
      dsimp [ogrG] at h0
      linear_combination 9*h0
    rcases mul_eq_zero.mp hk with hk | hk
    · have hk : K = 1/3 := by linear_combination hk/3
      norm_num [ogrEvenRoots,ha,hk]
    · have hk : K = -1/3 := by linear_combination hk/3
      norm_num [ogrEvenRoots,ha,hk]

set_option maxHeartbeats 4000000 in
lemma ogr_minus_case (A B K : ℂ) (hb : B+1 ≠ 0)
    (hk : K = 3*(A-B)-1)
    (h0 : ogrG A B K = 0) (h1 : ogrF A B K = 0)
    (h2 : ogrF B A (-K) = 0) (h3 : ogrG B A (-K) = 0) :
    ogrEvenRoots A B K := by
  have hc : A*(3*A+1) = 0 := by
    rw [hk] at h0 h1 h2 h3
    dsimp [ogrG,ogrF] at h0 h1 h2 h3
    linear_combination
      (-(1152*A*B^3 + 3024*A*B^2 + 3024*A*B + 1152*A + 3078*B^4 + 10989*B^3 + 10348*B^2 + 2981*B)/48) * h0 +
      ((336*A + 2745*B^3 + 5688*B^2 + 3272*B + 161)/48) * h1 +
      ((288*A^3 + 672*A^2*B + 126*A^2 - 516*A*B^2 - 369*A*B - 168*A - 630*B^2 - 737*B)/16) * h2 +
      (-(2592*A^4 + 4896*A^3*B + 2142*A^3 + 513*A^2*B^2 + 5283*A^2*B + 755*A^2 + 568*A - 513*B^2 - 1071*B + 287)/48) * h3
  rcases mul_eq_zero.mp hc with ha | ha
  · have hbc : (3*B+1)*(3*B+2) = 0 := by
      rw [hk,ha] at h0
      dsimp [ogrG] at h0
      linear_combination h0
    rcases mul_eq_zero.mp hbc with hb' | hb'
    · have hb' : B = -1/3 := by linear_combination hb'/3
      norm_num [ha,hb'] at hk
      norm_num [ogrEvenRoots,ha,hb',hk]
    · have hb' : B = -2/3 := by linear_combination hb'/3
      norm_num [ha,hb'] at hk
      norm_num [ogrEvenRoots,ha,hb',hk]
  · have ha : A = -1/3 := by linear_combination ha/3
    have hbc : (B+1)*(3*B+2) = 0 := by
      rw [hk,ha] at h0
      dsimp [ogrG] at h0
      linear_combination 3*h0/4
    have hb' : 3*B+2 = 0 := (mul_eq_zero.mp hbc).resolve_left hb
    have hb' : B = -2/3 := by linear_combination hb'/3
    norm_num [ha,hb'] at hk
    norm_num [ogrEvenRoots,ha,hb',hk]

lemma ogr_boundary_roots (B K : ℂ)
    (hB : B*(B-1)*(B+1)=0) (hK : K = -1 ∨ K = -2*B-1) :
    ogrEvenRoots (-1) B K := by
  have hcases : B = 0 ∨ B = 1 ∨ B = -1 := by
    rcases mul_eq_zero.mp hB with hB | hB
    · rcases mul_eq_zero.mp hB with hB | hB
      · exact Or.inl hB
      · right; left; linear_combination hB
    · right; right; linear_combination hB
  rcases hcases with rfl | rfl | rfl <;>
    rcases hK with rfl | rfl <;> norm_num [ogrEvenRoots]

set_option maxHeartbeats 4000000 in
lemma ogr_boundary_case (B K : ℂ)
    (h1 : ogrF (-1) B K = 0) (h2 : ogrF B (-1) (-K) = 0)
    (h3 : (B+1)*ogrG B (-1) (-K) = 0) : ogrEvenRoots (-1) B K := by
  have hc : (K+1)*(2*B+K+1)=0 := by
    dsimp [ogrG,ogrF] at h1 h2 h3
    linear_combination
      -(18*B^3+18*B^2+3*B*K+6*B+3*K+2)/4*h1 -
      (18*B^2+3*B*K+12*B+3*K+2)/4*h2 -
      3*(3*B+K+1)/2*h3
  rcases mul_eq_zero.mp hc with hk | hk
  · have hk : K = -1 := by linear_combination hk
    have hb : B*(B-1)*(B+1)=0 := by
      rw [hk] at h1
      dsimp [ogrF] at h1
      linear_combination h1/9
    exact ogr_boundary_roots B K hb (Or.inl hk)
  · have hk : K = -2*B-1 := by linear_combination hk
    have hb : B*(B-1)*(B+1)=0 := by
      rw [hk] at h1
      dsimp [ogrF] at h1
      linear_combination h1
    exact ogr_boundary_roots B K hb (Or.inr hk)

set_option maxHeartbeats 4000000 in
lemma hollow_even_chart_classification (A B K : ℂ)
    (h0 : (A+1)*ogrG A B K = 0) (h1 : ogrF A B K = 0)
    (h2 : ogrF B A (-K) = 0) (h3 : (B+1)*ogrG B A (-K) = 0) :
    ogrEvenRoots A B K := by
  by_cases ha : A+1 = 0
  · have ha : A = -1 := by linear_combination ha
    subst A
    exact ogr_boundary_case B K h1 h2 h3
  by_cases hb : B+1 = 0
  · have hb : B = -1 := by linear_combination hb
    subst B
    have hr := ogr_boundary_case A (-K) h2 (by simpa using h1) (by simpa using h0)
    simpa using ogr_even_roots_swap (-1) A (-K) hr
  have hg0 : ogrG A B K = 0 := (mul_eq_zero.mp h0).resolve_left ha
  have hg3 : ogrG B A (-K) = 0 := (mul_eq_zero.mp h3).resolve_left hb
  have hc : (A-B)*(3*A-3*B-K-1)*(3*A-3*B-K+1) = 0 := by
    dsimp [ogrG,ogrF] at hg0 h1 h2 hg3
    linear_combination -(B+1)^2*hg0+(B+1)*h1-(A+1)*h2+(A+1)^2*hg3
  rcases mul_eq_zero.mp hc with hc | hc
  · rcases mul_eq_zero.mp hc with hab | hk
    · have hab : B = A := by linear_combination -hab
      subst B
      exact ogr_equal_case A K hg0 h1 hg3
    · have hk : K = 3*(A-B)-1 := by linear_combination -hk
      exact ogr_minus_case A B K hb hk hg0 h1 h2 hg3
  · have hk : -K = 3*(B-A)-1 := by linear_combination hc
    have hr := ogr_minus_case B A (-K) ha hk hg3 h2
      (by simpa using h1) (by simpa using hg0)
    simpa using ogr_even_roots_swap B A (-K) hr

end PEqualNP.Outside.L_gct_231
