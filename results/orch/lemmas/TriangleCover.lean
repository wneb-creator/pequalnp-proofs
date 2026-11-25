import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

def wittQ (u : Fin 5 → ℂ) : ℂ := u 0*u 2+u 1*u 3-3*(u 4)^2

def wittPolar (u v : Fin 5 → ℂ) : ℂ :=
  u 0*v 2+u 2*v 0+u 1*v 3+u 3*v 1-6*u 4*v 4

def wittMinor (u v : Fin 5 → ℂ) (i j : Fin 5) : ℂ := u i*v j-u j*v i

def wittTriangleMinor (u v : Fin 5 → ℂ) : Fin 4 → ℂ :=
  ![wittMinor u v 0 1,
    (u 0-u 3)*(-v 0-v 1-v 2-2*v 3-6*v 4)-
      (v 0-v 3)*(-u 0-u 1-u 2-2*u 3-6*u 4),
    (u 1-u 2)*(-v 0-v 1-2*v 2-v 3-6*v 4)-
      (v 1-v 2)*(-u 0-u 1-2*u 2-u 3-6*u 4),
    -wittMinor u v 2 3]

set_option maxHeartbeats 4000000 in
lemma hollow_triangle_minors_zero (u v : Fin 5 → ℂ)
    (hqu : wittQ u = 0) (hqv : wittQ v = 0) (hb : wittPolar u v = 0)
    (ht : ∀ k : Fin 4, wittTriangleMinor u v k = 0) :
    ∀ i j : Fin 5, wittMinor u v i j = 0 := by
  have h01 : wittMinor u v 0 1 = 0 := by simpa [wittTriangleMinor] using ht 0
  have h23 : wittMinor u v 2 3 = 0 := by simpa [wittTriangleMinor] using ht 3
  have h04s : (wittMinor u v 0 4)^2 = 0 := by
    dsimp [wittQ,wittPolar,wittMinor] at hqu hqv hb h01 ⊢
    linear_combination -(v 0)^2/3*hqu-(u 0)^2/3*hqv+u 0*v 0/3*hb+
      (u 0*v 3-u 3*v 0)/3*h01
  have h14s : (wittMinor u v 1 4)^2 = 0 := by
    dsimp [wittQ,wittPolar,wittMinor] at hqu hqv hb h01 ⊢
    linear_combination -(v 1)^2/3*hqu-(u 1)^2/3*hqv+u 1*v 1/3*hb-
      (u 1*v 2-u 2*v 1)/3*h01
  have h24s : (wittMinor u v 2 4)^2 = 0 := by
    dsimp [wittQ,wittPolar,wittMinor] at hqu hqv hb h23 ⊢
    linear_combination -(v 2)^2/3*hqu-(u 2)^2/3*hqv+u 2*v 2/3*hb-
      (u 1*v 2-u 2*v 1)/3*h23
  have h34s : (wittMinor u v 3 4)^2 = 0 := by
    dsimp [wittQ,wittPolar,wittMinor] at hqu hqv hb h23 ⊢
    linear_combination -(v 3)^2/3*hqu-(u 3)^2/3*hqv+u 3*v 3/3*hb+
      (u 0*v 3-u 3*v 0)/3*h23
  have h04 : wittMinor u v 0 4 = 0 := eq_zero_of_pow_eq_zero h04s
  have h14 : wittMinor u v 1 4 = 0 := eq_zero_of_pow_eq_zero h14s
  have h24 : wittMinor u v 2 4 = 0 := eq_zero_of_pow_eq_zero h24s
  have h34 : wittMinor u v 3 4 = 0 := eq_zero_of_pow_eq_zero h34s
  have hsum2 : (wittMinor u v 0 2+wittMinor u v 1 3)^2 = 0 := by
    dsimp [wittQ,wittPolar,wittMinor] at hqu hqv hb h01 ⊢
    linear_combination -4*(v 0*v 2+v 1*v 3)*hqu-12*(u 4)^2*hqv+
      (u 0*v 2+u 2*v 0+u 1*v 3+u 3*v 1+6*u 4*v 4)*hb+
      4*(u 2*v 3-u 3*v 2)*h01
  have hsum : wittMinor u v 0 2+wittMinor u v 1 3 = 0 :=
    eq_zero_of_pow_eq_zero hsum2
  have h03 : wittMinor u v 0 3 = 0 := by
    have hh := ht 1
    simp [wittTriangleMinor] at hh
    dsimp [wittMinor] at h01 hsum h04 h23 h34 ⊢
    linear_combination -hh/3-h01/3-hsum/3-2*h04-h23/3+2*h34
  have h12 : wittMinor u v 1 2 = 0 := by
    have hh := ht 2
    simp [wittTriangleMinor] at hh
    dsimp [wittMinor] at h01 hsum h14 h23 h24 ⊢
    linear_combination -hh/3+h01/3-hsum/3-2*h14+h23/3+2*h24
  have h02s : (wittMinor u v 0 2)^2 = 0 := by
    dsimp [wittMinor] at hsum h01 h03 ⊢
    linear_combination (u 0*v 2-u 2*v 0)*hsum-
      (u 2*v 3-u 3*v 2)*h01-(u 1*v 2-u 2*v 1)*h03
  have h02 : wittMinor u v 0 2 = 0 := eq_zero_of_pow_eq_zero h02s
  have h13 : wittMinor u v 1 3 = 0 := by linear_combination hsum-h02
  intro i j
  fin_cases i <;> fin_cases j <;>
    dsimp [wittMinor] at h01 h02 h03 h04 h12 h13 h14 h23 h24 h34 ⊢ <;>
    solve
    | ring
    | linear_combination h01
    | linear_combination -h01
    | linear_combination h02
    | linear_combination -h02
    | linear_combination h03
    | linear_combination -h03
    | linear_combination h04
    | linear_combination -h04
    | linear_combination h12
    | linear_combination -h12
    | linear_combination h13
    | linear_combination -h13
    | linear_combination h14
    | linear_combination -h14
    | linear_combination h23
    | linear_combination -h23
    | linear_combination h24
    | linear_combination -h24
    | linear_combination h34
    | linear_combination -h34

lemma hollow_triangle_covers_nonzero_minor (u v : Fin 5 → ℂ)
    (hqu : wittQ u = 0) (hqv : wittQ v = 0) (hb : wittPolar u v = 0)
    (hi : ∃ i j : Fin 5, wittMinor u v i j ≠ 0) :
    ∃ k : Fin 4, wittTriangleMinor u v k ≠ 0 := by
  by_contra hh
  push Not at hh
  obtain ⟨i,j,hij⟩ := hi
  exact hij (hollow_triangle_minors_zero u v hqu hqv hb hh i j)

end PEqualNP.Outside.L_gct_231
