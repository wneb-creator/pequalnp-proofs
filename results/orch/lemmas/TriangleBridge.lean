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

lemma witt_pair_independent_has_minor (u v : Fin 5 → ℂ)
    (hi : LinearIndependent ℂ ![u,v]) : ∃ i j : Fin 5, wittMinor u v i j ≠ 0 := by
  by_contra hh
  push Not at hh
  have hlin := linearIndependent_fin2.mp hi
  change v ≠ 0 ∧ ∀ a : ℂ, a • v ≠ u at hlin
  obtain ⟨i,hvi⟩ : ∃ i : Fin 5, v i ≠ 0 := by
    by_contra hv
    push Not at hv
    apply hlin.1
    funext i
    exact hv i
  apply hlin.2 (u i / v i)
  funext j
  change u i / v i * v j = u j
  have h := hh i j
  dsimp [wittMinor] at h
  field_simp [hvi]
  linear_combination h

lemma hollow_triangle_covers_independent_pair (u v : Fin 5 → ℂ)
    (hqu : wittQ u = 0) (hqv : wittQ v = 0) (hb : wittPolar u v = 0)
    (hi : LinearIndependent ℂ ![u,v]) :
    ∃ k : Fin 4, wittTriangleMinor u v k ≠ 0 := by
  exact hollow_triangle_covers_nonzero_minor u v hqu hqv hb
    (witt_pair_independent_has_minor u v hi)

lemma normalize_two_linear_coordinates
    (W : Submodule ℂ (Fin 5 → ℂ))
    (F G : (Fin 5 → ℂ) →ₗ[ℂ] ℂ)
    (u v : Fin 5 → ℂ) (hu : u ∈ W) (hv : v ∈ W)
    (hd : F u*G v-F v*G u ≠ 0) :
    ∃ a ∈ W, ∃ b ∈ W, F a=1 ∧ G a=0 ∧ F b=0 ∧ G b=1 := by
  have hd' : G v*F u-F v*G u ≠ 0 := by simpa [mul_comm] using hd
  let d := F u*G v-F v*G u
  let a := (G v/d) • u-(G u/d) • v
  let b := (F u/d) • v-(F v/d) • u
  refine ⟨a,W.sub_mem (W.smul_mem _ hu) (W.smul_mem _ hv),
    b,W.sub_mem (W.smul_mem _ hv) (W.smul_mem _ hu),?_,?_,?_,?_⟩
  all_goals
    dsimp [a,b,d]
    simp only [map_sub,map_smul,smul_eq_mul]
    field_simp [hd,hd'] <;> ring

lemma isotropic_even_chart_normal_form (u v : Fin 5 → ℂ)
    (hu0 : u 0=1) (hu1 : u 1=0) (hv0 : v 0=0) (hv1 : v 1=1)
    (hqu : wittQ u=0) (hqv : wittQ v=0) (hb : wittPolar u v=0) :
    ∃ A B K : ℂ,
      u = ![1,0,3*A^2,3*A*B-K,A] ∧
      v = ![0,1,3*A*B+K,3*B^2,B] := by
  have hu2 : u 2=3*(u 4)^2 := by
    dsimp [wittQ] at hqu
    rw [hu0,hu1] at hqu
    linear_combination hqu
  have hv3 : v 3=3*(v 4)^2 := by
    dsimp [wittQ] at hqv
    rw [hv0,hv1] at hqv
    linear_combination hqv
  have hu3 : u 3=6*u 4*v 4-v 2 := by
    dsimp [wittPolar] at hb
    rw [hu0,hu1,hv0,hv1] at hb
    linear_combination hb
  refine ⟨u 4,v 4,v 2-3*u 4*v 4,?_,?_⟩
  · funext i
    fin_cases i <;> simp [hu0,hu1,hu2,hu3] <;> ring
  · funext i
    fin_cases i <;> simp [hv0,hv1,hv3]

end PEqualNP.Outside.L_gct_231
