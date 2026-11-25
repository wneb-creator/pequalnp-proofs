import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace PEqualNP.Outside.L_gct_231.Sym3Coverage

def wittQ (u : Fin 5 → ℂ) : ℂ := 2*u 0*u 2+2*u 1*u 3+18*(u 4)^2

def minor (u v : Fin 5 → ℂ) (i j : Fin 5) : ℂ := u i*v j-u j*v i

lemma minor_self (u v : Fin 5 → ℂ) (i : Fin 5) : minor u v i i=0 := by
  simp [minor]

lemma minor_swap (u v : Fin 5 → ℂ) (i j : Fin 5) :
    minor u v i j= -minor u v j i := by
  dsimp [minor]
  ring

lemma minor_isotropic (u v : Fin 5 → ℂ)
    (hq : ∀ a b : ℂ, wittQ (fun i => a*u i+b*v i)=0) (i : Fin 5) :
    2*minor u v i 0*minor u v i 2+2*minor u v i 1*minor u v i 3+
      18*(minor u v i 4)^2=0 := by
  have he := hq (v i) (-u i)
  dsimp [wittQ] at he
  dsimp [minor]
  linear_combination he

lemma minor_polar (u v : Fin 5 → ℂ)
    (hq : ∀ a b : ℂ, wittQ (fun i => a*u i+b*v i)=0) (i j : Fin 5) :
    minor u v i 0*minor u v j 2+minor u v i 2*minor u v j 0+
      minor u v i 1*minor u v j 3+minor u v i 3*minor u v j 1+
      18*minor u v i 4*minor u v j 4=0 := by
  have hi := hq (v i) (-u i)
  have hj := hq (v j) (-u j)
  have hij := hq (v i+v j) (-u i-u j)
  dsimp [wittQ] at hi hj hij
  dsimp [minor]
  linear_combination (1/2:ℂ)*(hij-hi-hj)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma four_minors_cover (u v : Fin 5 → ℂ)
    (hq : ∀ a b : ℂ, wittQ (fun i => a*u i+b*v i)=0)
    (h01 : minor u v 0 1=0) (h03 : minor u v 0 3=0)
    (h21 : minor u v 2 1=0) (h23 : minor u v 2 3=0) :
    ∀ i j : Fin 5, minor u v i j=0 := by
  have h10 : minor u v 1 0=0 := by rw [minor_swap, h01, neg_zero]
  have h12 : minor u v 1 2=0 := by rw [minor_swap, h21, neg_zero]
  have h30 : minor u v 3 0=0 := by rw [minor_swap, h03, neg_zero]
  have h32 : minor u v 3 2=0 := by rw [minor_swap, h23, neg_zero]
  have h04 : minor u v 0 4=0 := by
    have he := minor_isotropic u v hq 0
    simp only [minor_self, h01, h03, mul_zero, zero_mul, zero_add] at he
    apply eq_zero_of_pow_eq_zero (n := 2)
    linear_combination (1/18:ℂ)*he
  have h14 : minor u v 1 4=0 := by
    have he := minor_isotropic u v hq 1
    simp only [minor_self, h10, h12, mul_zero, zero_mul, zero_add] at he
    apply eq_zero_of_pow_eq_zero (n := 2)
    linear_combination (1/18:ℂ)*he
  have h24 : minor u v 2 4=0 := by
    have he := minor_isotropic u v hq 2
    simp only [minor_self, h21, h23, mul_zero, zero_add] at he
    apply eq_zero_of_pow_eq_zero (n := 2)
    linear_combination (1/18:ℂ)*he
  have h34 : minor u v 3 4=0 := by
    have he := minor_isotropic u v hq 3
    simp only [minor_self, h30, h32, mul_zero, zero_add] at he
    apply eq_zero_of_pow_eq_zero (n := 2)
    linear_combination (1/18:ℂ)*he
  have h02 : minor u v 0 2=0 := by
    have he := minor_polar u v hq 0 2
    rw [minor_swap u v 2 0] at he
    simp only [minor_self, h01, h03, h04, mul_zero, zero_mul, zero_add, add_zero] at he
    apply eq_zero_of_pow_eq_zero (n := 2)
    linear_combination -he
  have h13 : minor u v 1 3=0 := by
    have he := minor_polar u v hq 1 3
    rw [minor_swap u v 3 1] at he
    simp only [minor_self, h10, h12, h14, mul_zero, zero_mul, zero_add, add_zero] at he
    apply eq_zero_of_pow_eq_zero (n := 2)
    linear_combination -he
  have h20 : minor u v 2 0=0 := by rw [minor_swap, h02, neg_zero]
  have h31 : minor u v 3 1=0 := by rw [minor_swap, h13, neg_zero]
  have h40 : minor u v 4 0=0 := by rw [minor_swap, h04, neg_zero]
  have h41 : minor u v 4 1=0 := by rw [minor_swap, h14, neg_zero]
  have h42 : minor u v 4 2=0 := by rw [minor_swap, h24, neg_zero]
  have h43 : minor u v 4 3=0 := by rw [minor_swap, h34, neg_zero]
  intro i j
  fin_cases i <;> fin_cases j <;>
    first | exact minor_self u v _ | exact h01 | exact h02 | exact h03 | exact h04
          | exact h10 | exact h12 | exact h13 | exact h14 | exact h20 | exact h21
          | exact h23 | exact h24 | exact h30 | exact h31 | exact h32 | exact h34
          | exact h40 | exact h41 | exact h42 | exact h43

lemma nonzero_chart_minor (u v : Fin 5 → ℂ)
    (hq : ∀ a b : ℂ, wittQ (fun i => a*u i+b*v i)=0)
    (hind : ∃ i j : Fin 5, minor u v i j≠0) :
    minor u v 0 1≠0 ∨ minor u v 0 3≠0 ∨ minor u v 2 1≠0 ∨ minor u v 2 3≠0 := by
  by_contra hn
  have h01 : minor u v 0 1=0 := by
    by_contra h
    exact hn (Or.inl h)
  have h03 : minor u v 0 3=0 := by
    by_contra h
    exact hn (Or.inr (Or.inl h))
  have h21 : minor u v 2 1=0 := by
    by_contra h
    exact hn (Or.inr (Or.inr (Or.inl h)))
  have h23 : minor u v 2 3=0 := by
    by_contra h
    exact hn (Or.inr (Or.inr (Or.inr h)))
  obtain ⟨i,j,hij⟩ := hind
  exact hij (four_minors_cover u v hq h01 h03 h21 h23 i j)

end PEqualNP.Outside.L_gct_231.Sym3Coverage
