import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace PEqualNP.Outside.L_gct_231.DenseStar

noncomputable def linear0 (h d e f a b c : ℂ) : ℂ :=
  d+2*h*e-2*(h+1)*f+h^2*a-2*h*(h+1)*b+(h+1)^2*c
noncomputable def linear1 (h d e f a b c : ℂ) : ℂ :=
  d+(h+1)*e-h*f+h*a-b-(h+1)*c
noncomputable def coordK (h e f a b c : ℂ) : ℂ :=
  (e-f+h*a-(2*h+1)*b+(h+1)*c)/3
noncomputable def coordX (h a b c : ℂ) : ℂ := h*(h+1)*(a-2*b+c)
noncomputable def coordY (h a b c : ℂ) : ℂ :=
  h*(h+1)*((h+1)*a-(2*h+1)*b+h*c)
noncomputable def lowerQuadratic (h d e f a b c : ℂ) : ℂ :=
  a*c+b^2+2*h*(e*c+b*f)-2*(h+1)*(e*b+a*f)+h^2*(d*c+f^2)-
    2*h*(h+1)*(d*b+e*f)+(h+1)^2*(d*a+e^2)
noncomputable def quotientQuadratic (h X Y k : ℂ) : ℂ :=
  X^2-6*k*Y+2*(2*h+1)^2*k^2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma lower_parameters (h d e f a b c : ℂ)
    (h0 : linear0 h d e f a b c=0) (h1 : linear1 h d e f a b c=0) :
    d=h^2*a-2*h*(h+1)*b+(h+1)^2*c-2*(2*h+1)*coordK h e f a b c ∧
    e= -h*a+(h+1)*b+(h+2)*coordK h e f a b c ∧
    f= -h*b+(h+1)*c+(h-1)*coordK h e f a b c := by
  dsimp [linear0,linear1] at h0 h1
  dsimp [coordK]
  refine ⟨?_,?_,?_⟩
  · linear_combination (1/3:ℂ)*h0+(2/3:ℂ)*h1
  · linear_combination (1/3:ℂ)*h1-(1/3:ℂ)*h0
  · linear_combination (1/3:ℂ)*h1-(1/3:ℂ)*h0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma quadratic_coordinates (h d e f a b c : ℂ)
    (h0 : linear0 h d e f a b c=0) (h1 : linear1 h d e f a b c=0) :
    lowerQuadratic h d e f a b c=
      2*quotientQuadratic h (coordX h a b c) (coordY h a b c) (coordK h e f a b c) := by
  obtain ⟨hd,he,hf⟩ := lower_parameters h d e f a b c h0 h1
  generalize hk : coordK h e f a b c=k at hd he hf ⊢
  rw [hd,he,hf]
  dsimp [lowerQuadratic,quotientQuadratic,coordX,coordY]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma radical_coordinates (h d e f a b c : ℂ) (hh : h≠0) (hh1 : h+1≠0)
    (h0 : linear0 h d e f a b c=0) (h1 : linear1 h d e f a b c=0)
    (hX : coordX h a b c=0) (hY : coordY h a b c=0) (hK : coordK h e f a b c=0) :
    d=a ∧ e=a ∧ f=a ∧ b=a ∧ c=a := by
  have hD : h*(h+1)≠0 := mul_ne_zero hh hh1
  have hab0 : h*(h+1)*(a-b)=0 := by
    dsimp [coordX,coordY] at hX hY
    linear_combination hY-h*hX
  have hbc0 : h*(h+1)*(b-c)=0 := by
    dsimp [coordX,coordY] at hX hY
    linear_combination hY-(h+1)*hX
  have hab : a=b := sub_eq_zero.mp ((mul_eq_zero.mp hab0).resolve_left hD)
  have hbc : b=c := sub_eq_zero.mp ((mul_eq_zero.mp hbc0).resolve_left hD)
  subst b
  subst c
  obtain ⟨hd,he,hf⟩ := lower_parameters h d e f a a a h0 h1
  rw [hK] at hd he hf
  refine ⟨?_,?_,?_,rfl,rfl⟩
  · linear_combination hd
  · linear_combination he
  · linear_combination hf

lemma sum_perm_succ {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma perm4 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix.permanent M =
    (M 0 0 * M 1 1 + M 0 1 * M 1 0) * (M 2 2 * M 3 3 + M 2 3 * M 3 2) + (M 0 0 * M 1 2 + M 0 2 * M 1 0) * (M 2 1 * M 3 3 + M 2 3 * M 3 1) + (M 0 0 * M 1 3 + M 0 3 * M 1 0) * (M 2 1 * M 3 2 + M 2 2 * M 3 1) + (M 0 1 * M 1 2 + M 0 2 * M 1 1) * (M 2 0 * M 3 3 + M 2 3 * M 3 0) + (M 0 1 * M 1 3 + M 0 3 * M 1 1) * (M 2 0 * M 3 2 + M 2 2 * M 3 0) + (M 0 2 * M 1 3 + M 0 3 * M 1 2) * (M 2 0 * M 3 1 + M 2 1 * M 3 0) := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring


def star (x y : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0, x, y, -x - y], ![x, 0, 0, 0],
    ![y, 0, 0, 0], ![-x - y, 0, 0, 0]]

def symMatrix (a b c d e f g h i j : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![a, b, c, d], ![b, e, f, g], ![c, f, h, i], ![d, g, i, j]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma tangent_at_star (a b c d e f g h i j x y : ℂ)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1:ℂ)+star x y r s+z*symMatrix a b c d e f g h i j r s)=24) :
    6 * a + 12 * b + 12 * c + 12 * d + e * x ^ 2 - 4 * e * x + 6 * e + 2 * f * x * y - 4 * f * x - 4 * f * y + 12 * f - 2 * g * x ^ 2 - 2 * g * x * y + 4 * g * y + 12 * g + h * y ^ 2 - 4 * h * y + 6 * h - 2 * i * x * y + 4 * i * x - 2 * i * y ^ 2 + 12 * i + j * x ^ 2 + 2 * j * x * y + 4 * j * x + j * y ^ 2 + 4 * j * y + 6 * j = 0 := by
  have h1 := hp 1
  have hm1 := hp (-1)
  have h2 := hp 2
  have hm2 := hp (-2)
  simp [perm4, Matrix.of_apply, star, symMatrix] at h1 hm1 h2 hm2
  linear_combination (2 / 3 : ℂ) * h1 - (2 / 3 : ℂ) * hm1 -
    (1 / 12 : ℂ) * h2 + (1 / 12 : ℂ) * hm2


set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma dense_scalar_constraints (H A U V W D E F a b c : ℂ)
    (hp : ∀ s t : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (1:ℂ)+star s (s*H) i j+t*symMatrix A U V W D E F a b c i j)=24) :
    linear0 H D E F a b c=0 ∧ linear1 H D E F a b c=0 ∧ lowerQuadratic H D E F a b c=0 := by
  have v0 := tangent_at_star A U V W D E F a b c 0 0 (by simpa using hp 0)
  have v1 := tangent_at_star A U V W D E F a b c 1 H (by simpa using hp 1)
  have vm1 := tangent_at_star A U V W D E F a b c (-1) (-H) (by simpa using hp (-1))
  have hL0 : linear0 H D E F a b c=0 := by
    dsimp [linear0]
    linear_combination (1/2:ℂ)*(v1+vm1-2*v0)
  have hL1 : linear1 H D E F a b c=0 := by
    dsimp [linear1]
    linear_combination (1/8:ℂ)*(vm1-v1)
  refine ⟨hL0,hL1,?_⟩
  have hpp := hp 1 1
  have hmp := hp (-1) 1
  have h0p := hp 0 1
  have hpm := hp 1 (-1)
  have hmm := hp (-1) (-1)
  have h0m := hp 0 (-1)
  simp [perm4,Matrix.of_apply,star,symMatrix] at hpp hmp h0p hpm hmm h0m
  dsimp [lowerQuadratic]
  linear_combination (1/4:ℂ)*(hpp+hmp-2*h0p+hpm+hmm-2*h0m)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma dense_matrix_constraints (M : Matrix (Fin 4) (Fin 4) ℂ) (h : ℂ)
    (hs : ∀ i j : Fin 4, M i j=M j i)
    (hp : ∀ s t : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (1:ℂ)+s*star 1 h i j+t*M i j)=24) :
    linear0 h (M 1 1) (M 1 2) (M 1 3) (M 2 2) (M 2 3) (M 3 3)=0 ∧
    linear1 h (M 1 1) (M 1 2) (M 1 3) (M 2 2) (M 2 3) (M 3 3)=0 ∧
    lowerQuadratic h (M 1 1) (M 1 2) (M 1 3) (M 2 2) (M 2 3) (M 3 3)=0 := by
  have hM : M=symMatrix (M 0 0) (M 0 1) (M 0 2) (M 0 3)
      (M 1 1) (M 1 2) (M 1 3) (M 2 2) (M 2 3) (M 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [symMatrix]
    all_goals exact hs _ _
  apply dense_scalar_constraints h (M 0 0) (M 0 1) (M 0 2) (M 0 3)
    (M 1 1) (M 1 2) (M 1 3) (M 2 2) (M 2 3) (M 3 3)
  intro s t
  have hz := hp s t
  rw [hM] at hz
  convert hz using 1
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.of_apply,star] <;> ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma lower_constant_zero (M : Matrix (Fin 4) (Fin 4) ℂ) (δ : ℂ)
    (hl : ∀ i j : Fin 3, M i.succ j.succ=δ)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1:ℂ)+z*M i j)=24) : δ=0 := by
  by_contra hn
  have hz := hp (-δ⁻¹)
  have he : (1:ℂ)+-(δ⁻¹*δ)=0 := by simp [hn]
  have h11 : M 1 1=δ := hl 0 0
  have h12 : M 1 2=δ := hl 0 1
  have h13 : M 1 3=δ := hl 0 2
  have h21 : M 2 1=δ := hl 1 0
  have h22 : M 2 2=δ := hl 1 1
  have h23 : M 2 3=δ := hl 1 2
  have h31 : M 3 1=δ := hl 2 0
  have h32 : M 3 2=δ := hl 2 1
  have h33 : M 3 3=δ := hl 2 2
  norm_num [perm4,Matrix.of_apply,h11,h12,h13,h21,h22,h23,h31,h32,h33,he] at hz

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma lower_zero_star (M : Matrix (Fin 4) (Fin 4) ℂ)
    (hs : ∀ i j : Fin 4, M i j=M j i)
    (hl : ∀ i j : Fin 3, M i.succ j.succ=0)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1:ℂ)+z*M i j)=24) :
    M=star (M 0 1) (M 0 2) := by
  have h11 : M 1 1=0 := hl 0 0
  have h12 : M 1 2=0 := hl 0 1
  have h13 : M 1 3=0 := hl 0 2
  have h21 : M 2 1=0 := hl 1 0
  have h22 : M 2 2=0 := hl 1 1
  have h23 : M 2 3=0 := hl 1 2
  have h31 : M 3 1=0 := hl 2 0
  have h32 : M 3 2=0 := hl 2 1
  have h33 : M 3 3=0 := hl 2 2
  have h1 := hp 1
  have hm1 := hp (-1)
  simp [perm4,Matrix.of_apply,h11,h12,h13,h21,h22,h23,h31,h32,h33,
    hs 1 0,hs 2 0,hs 3 0] at h1 hm1
  have hS2 : (M 0 1+M 0 2+M 0 3)^2=0 := by
    linear_combination (1/4:ℂ)*(h1+hm1)
  have hS : M 0 1+M 0 2+M 0 3=0 := eq_zero_of_pow_eq_zero hS2
  have hA : M 0 0=0 := by
    linear_combination (1/12:ℂ)*(h1-hm1)-2*hS
  have hW : M 0 3= -M 0 1-M 0 2 := by linear_combination hS
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [star,hA,hW,h11,h12,h13,h21,h22,h23,h31,h32,h33,hs 1 0,hs 2 0,hs 3 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma dense_matrix_kernel (M : Matrix (Fin 4) (Fin 4) ℂ) (h : ℂ)
    (hh : h≠0) (hh1 : h+1≠0) (hs : ∀ i j : Fin 4, M i j=M j i)
    (hp : ∀ s t : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (1:ℂ)+s*star 1 h i j+t*M i j)=24)
    (hX : coordX h (M 2 2) (M 2 3) (M 3 3)=0)
    (hY : coordY h (M 2 2) (M 2 3) (M 3 3)=0)
    (hK : coordK h (M 1 2) (M 1 3) (M 2 2) (M 2 3) (M 3 3)=0) :
    M=star (M 0 1) (M 0 2) := by
  obtain ⟨h0,h1,hQ⟩ := dense_matrix_constraints M h hs hp
  obtain ⟨hd,he,hf,hb,hc⟩ := radical_coordinates h (M 1 1) (M 1 2) (M 1 3)
    (M 2 2) (M 2 3) (M 3 3) hh hh1 h0 h1 hX hY hK
  have hl : ∀ i j : Fin 3, M i.succ j.succ=M 2 2 := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [hd,he,hf,hb,hc,hs 2 1,hs 3 1,hs 3 2]
  have hline : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1:ℂ)+z*M i j)=24 := by
    intro z
    simpa using hp 0 z
  have ha := lower_constant_zero M (M 2 2) hl hline
  apply lower_zero_star M hs ?_ hline
  intro i j
  exact (hl i j).trans ha

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma dense_matrix_isotropic (M : Matrix (Fin 4) (Fin 4) ℂ) (h : ℂ)
    (hs : ∀ i j : Fin 4, M i j=M j i)
    (hp : ∀ s t : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (1:ℂ)+s*star 1 h i j+t*M i j)=24) :
    quotientQuadratic h (coordX h (M 2 2) (M 2 3) (M 3 3))
      (coordY h (M 2 2) (M 2 3) (M 3 3))
      (coordK h (M 1 2) (M 1 3) (M 2 2) (M 2 3) (M 3 3))=0 := by
  obtain ⟨h0,h1,hQ⟩ := dense_matrix_constraints M h hs hp
  have he := quadratic_coordinates h (M 1 1) (M 1 2) (M 1 3)
    (M 2 2) (M 2 3) (M 3 3) h0 h1
  linear_combination (1/2:ℂ)*(hQ-he)

end PEqualNP.Outside.L_gct_231.DenseStar
