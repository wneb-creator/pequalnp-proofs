import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin

namespace PEqualNP.Outside.L_gct_231.LaguerreBlock

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




set_option maxHeartbeats 0 in
lemma laguerre_from_coefficients (a η b c d : ℂ)
    (h3 : 6*a+3*b-96*η=0) (h2 : a*b+2*c-144*η^2=0)
    (h1 : a*c+d-96*η^3=0) (h0 : a*d-24*η^4=0) :
    a^4-16*η*a^3+72*η^2*a^2-96*η^3*a+24*η^4=0 := by
  linear_combination (a^3/6)*h3-(a^2/2)*h2+a*h1-h0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma laguerre_from_polynomial (a η b c d : ℂ)
    (hp : ∀ z : ℂ, (a+z)*(6*z^3+b*z^2+c*z+d)+z^2*(18*z^2+2*b*z+c)=24*(η+z)^4) :
    a^4-16*η*a^3+72*η^2*a^2-96*η^3*a+24*η^4=0 := by
  have h0 := hp 0
  have h1 := hp 1
  have hn1 := hp (-1)
  have h2 := hp 2
  have e3 : 6*a+3*b-96*η=0 := by
    linear_combination (1/6:ℂ)*(h2-3*h1-hn1+3*h0)
  have e2 : a*b+2*c-144*η^2=0 := by
    linear_combination (1/2:ℂ)*(h1+hn1-2*h0)
  have e1 : a*c+d-96*η^3=0 := by
    linear_combination (1/2:ℂ)*(h1-hn1)-e3
  have e0 : a*d-24*η^4=0 := by
    linear_combination h0
  exact laguerre_from_coefficients a η b c d e3 e2 e1 e0

noncomputable def blockMatrix (a b c d e f g h i j : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![a,0,0,0],![0,b,c,d],![0,e,f,g],![0,h,i,j]]

noncomputable def smallPermanent (b c d e f g h i j : ℂ) : ℂ :=
  b*f*j+b*g*i+c*e*j+c*g*h+d*e*i+d*f*h

noncomputable def smallMinorSum (b c d e f g h i j : ℂ) : ℂ :=
  (b*f+c*e)+(b*g+d*e)+(c*g+d*f)+(b*i+c*h)+(b*j+d*h)+
    (c*j+d*i)+(e*i+f*h)+(e*j+g*h)+(f*j+g*i)

noncomputable def smallEntrySum (b c d e f g h i j : ℂ) : ℂ := b+c+d+e+f+g+h+i+j

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma permanent_block (a b c d e f g h i j z : ℂ) :
    Matrix.permanent (Matrix.of fun (u v : Fin 4) => blockMatrix a b c d e f g h i j u v+z)=
      (a+z)*(6*z^3+2*smallEntrySum b c d e f g h i j*z^2+
        smallMinorSum b c d e f g h i j*z+smallPermanent b c d e f g h i j)+
      z^2*(18*z^2+4*smallEntrySum b c d e f g h i j*z+smallMinorSum b c d e f g h i j) := by
  simp [perm4,Matrix.of_apply,blockMatrix,smallEntrySum,smallMinorSum,smallPermanent]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma laguerre_block (a η b c d e f g h i j : ℂ)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (u v : Fin 4) =>
      blockMatrix a b c d e f g h i j u v+z)=24*(η+z)^4) :
    a^4-16*η*a^3+72*η^2*a^2-96*η^3*a+24*η^4=0 := by
  apply laguerre_from_polynomial a η (2*smallEntrySum b c d e f g h i j)
    (smallMinorSum b c d e f g h i j) (smallPermanent b c d e f g h i j)
  intro z
  have hz := hp z
  rw [permanent_block] at hz
  convert hz using 1 <;> ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma laguerre_zero_off_row (M : Matrix (Fin 4) (Fin 4) ℂ) (η : ℂ)
    (hr : ∀ i : Fin 3, M 0 i.succ=0) (hc : ∀ i : Fin 3, M i.succ 0=0)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (u v : Fin 4) => M u v+z)=24*(η+z)^4) :
    (M 0 0)^4-16*η*(M 0 0)^3+72*η^2*(M 0 0)^2-96*η^3*(M 0 0)+24*η^4=0 := by
  have hM : M=blockMatrix (M 0 0) (M 1 1) (M 1 2) (M 1 3)
      (M 2 1) (M 2 2) (M 2 3) (M 3 1) (M 3 2) (M 3 3) := by
    ext u v
    fin_cases u <;> fin_cases v <;> simp [blockMatrix]
    all_goals first | exact hr 0 | exact hr 1 | exact hr 2 | exact hc 0 | exact hc 1 | exact hc 2
  apply laguerre_block (M 0 0) η (M 1 1) (M 1 2) (M 1 3)
    (M 2 1) (M 2 2) (M 2 3) (M 3 1) (M 3 2) (M 3 3)
  intro z
  have hz := hp z
  rw [hM] at hz
  exact hz

end PEqualNP.Outside.L_gct_231.LaguerreBlock
