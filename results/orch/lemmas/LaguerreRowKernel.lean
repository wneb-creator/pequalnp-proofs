import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin

import Mathlib.Algebra.Module.Submodule.Basic

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

namespace PEqualNP.Outside.L_gct_231.LaguerreRowKernel

lemma zero_iff (a η : ℂ)
    (h : a^4-16*η*a^3+72*η^2*a^2-96*η^3*a+24*η^4=0) :
    a=0 ↔ η=0 := by
  constructor
  · intro ha
    rw [ha] at h
    norm_num at h
    exact h
  · intro hη
    rw [hη] at h
    norm_num at h
    exact h

lemma proportional_on_submodule {V : Type*} [AddCommGroup V] [Module ℂ V]
    (K : Submodule ℂ V) (d e : V →ₗ[ℂ] ℂ) (w : V) (hw : w∈K) (hew : e w=1)
    (h : ∀ v∈K, (d v)^4-16*(e v)*(d v)^3+72*(e v)^2*(d v)^2-
      96*(e v)^3*(d v)+24*(e v)^4=0) :
    (d w)^4-16*(d w)^3+72*(d w)^2-96*(d w)+24=0 ∧
      ∀ v∈K, d v=(d w)*(e v) := by
  constructor
  · simpa [hew] using h w hw
  · intro v hv
    have hvw : v-(e v) • w ∈ K := K.sub_mem hv (K.smul_mem (e v) hw)
    have hz : e (v-(e v) • w)=0 := by simp [hew]
    have hd := (zero_iff (d (v-(e v) • w)) (e (v-(e v) • w)) (h _ hvw)).mpr hz
    simp only [map_sub, map_smul, smul_eq_mul] at hd
    linear_combination hd

lemma actual_zero_iff (M : Matrix (Fin 4) (Fin 4) ℂ) (η : ℂ)
    (hr : ∀ i : Fin 3, M 0 i.succ=0) (hc : ∀ i : Fin 3, M i.succ 0=0)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (u v : Fin 4) => M u v+z)=24*(η+z)^4) :
    M 0 0=0 ↔ η=0 :=
  zero_iff _ _ (LaguerreBlock.laguerre_zero_off_row M η hr hc hp)


lemma row_difference_kernel_iff (T : Matrix (Fin 4) (Fin 4) ℂ)
    (hs : ∀ i j, T i j=T j i)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (u v : Fin 4) => T u v+z)=24*z^4) :
    (∀ j : Fin 4, T 0 j=T 0 0) ↔ (∀ j : Fin 3, T 0 j.succ=0) := by
  constructor
  · intro hr
    let N : Matrix (Fin 4) (Fin 4) ℂ := fun u v => T u v-T 0 0
    have hNr : ∀ j : Fin 3, N 0 j.succ=0 := by intro j; simp [N,hr]
    have hNc : ∀ j : Fin 3, N j.succ 0=0 := by intro j; simp [N,hs j.succ 0,hr]
    have hNp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (u v : Fin 4) => N u v+z)=24*(-T 0 0+z)^4 := by
      intro z
      have hM : (Matrix.of fun (u v : Fin 4) => N u v+z)=
          (Matrix.of fun (u v : Fin 4) => T u v+(z-T 0 0)) := by
        ext u v
        simp only [Matrix.of_apply,N]
        ring
      rw [hM,hp]
      ring
    have hz : T 0 0=0 := neg_eq_zero.mp ((actual_zero_iff N (-T 0 0) hNr hNc hNp).mp (by simp [N]))
    intro j
    rw [hr,hz]
  · intro hr
    have hc : ∀ j : Fin 3, T j.succ 0=0 := by intro j; rw [hs,hr]
    have hdiag : T 0 0=0 := (actual_zero_iff T 0 hr hc (by simpa using hp)).mpr rfl
    intro j
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k,rfl⟩
    · rfl
    · rw [hr,hdiag]

end PEqualNP.Outside.L_gct_231.LaguerreRowKernel
