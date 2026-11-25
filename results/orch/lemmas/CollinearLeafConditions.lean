import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination

import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin

namespace PEqualNP.Outside.L_gct_231.Overlap

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


lemma block_root (a b c : ℂ) (hS : a+c+2*b=0) (hQ : a*c+b^2=0)
    (hne : a≠0 ∨ b≠0 ∨ c≠0) :
    b≠0 ∧ ∃ h : ℂ, h^2=2 ∧ a=b*(h-1) ∧ c=b*(-h-1) := by
  have hb : b≠0 := by
    intro hb
    have ha2 : a^2=0 := by linear_combination a*hS-hQ+(b-2*a)*hb
    have ha := eq_zero_of_pow_eq_zero ha2
    have hc : c=0 := by linear_combination hS-ha-2*hb
    exact hne.elim (fun hn => hn ha) (fun hn => hn.elim (fun hn => hn hb) (fun hn => hn hc))
  have hmul : (a/b)*b=a := div_mul_cancel₀ a hb
  have haq : a^2+2*a*b-b^2=0 := by linear_combination a*hS-hQ
  refine ⟨hb,a/b+1,?_,?_,?_⟩
  · apply mul_right_cancel₀ (pow_ne_zero 2 hb)
    linear_combination (a/b*b+a+2*b)*hmul+haq
  · linear_combination -hmul
  · linear_combination hS+hmul

lemma roots_overlap_impossible (h k : ℂ) (hh : h^2=2) (hk : k^2=2)
    (hp : 1-h-k-h*k=0) : False := by
  have hl : 2*h-k-3=0 := by linear_combination (h-1)*hp+(1+k)*hh
  have ht : h-(5/4:ℂ)=0 := by
    linear_combination (1/3:ℂ)*hh-(1/12:ℂ)*hk-(1/12:ℂ)*(2*h+k-3)*hl
  have hbad : (7:ℂ)=0 := by linear_combination (16*h+20)*ht-16*hh
  norm_num at hbad

def topBlock (a b c : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![a,b,0,0],![b,c,0,0],![0,0,0,0],![0,0,0,0]]

def sideBlock (a b c : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![a,0,b,0],![0,0,0,0],![b,0,c,0],![0,0,0,0]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma normalized_overlap_impossible (h k : ℂ) (hh : h^2=2) (hk : k^2=2)
    (hp : ∀ U V : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*topBlock (h-1) 1 (-h-1) r s+V*sideBlock (k-1) 1 (-k-1) r s)=24) : False := by
  have h1 := hp 1 1
  have hm1 := hp (-1) (-1)
  have h2 := hp 2 2
  have hm2 := hp (-2) (-2)
  simp [perm4,Matrix.of_apply,topBlock,sideBlock] at h1 hm1 h2 hm2
  apply roots_overlap_impossible h k hh hk
  linear_combination (1/3:ℂ)*(h1+hm1)-(1/48:ℂ)*(h2+hm2)+hh+hk

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma overlap_blocks_impossible (a b c d e f : ℂ)
    (hA : a≠0 ∨ b≠0 ∨ c≠0) (hB : d≠0 ∨ e≠0 ∨ f≠0)
    (hp : ∀ U V : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*topBlock a b c r s+V*sideBlock d e f r s)=24) : False := by
  have hA1 := hp 1 0
  have hAm := hp (-1) 0
  have hB1 := hp 0 1
  have hBm := hp 0 (-1)
  simp [perm4,Matrix.of_apply,topBlock,sideBlock] at hA1 hAm hB1 hBm
  have hAS : a+c+2*b=0 := by linear_combination (1/12:ℂ)*(hA1-hAm)
  have hAQ : a*c+b^2=0 := by linear_combination (1/4:ℂ)*(hA1+hAm)
  have hBS : d+f+2*e=0 := by linear_combination (1/12:ℂ)*(hB1-hBm)
  have hBQ : d*f+e^2=0 := by linear_combination (1/4:ℂ)*(hB1+hBm)
  obtain ⟨hb,h,hh,ha,hc⟩ := block_root a b c hAS hAQ hA
  obtain ⟨he,k,hk,hd,hf⟩ := block_root d e f hBS hBQ hB
  apply normalized_overlap_impossible h k hh hk
  intro U V
  have hp0 := hp (U/b) (V/e)
  have heqA : topBlock a b c=Matrix.of (fun (r s : Fin 4) => b*topBlock (h-1) 1 (-h-1) r s) := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [topBlock,ha,hc] <;> ring_nf <;> simp
  have heqB : sideBlock d e f=Matrix.of (fun (r s : Fin 4) => e*sideBlock (k-1) 1 (-k-1) r s) := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [sideBlock,hd,hf] <;> ring_nf <;> simp
  rw [heqA,heqB] at hp0
  simpa only [Matrix.of_apply,← mul_assoc,div_mul_cancel₀ U hb,div_mul_cancel₀ V he] using hp0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma overlap_zero_rows_impossible (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hsA : ∀ r s : Fin 4, A r s=A s r)
    (hsB : ∀ r s : Fin 4, B r s=B s r)
    (hA2 : ∀ j : Fin 4, A 2 j=0) (hA3 : ∀ j : Fin 4, A 3 j=0)
    (hB1 : ∀ j : Fin 4, B 1 j=0) (hB3 : ∀ j : Fin 4, B 3 j=0)
    (hA : A≠0) (hB : B≠0)
    (hp : ∀ U V : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*A r s+V*B r s)=24) : False := by
  have heqA : A=topBlock (A 0 0) (A 0 1) (A 1 1) := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [topBlock,hA2,hA3,hsA 0 2,hsA 0 3,hsA 1 2,hsA 1 3,hsA 1 0]
  have heqB : B=sideBlock (B 0 0) (B 0 2) (B 2 2) := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [sideBlock,hB1,hB3,hsB 0 1,hsB 0 3,hsB 2 1,hsB 2 3,hsB 2 0]
  have hAne : A 0 0≠0 ∨ A 0 1≠0 ∨ A 1 1≠0 := by
    by_contra hn
    have ha : A 0 0=0 := Classical.not_not.mp (fun h => hn (Or.inl h))
    have hb : A 0 1=0 := Classical.not_not.mp (fun h => hn (Or.inr (Or.inl h)))
    have hc : A 1 1=0 := Classical.not_not.mp (fun h => hn (Or.inr (Or.inr h)))
    apply hA
    apply heqA.trans
    ext r s
    fin_cases r <;> fin_cases s <;> simp [topBlock,ha,hb,hc]
  have hBne : B 0 0≠0 ∨ B 0 2≠0 ∨ B 2 2≠0 := by
    by_contra hn
    have ha : B 0 0=0 := Classical.not_not.mp (fun h => hn (Or.inl h))
    have hb : B 0 2=0 := Classical.not_not.mp (fun h => hn (Or.inr (Or.inl h)))
    have hc : B 2 2=0 := Classical.not_not.mp (fun h => hn (Or.inr (Or.inr h)))
    apply hB
    apply heqB.trans
    ext r s
    fin_cases r <;> fin_cases s <;> simp [sideBlock,ha,hb,hc]
  apply overlap_blocks_impossible (A 0 0) (A 0 1) (A 1 1)
    (B 0 0) (B 0 2) (B 2 2) hAne hBne
  intro U V
  have hc := hp U V
  rw [heqA,heqB] at hc
  exact hc

lemma submatrix_ne_zero (M : Matrix (Fin 4) (Fin 4) ℂ)
    (hM : M≠0) (σ : Equiv.Perm (Fin 4)) : M.submatrix σ σ≠0 := by
  intro hz
  apply hM
  ext r s
  have he := congrArg (fun N : Matrix (Fin 4) (Fin 4) ℂ => N (σ.symm r) (σ.symm s)) hz
  simpa only [Matrix.submatrix_apply,Equiv.apply_symm_apply,Matrix.zero_apply] using he

lemma permanent_pair_reindex (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hp : ∀ U V : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*A r s+V*B r s)=24) (σ : Equiv.Perm (Fin 4)) :
    ∀ U V : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*(A.submatrix σ σ) r s+V*(B.submatrix σ σ) r s)=24 := by
  intro U V
  let M : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun r s => (1 : ℂ)+U*A r s+V*B r s
  change Matrix.permanent (M.submatrix σ σ)=24
  have he : Matrix.permanent (M.submatrix σ σ)=Matrix.permanent M := by
    change Matrix.permanent ((M.submatrix σ id).submatrix id σ)=Matrix.permanent M
    rw [Matrix.permanent_permute_rows,Matrix.permanent_permute_cols]
  exact he.trans (hp U V)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma three_collinear_leaf_rows (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hsA : ∀ r s : Fin 4, A r s=A s r)
    (hsB : ∀ r s : Fin 4, B r s=B s r)
    (hA0 : ∀ j : Fin 4, A 0 j=0) (hB1 : ∀ j : Fin 4, B 1 j=0)
    (hAB2 : ∀ j : Fin 4, A 2 j+B 2 j=0)
    (hA : A≠0) (hB : B≠0) (hAB : A+B≠0)
    (hp : ∀ U V : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*A r s+V*B r s)=24) :
    (∃ j : Fin 4, B 0 j≠0) ∧ (∃ j : Fin 4, A 1 j≠0) ∧ (∃ j : Fin 4, A 2 j≠0) := by
  have hsAB (r s : Fin 4) : (A+B) r s=(A+B) s r :=
    congrArg₂ (·+·) (hsA r s) (hsB r s)
  have hpAS (U V : ℂ) : Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*A r s+V*(A+B) r s)=24 := by
    convert hp (U+V) V using 1
    congr 1
    ext r s
    simp only [Matrix.of_apply,Matrix.add_apply]
    ring
  have hpBS (U V : ℂ) : Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*B r s+V*(A+B) r s)=24 := by
    convert hp V (U+V) using 1
    congr 1
    ext r s
    simp only [Matrix.of_apply,Matrix.add_apply]
    ring
  constructor
  · by_contra hn
    have hB0 (j : Fin 4) : B 0 j=0 := Classical.not_not.mp ((not_exists.mp hn) j)
    have hS0 (j : Fin 4) : (A+B) 0 j=0 := by simp [Matrix.add_apply,hA0,hB0]
    let σ : Equiv.Perm (Fin 4) :=
      { toFun := ![3,2,1,0], invFun := ![3,2,1,0], left_inv := by decide, right_inv := by decide }
    apply overlap_zero_rows_impossible (B.submatrix σ σ) ((A+B).submatrix σ σ)
      (fun r s => hsB (σ r) (σ s)) (fun r s => hsAB (σ r) (σ s))
      _ _ _ _ (submatrix_ne_zero B hB σ) (submatrix_ne_zero (A+B) hAB σ)
      (permanent_pair_reindex B (A+B) hpBS σ)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hB1 (σ j)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hB0 (σ j)
    · intro j
      simpa [σ,Matrix.submatrix_apply,Matrix.add_apply] using hAB2 (σ j)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hS0 (σ j)
  constructor
  · by_contra hn
    have hA1 (j : Fin 4) : A 1 j=0 := Classical.not_not.mp ((not_exists.mp hn) j)
    have hS1 (j : Fin 4) : (A+B) 1 j=0 := by simp [Matrix.add_apply,hA1,hB1]
    let σ : Equiv.Perm (Fin 4) :=
      { toFun := ![3,2,0,1], invFun := ![2,3,1,0], left_inv := by decide, right_inv := by decide }
    apply overlap_zero_rows_impossible (A.submatrix σ σ) ((A+B).submatrix σ σ)
      (fun r s => hsA (σ r) (σ s)) (fun r s => hsAB (σ r) (σ s))
      _ _ _ _ (submatrix_ne_zero A hA σ) (submatrix_ne_zero (A+B) hAB σ)
      (permanent_pair_reindex A (A+B) hpAS σ)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hA0 (σ j)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hA1 (σ j)
    · intro j
      simpa [σ,Matrix.submatrix_apply,Matrix.add_apply] using hAB2 (σ j)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hS1 (σ j)
  · by_contra hn
    have hA2 (j : Fin 4) : A 2 j=0 := Classical.not_not.mp ((not_exists.mp hn) j)
    have hB2 (j : Fin 4) : B 2 j=0 := by simpa only [hA2,zero_add] using hAB2 j
    let σ : Equiv.Perm (Fin 4) :=
      { toFun := ![3,1,0,2], invFun := ![2,1,3,0], left_inv := by decide, right_inv := by decide }
    apply overlap_zero_rows_impossible (A.submatrix σ σ) (B.submatrix σ σ)
      (fun r s => hsA (σ r) (σ s)) (fun r s => hsB (σ r) (σ s))
      _ _ _ _ (submatrix_ne_zero A hA σ) (submatrix_ne_zero B hB σ)
      (permanent_pair_reindex A B hp σ)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hA0 (σ j)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hA2 (σ j)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hB1 (σ j)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hB2 (σ j)

end PEqualNP.Outside.L_gct_231.Overlap
