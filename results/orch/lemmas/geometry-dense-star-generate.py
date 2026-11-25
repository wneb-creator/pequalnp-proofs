from pathlib import Path
j=Path('/tmp/oec/pequalnp-pilot-79');repo=Path('/workspace/pequalnp-proofs/results/orch/lemmas');old=(repo/'StarMaximal.lean').read_text();coord=(j/'DenseStarCoordinates.lean').read_text();base=coord[:coord.rindex('end PEqualNP.Outside.L_gct_231.DenseStar')];imports=['import Mathlib.LinearAlgebra.Matrix.Permanent','import Mathlib.LinearAlgebra.Matrix.Notation','import Mathlib.GroupTheory.Perm.Fin','import Mathlib.Tactic.FinCases','import Mathlib.Tactic.FieldSimp'];base='\n'.join(imports)+'\n'+base
helpers=old[old.index('lemma sum_perm_succ'):old.index('lemma first_order')];fo=old[old.index('lemma first_order'):old.index('lemma maximal_coordinates')];marker=') (x y : ℂ) :\n';target=fo[fo.index(marker)+len(marker):];target=target.replace('hp x y 1','hp 1').replace('hp x y (-1)','hp (-1)').replace('hp x y 2','hp 2').replace('hp x y (-2)','hp (-2)')
tangent='''set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma tangent_at_star (a b c d e f g h i j x y : ℂ)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1:ℂ)+star x y r s+z*symMatrix a b c d e f g h i j r s)=24) :
'''+target
rest=r'''
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
'''
out=base+helpers+tangent+rest;(j/'DenseStarMatrixConstraints.lean').write_text(out.rstrip()+'\n');print('Prepared dense-star actual q/kernel bridge',len(out.encode()))
