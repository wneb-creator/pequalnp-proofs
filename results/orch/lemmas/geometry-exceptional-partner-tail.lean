set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma symmetric_sum_zero (M : Matrix (Fin 4) (Fin 4) ℂ)
    (hs : ∀ i j : Fin 4, M i j=M j i)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1:ℂ)+z*M i j)=24) :
    M 0 0+M 1 1+M 2 2+M 3 3+2*(M 0 1+M 0 2+M 0 3+M 1 2+M 1 3+M 2 3)=0 := by
  have h1 := hp 1
  have hm1 := hp (-1)
  have h2 := hp 2
  have hm2 := hp (-2)
  simp [perm4,Matrix.of_apply,hs 1 0,hs 2 0,hs 3 0,hs 2 1,hs 3 1,hs 3 2] at h1 hm1 h2 hm2
  linear_combination (1/9:ℂ)*(h1-hm1)-(1/72:ℂ)*(h2-hm2)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma partner_normalization (B : Matrix (Fin 4) (Fin 4) ℂ)
    (hs : ∀ i j : Fin 4, B i j=B j i)
    (h01 : B 0 1=B 0 0) (h02 : B 0 2=B 0 0+1) (h03 : B 0 3=B 0 0)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1:ℂ)+z*B i j)=24) :
    ∃ b0 b1 b2 b3 b4 b5 : ℂ, B=partner b0 b1 b2 b3 b4 b5 := by
  have hS := symmetric_sum_zero B hs hp
  rw [h01,h02,h03] at hS
  let b0 := B 1 1-B 0 0
  let b1 := B 1 2-B 0 0
  let b2 := B 1 3-B 0 0
  let b3 := B 2 2-B 0 0
  let b4 := B 2 3-B 0 0
  let b5 := B 3 3-B 0 0
  have ha : (b0+b3+b5+2*(b1+b2+b4)+2)/16= -B 0 0 := by
    dsimp [b0,b1,b2,b3,b4,b5]
    linear_combination (1/16:ℂ)*hS
  refine ⟨b0,b1,b2,b3,b4,b5,?_⟩
  dsimp [partner]
  rw [ha]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b0,b1,b2,b3,b4,b5,h01,h02,h03,hs 1 0,hs 2 0,hs 3 0,hs 2 1,hs 3 1,hs 3 2] <;> ring
