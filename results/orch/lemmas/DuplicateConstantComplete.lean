import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

def duplicateRowPolynomial (a b c d e f : ℂ) : ℂ :=
  2*a^2*(d*f+e^2)+8*a*b*c*e+4*a*(b^2*f+c^2*d)+4*b^2*c^2

def duplicateRowMatrix (a b c d e f : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![a,a,b,c; a,a,b,c; b,b,d,e; c,c,e,f]

def duplicateRowMap : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun v p := duplicateRowMatrix (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) p.1 p.2
  map_add' v w := by
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> rfl
  map_smul' z v := by
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> rfl

lemma duplicateRowMap_injective : Function.Injective duplicateRowMap := by
  intro v w h
  have h00 := congrArg (fun V => V (0,0)) h
  have h02 := congrArg (fun V => V (0,2)) h
  have h03 := congrArg (fun V => V (0,3)) h
  have h22 := congrArg (fun V => V (2,2)) h
  have h23 := congrArg (fun V => V (2,3)) h
  have h33 := congrArg (fun V => V (3,3)) h
  funext i
  fin_cases i
  · exact h00
  · exact h02
  · exact h03
  · exact h22
  · exact h23
  · exact h33

lemma permanent_duplicateRow (a b c d e f : ℂ) :
    Matrix.permanent (duplicateRowMatrix a b c d e f) =
      duplicateRowPolynomial a b c d e f := by
  rw [permanent_four]
  simp [duplicateRowMatrix, duplicateRowPolynomial]
  ring

lemma permanent_duplicateRowMap (v : Fin 6 → ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (1 : ℂ) + duplicateRowMap v (i,j)) =
      duplicateRowPolynomial (1+v 0) (1+v 1) (1+v 2)
        (1+v 3) (1+v 4) (1+v 5) := by
  rw [permanent_four]
  simp [duplicateRowMap, duplicateRowMatrix, duplicateRowPolynomial]
  ring

lemma quartic_all_coefficients (a b c d : ℂ)
    (h : ∀ z : ℂ, a*z+b*z^2+c*z^3+d*z^4 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  obtain ⟨ha,hb⟩ := quartic_first_coefficients a b c d h
  have h1 := h 1
  have hn := h (-1)
  refine ⟨ha,hb,?_,?_⟩
  · linear_combination (1/2:ℂ)*h1-(1/2:ℂ)*hn-ha
  · linear_combination (1/2:ℂ)*h1+(1/2:ℂ)*hn-hb

lemma coordinate_product_zero_split (W : Submodule ℂ (Fin 6 → ℂ)) (i j : Fin 6)
    (h : ∀ v ∈ W, v i * v j = 0) :
    (∀ v ∈ W, v i = 0) ∨ (∀ v ∈ W, v j = 0) := by
  classical
  by_cases hi : ∀ v ∈ W, v i = 0
  · exact Or.inl hi
  · push Not at hi
    obtain ⟨u, hu, hui⟩ := hi
    have huj := (mul_eq_zero.mp (h u hu)).resolve_left hui
    right
    intro v hv
    by_cases hvi : v i = 0
    · have huv := h (u + v) (W.add_mem hu hv)
      simp only [Pi.add_apply, hvi, huj, add_zero, zero_add] at huv
      exact (mul_eq_zero.mp huv).resolve_left hui
    · exact (mul_eq_zero.mp (h v hv)).resolve_left hvi

lemma finrank_le_one_of_coordinate_kernel (W : Submodule ℂ (Fin 6 → ℂ)) (i : Fin 6)
    (hk : ∀ v ∈ W, v i = 0 → v = 0) : Module.finrank ℂ W ≤ 1 := by
  let F : W →ₗ[ℂ] ℂ :=
    { toFun := fun v => v.val i
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hker : ∀ v : W, F v = 0 → v = 0 := by
    intro v hv
    apply Subtype.ext
    exact hk v.val v.property hv
  have hF : Function.Injective F := by
    intro v w h
    apply sub_eq_zero.mp
    apply hker (v - w)
    rw [map_sub, h, sub_self]
  have hd := Submodule.finrank_le (LinearMap.range F)
  rw [LinearMap.finrank_range_of_inj hF] at hd
  simpa using hd

lemma duplicate_constant_quartic (b c d e f : ℂ)
    (hp : ∀ z : ℂ, duplicateRowPolynomial 1 (1+z*b) (1+z*c)
      (1+z*d) (1+z*e) (1+z*f) = 24) : b*c = 0 := by
  have h1 := hp 1
  have hm1 := hp (-1)
  have h2 := hp 2
  have hm2 := hp (-2)
  dsimp [duplicateRowPolynomial] at h1 hm1 h2 hm2
  have hsq : (b*c)^2 = 0 := by
    linear_combination h2/96 + hm2/96 - h1/24 - hm1/24
  by_contra hne
  exact (mul_ne_zero hne hne) (by simpa only [pow_two] using hsq)

lemma duplicate_constant_left_cubic (c d e f : ℂ)
    (hp : ∀ z : ℂ, duplicateRowPolynomial 1 1 (1+z*c)
      (1+z*d) (1+z*e) (1+z*f) = 24) : c*d = 0 := by
  have h1 := hp 1
  have hm1 := hp (-1)
  have h2 := hp 2
  have hm2 := hp (-2)
  dsimp [duplicateRowPolynomial] at h1 hm1 h2 hm2
  have hcube : c^2*d = 0 := by
    linear_combination h2/48 - hm2/48 - h1/24 + hm1/24
  rcases mul_eq_zero.mp hcube with hc | hd
  · have hc0 : c = 0 := by
      by_contra hne
      exact (mul_ne_zero hne hne) (by simpa only [pow_two] using hc)
    simp [hc0]
  · simp [hd]

lemma duplicate_constant_right_cubic (b d e f : ℂ)
    (hp : ∀ z : ℂ, duplicateRowPolynomial 1 (1+z*b) 1
      (1+z*d) (1+z*e) (1+z*f) = 24) : b*f = 0 := by
  apply duplicate_constant_left_cubic b f e d
  intro z
  have hz := hp z
  dsimp [duplicateRowPolynomial] at hz ⊢
  linear_combination hz

lemma duplicate_constant_block_finrank_le_one
    (W : Submodule ℂ (Fin 6 → ℂ))
    (hp : ∀ v ∈ W, duplicateRowPolynomial (1+v 0) (1+v 1) (1+v 2)
      (1+v 3) (1+v 4) (1+v 5) = 24)
    (ha : ∀ v ∈ W, v 0 = 0) : Module.finrank ℂ W ≤ 1 := by
  have hs (v : Fin 6 → ℂ) (hv : v ∈ W) (z : ℂ) :
      duplicateRowPolynomial 1 (1+z*v 1) (1+z*v 2)
        (1+z*v 3) (1+z*v 4) (1+z*v 5) = 24 := by
    have hz := hp (z • v) (W.smul_mem z hv)
    simpa only [Pi.smul_apply, smul_eq_mul, ha v hv, mul_zero, add_zero] using hz
  have hbc : (∀ v ∈ W, v 1 = 0) ∨ (∀ v ∈ W, v 2 = 0) := by
    apply coordinate_product_zero_split W 1 2
    intro v hv
    exact duplicate_constant_quartic _ _ _ _ _ (hs v hv)
  have hboth (hb : ∀ v ∈ W, v 1 = 0) (hc : ∀ v ∈ W, v 2 = 0) :
      Module.finrank ℂ W ≤ 1 := by
    apply finrank_le_one_of_coordinate_kernel W 4
    intro v hv he
    have h1 := hs v hv 1
    have hm1 := hs v hv (-1)
    simp only [hb v hv, hc v hv, he, mul_zero, add_zero] at h1 hm1
    dsimp [duplicateRowPolynomial] at h1 hm1
    have hlin : v 3 + v 5 = 0 := by linear_combination h1/12 - hm1/12
    have hquad : v 3 * v 5 = 0 := by linear_combination h1/4 + hm1/4
    have hd : v 3 = 0 := by
      have hsq : (v 3)^2 = 0 := by linear_combination v 3*hlin - hquad
      by_contra hne
      exact (mul_ne_zero hne hne) (by simpa only [pow_two] using hsq)
    have hf : v 5 = 0 := by linear_combination hlin - hd
    funext i
    fin_cases i <;> simp [ha v hv, hb v hv, hc v hv, hd, he, hf]
  have hleft (hb : ∀ v ∈ W, v 1 = 0) (hd : ∀ v ∈ W, v 3 = 0) :
      Module.finrank ℂ W ≤ 1 := by
    apply finrank_le_one_of_coordinate_kernel W 2
    intro v hv hc
    have h1 := hs v hv 1
    have hm1 := hs v hv (-1)
    simp only [hb v hv, hd v hv, hc, mul_zero, add_zero] at h1 hm1
    dsimp [duplicateRowPolynomial] at h1 hm1
    have he : v 4 = 0 := by
      have hsq : (v 4)^2 = 0 := by linear_combination h1/4 + hm1/4
      by_contra hne
      exact (mul_ne_zero hne hne) (by simpa only [pow_two] using hsq)
    have hf : v 5 = 0 := by linear_combination h1/12 - hm1/12 - 2*he
    funext i
    fin_cases i <;> simp [ha v hv, hb v hv, hc, hd v hv, he, hf]
  have hright (hc : ∀ v ∈ W, v 2 = 0) (hf : ∀ v ∈ W, v 5 = 0) :
      Module.finrank ℂ W ≤ 1 := by
    apply finrank_le_one_of_coordinate_kernel W 1
    intro v hv hb
    have h1 := hs v hv 1
    have hm1 := hs v hv (-1)
    simp only [hc v hv, hf v hv, hb, mul_zero, add_zero] at h1 hm1
    dsimp [duplicateRowPolynomial] at h1 hm1
    have he : v 4 = 0 := by
      have hsq : (v 4)^2 = 0 := by linear_combination h1/4 + hm1/4
      by_contra hne
      exact (mul_ne_zero hne hne) (by simpa only [pow_two] using hsq)
    have hd : v 3 = 0 := by linear_combination h1/12 - hm1/12 - 2*he
    funext i
    fin_cases i <;> simp [ha v hv, hb, hc v hv, hd, he, hf v hv]
  rcases hbc with hb | hc
  · have hcd : (∀ v ∈ W, v 2 = 0) ∨ (∀ v ∈ W, v 3 = 0) := by
      apply coordinate_product_zero_split W 2 3
      intro v hv
      apply duplicate_constant_left_cubic (v 2) (v 3) (v 4) (v 5)
      intro z
      simpa only [hb v hv, mul_zero, add_zero] using hs v hv z
    exact hcd.elim (hboth hb) (hleft hb)
  · have hbf : (∀ v ∈ W, v 1 = 0) ∨ (∀ v ∈ W, v 5 = 0) := by
      apply coordinate_product_zero_split W 1 5
      intro v hv
      apply duplicate_constant_right_cubic (v 1) (v 3) (v 4) (v 5)
      intro z
      simpa only [hc v hv, mul_zero, add_zero] using hs v hv z
    exact hbf.elim (fun hb => hboth hb hc) (hright hc)

end PEqualNP.Outside.L_gct_231
