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

set_option maxHeartbeats 1600000 in
lemma duplicate_normalized_pair_impossible (B C D E F r : ℂ) (hr : r^2 = 2)
    (hp : ∀ z h : ℂ, duplicateRowPolynomial (1+z) (1+B*z) (1+C*z)
      (1+D*z+(r-1)*h) (1+E*z+h) (1+F*z+(-r-1)*h) = 24) : False := by
  let q1 := 6*(4*B+4*C+D+2*E+F+4)
  let q2 := 2*(4*B^2+12*B*C+4*B*E+4*B*F+8*B+4*C^2+4*C*D+
    4*C*E+8*C+D*F+4*D+E^2+8*E+4*F+2)
  let q3 := 2*(4*B^2*C+2*B^2*F+2*B^2+4*B*C^2+4*B*C*E+4*B*C+
    4*B*E+4*B*F+2*C^2*D+2*C^2+4*C*D+4*C*E+2*D*F+D+2*E^2+2*E+F)
  have hz : ∀ z : ℂ, q1*z+q2*z^2+q3*z^3+
      duplicateRowPolynomial 1 B C D E F*z^4 = 0 := by
    intro z
    have h := hp z 0
    dsimp [q1,q2,q3,duplicateRowPolynomial] at *
    linear_combination h
  obtain ⟨h1,h2,h3,_⟩ := quartic_all_coefficients _ _ _ _ hz
  let l1 := -2*(4*B*r-4*C*r+D*r+D-2*E-F*r+F)
  let l2 := -4*(B^2*r+B^2-2*B*C+2*B*r-C^2*r+C^2-2*C*r+
    D*r+D-2*E-F*r+F)
  let l3 := -2*(2*B^2*r+2*B^2-4*B*C-2*C^2*r+2*C^2+D*r+D-2*E-F*r+F)
  have hl : ∀ z : ℂ, l1*z+l2*z^2+l3*z^3+0*z^4 = 0 := by
    intro z
    have hp1 := hp z 1
    have hpn := hp z (-1)
    dsimp [l1,l2,l3,duplicateRowPolynomial] at *
    linear_combination (1/2:ℂ)*hp1-(1/2:ℂ)*hpn
  obtain ⟨hl1,hl2,_⟩ := quartic_all_coefficients _ _ _ _ hl
  dsimp [q1,q2,q3] at h1 h2 h3
  dsimp [l1,l2] at hl1 hl2
  have hd : D = r-2+(r-4)*B+r*C+(r-1)*E := by
    linear_combination (2-r)/24*h1-r/8*hl1-(4*B-4*C+D-F)/4*hr
  have hf : F = -2-r-r*B-(4+r)*C-(r+1)*E := by
    linear_combination (2+r)/24*h1+r/8*hl1+(4*B-4*C+D-F)/4*hr
  subst D
  subst F
  have hsplit : (B-C)*((r+1)*B+(r-1)*C-2*r) = 0 := by
    linear_combination -(1/4:ℂ)*hl2-2*(B+C+E+1)*hr
  rcases mul_eq_zero.mp hsplit with heq | hother
  · have hCB : C = B := by linear_combination -heq
    subst C
    have hQ : B^2+6*B+3 = 0 := by
      linear_combination -(1/8:ℂ)*h2-(1/4:ℂ)*(2*B+E+1)^2*hr
    have hC : B*(B+1)^2 = 0 := by
      linear_combination -(1/16:ℂ)*h3-(1/4:ℂ)*(2*B+E+1)^2*hr
    have hbad : (6:ℂ) = 0 := by
      linear_combination (11*B^2+16*B+2)*hQ-(11*B+60)*hC
    norm_num at hbad
  · have hCB : C = 4+2*r-(3+2*r)*B := by
      linear_combination (r+1)*hother-(B+C-2)*hr
    subst C
    let Q := 5*B^2+(-18+8*r)*B-17+12*r
    let T := (B-r)*(5*B^2+(-14+4*r)*B-3+4*r)
    let X := 4*B^2*r^2+8*B^2*r-4*B^2-4*B*E*r-4*B*E-8*B*r^2-
      28*B*r+60*B+E^2+4*E*r+10*E+4*r^2+20*r+113
    let Y := 8*B^3*r^2+32*B^3*r+64*B^3-4*B^2*E*r-8*B^2*E-
      20*B^2*r^2-100*B^2*r-184*B^2+4*B*E*r+12*B*E+16*B*r^2+
      172*B*r-44*B+E^2+2*E-4*r^2+56*r-3
    have hQraw : (16*r+24)*Q = 0 := by
      dsimp [Q,X]
      linear_combination h2+2*X*hr
    have hTraw : (-80*r-112)*T = 0 := by
      dsimp [T,Y]
      linear_combination h3+4*Y*hr
    have hQ : Q = 0 := by
      linear_combination (3-2*r)/8*hQraw+4*Q*hr
    have hT : T = 0 := by
      linear_combination -(5*r-7)/16*hTraw-25*T*hr
    have hbad : (318:ℂ) = 0 := by
      dsimp [Q,T] at hQ hT
      linear_combination
        ((3485+2460*r)*B^2-(6032+4250*r)*B+1848+1324*r)*hQ-
        ((3485+2460*r)*B+36+55*r)*hT-
        (22140*B^3+9840*B^2*r-34765*B^2+10060*B*r-34694*B+220*r+15867)*hr
    norm_num at hbad

set_option maxHeartbeats 800000 in
lemma duplicate_normalized_first_kernel_zero (v w : Fin 6 → ℂ)
    (hv0 : v 0 = 1) (hw0 : w 0 = 0)
    (hp : ∀ z h : ℂ, duplicateRowPolynomial
      (1+z*v 0+h*w 0) (1+z*v 1+h*w 1) (1+z*v 2+h*w 2)
      (1+z*v 3+h*w 3) (1+z*v 4+h*w 4) (1+z*v 5+h*w 5) = 24) :
    w = 0 := by
  have hw1 : w 1 = 0 := by
    by_contra hne
    have h := hp (-1) ((v 1-1)/w 1)
    have hzero : 1+(-1)*v 1+((v 1-1)/w 1)*w 1 = 0 := by
      field_simp
      ring
    rw [hzero] at h
    norm_num [hv0,hw0,duplicateRowPolynomial] at h
  have hw2 : w 2 = 0 := by
    by_contra hne
    have h := hp (-1) ((v 2-1)/w 2)
    have hzero : 1+(-1)*v 2+((v 2-1)/w 2)*w 2 = 0 := by
      field_simp
      ring
    rw [hzero] at h
    norm_num [hv0,hw0,duplicateRowPolynomial] at h
  have h1 := hp 0 1
  have hn := hp 0 (-1)
  simp only [zero_mul,add_zero,hw0,hw1,hw2,mul_zero] at h1 hn
  dsimp [duplicateRowPolynomial] at h1 hn
  have hlin : w 3+2*w 4+w 5 = 0 := by
    linear_combination h1/12-hn/12
  have hquad : w 3*w 5+(w 4)^2 = 0 := by
    linear_combination h1/4+hn/4
  by_cases hw4 : w 4 = 0
  · have hsq : (w 3)^2 = 0 := by
      linear_combination w 3*hlin-hquad+(w 4-2*w 3)*hw4
    have hw3 : w 3 = 0 := eq_zero_of_pow_eq_zero hsq
    have hw5 : w 5 = 0 := by linear_combination hlin-hw3-2*hw4
    funext i
    fin_cases i <;> simp [hw0,hw1,hw2,hw3,hw4,hw5]
  · let r := w 3/w 4+1
    have hr : r^2 = 2 := by
      dsimp [r]
      field_simp
      linear_combination w 3*hlin-hquad
    have hratio : w 5/w 4 = -r-1 := by
      dsimp [r]
      field_simp
      linear_combination hlin
    exfalso
    apply duplicate_normalized_pair_impossible (v 1) (v 2) (v 3) (v 4) (v 5) r hr
    intro z h
    have hh := hp z (h/w 4)
    simp only [hv0,hw0,hw1,hw2,mul_one,mul_zero,add_zero] at hh
    have hd : h/w 4*w 3 = (r-1)*h := by dsimp [r]; ring
    have he : h/w 4*w 4 = h := by field_simp
    have hf : h/w 4*w 5 = (-r-1)*h := by
      rw [← hratio]
      ring
    rw [hd,he,hf] at hh
    simpa only [mul_comm] using hh

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

lemma duplicate_row_flat_finrank_le_one
    (W : Submodule ℂ (Fin 6 → ℂ))
    (hp : ∀ v ∈ W, duplicateRowPolynomial (1+v 0) (1+v 1) (1+v 2)
      (1+v 3) (1+v 4) (1+v 5) = 24) : Module.finrank ℂ W ≤ 1 := by
  classical
  by_cases ha : ∀ v ∈ W, v 0 = 0
  · exact duplicate_constant_block_finrank_le_one W hp ha
  · push Not at ha
    obtain ⟨v,hv,hv0⟩ := ha
    let v' := (v 0)⁻¹ • v
    have hv' : v' ∈ W := W.smul_mem _ hv
    have hv'0 : v' 0 = 1 := by simp [v',hv0]
    apply finrank_le_one_of_coordinate_kernel W 0
    intro w hw hw0
    apply duplicate_normalized_first_kernel_zero v' w hv'0 hw0
    intro z h
    have hm := W.add_mem (W.smul_mem z hv') (W.smul_mem h hw)
    have hz := hp (z • v' + h • w) hm
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_assoc] using hz

lemma basic_star_row_relations (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ a z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + starMatrix a (-a) (i,j) +
        z * V (i,j)) = 24) :
    V (1,1) = V (2,2) ∧ V (1,1) = V (1,2) ∧ V (1,3) = V (2,3) := by
  have hp' : ∀ a z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + starMatrix a ((-1)*a) (i,j) +
        z * V (i,j)) = 24 := by simpa using hp
  rcases star_line_constraints (-1) V hs hp' with ⟨h1,h2,hq⟩
  have hsq : (V (1,3) - V (2,3))^2 = 0 := by
    unfold starLineQuad at hq
    linear_combination hq - V (3,3) * h2
  have h13 : V (1,3) = V (2,3) := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsq)
  have h11 : V (1,1) = V (2,2) := by linear_combination h1 - h13
  have h12 : V (1,1) = V (1,2) := by linear_combination (h2 + h11) / 2
  exact ⟨h11,h12,h13⟩

noncomputable def basicStarCoordinates : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) where
  toFun V := ![V (1,1),(V (0,1)+V (0,2))/2,V (1,3),V (0,0),V (0,3),V (3,3)]
  map_add' := by intros; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intros; ext i; fin_cases i <;> simp <;> ring

noncomputable def basicStarPermutation : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective ![1,2,0,3] (by decide)

lemma basic_star_projection_reconstruction (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (h11 : V (1,1)=V (2,2)) (h12 : V (1,1)=V (1,2))
    (h13 : V (1,3)=V (2,3)) :
    duplicateRowMap (basicStarCoordinates V) = entryPermute basicStarPermutation
      (V - ((V (0,1)-V (0,2))/2) • starMatrix 1 (-1)) := by
  have h10 := hs 1 0
  have h20 := hs 2 0
  have h30 := hs 3 0
  have h21 := hs 2 1
  have h31 := hs 3 1
  have h32 := hs 3 2
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [duplicateRowMap,duplicateRowMatrix,basicStarCoordinates,entryPermute,
      basicStarPermutation,starMatrix,h10,h20,h30,h21,h31,h32,
      ← h11,← h12,← h13] <;> ring

lemma basic_star_coordinates_kernel (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (h11 : V (1,1)=V (2,2)) (h12 : V (1,1)=V (1,2))
    (h13 : V (1,3)=V (2,3))
    (hF : basicStarCoordinates V=0) (h01 : V (0,1)=0) : V=0 := by
  have h₀ : V (1,1)=0 := by simpa [basicStarCoordinates] using congrFun hF 0
  have h₁ : (V (0,1)+V (0,2))/2=0 := by
    simpa [basicStarCoordinates] using congrFun hF 1
  have h₂ : V (1,3)=0 := by simpa [basicStarCoordinates] using congrFun hF 2
  have h₃ : V (0,0)=0 := by simpa [basicStarCoordinates] using congrFun hF 3
  have h₄ : V (0,3)=0 := by simpa [basicStarCoordinates] using congrFun hF 4
  have h₅ : V (3,3)=0 := by simpa [basicStarCoordinates] using congrFun hF 5
  have h02 : V (0,2)=0 := by linear_combination 2*h₁-h01
  have h10 := hs 1 0
  have h20 := hs 2 0
  have h30 := hs 3 0
  have h21 := hs 2 1
  have h31 := hs 3 1
  have h32 := hs 3 2
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [h10,h20,h30,h21,h31,h32,← h11,← h12,← h13,
      h₀,h₂,h₃,h₄,h₅,h01,h02]

lemma containing_basic_star_line_finrank_le_two
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (hA : starMatrix 1 (-1) ∈ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    Module.finrank ℂ L ≤ 2 := by
  have hrows (V : Fin 4 × Fin 4 → ℂ) (hV : V ∈ L) :
      V (1,1)=V (2,2) ∧ V (1,1)=V (1,2) ∧ V (1,3)=V (2,3) := by
    apply basic_star_row_relations V (hs V hV)
    intro a z
    simpa using star_line_closed_family L (-1) hA hp V hV a z
  have himage : ∀ v ∈ L.map basicStarCoordinates,
      duplicateRowPolynomial (1+v 0) (1+v 1) (1+v 2)
        (1+v 3) (1+v 4) (1+v 5)=24 := by
    rintro v ⟨V,hV,rfl⟩
    obtain ⟨h11,h12,h13⟩ := hrows V hV
    rw [← permanent_duplicateRowMap,
      basic_star_projection_reconstruction V (hs V hV) h11 h12 h13]
    apply (entryPermute_permanent basicStarPermutation _).trans
    exact hp _ (L.sub_mem hV (L.smul_mem _ hA))
  let F := basicStarCoordinates.domRestrict L
  have hrange : Module.finrank ℂ (LinearMap.range F) ≤ 1 := by
    change Module.finrank ℂ (LinearMap.range (basicStarCoordinates.domRestrict L)) ≤ 1
    rw [LinearMap.range_domRestrict]
    exact duplicate_row_flat_finrank_le_one _ himage
  let G : LinearMap.ker F →ₗ[ℂ] ℂ :=
    { toFun := fun V => V.val.val (0,1)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hGker : ∀ V : LinearMap.ker F, G V=0 → V=0 := by
    intro V hV
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨h11,h12,h13⟩ := hrows V.val.val V.val.property
    exact basic_star_coordinates_kernel V.val.val (hs _ V.val.property)
      h11 h12 h13 V.property hV
  have hG : Function.Injective G := by
    intro V W h
    apply sub_eq_zero.mp
    apply hGker (V-W)
    change G V-G W=0
    exact sub_eq_zero.mpr h
  have hkernel : Module.finrank ℂ (LinearMap.ker F) ≤ 1 := by
    have hd := Submodule.finrank_le (LinearMap.range G)
    rw [LinearMap.finrank_range_of_inj hG] at hd
    simpa using hd
  have htotal := F.finrank_range_add_finrank_ker
  omega

end PEqualNP.Outside.L_gct_231
