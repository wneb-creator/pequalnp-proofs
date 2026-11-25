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

end PEqualNP.Outside.L_gct_231
