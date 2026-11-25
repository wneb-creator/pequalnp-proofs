import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

set_option maxHeartbeats 4000000 in
lemma permanent_shifted_hollow_scaled {R : Type*} [CommRing R]
    (r a b c d e f z : R) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1 + z * (r + hollowMatrix a b c d e f i j)) =
    24 + (96*r+12*(a+b+c+d+e+f))*z +
      (144*r^2+36*r*(a+b+c+d+e+f)+2*(a+b+c+d+e+f)^2+
        4*(a*f+b*e+c*d))*z^2 +
      (96*r^3+36*r^2*(a+b+c+d+e+f)+4*r*(a+b+c+d+e+f)^2+
        8*r*(a*f+b*e+c*d)+hollowCubic a b c d e f)*z^3 +
      (24*r^4+12*r^3*(a+b+c+d+e+f)+2*r^2*(a+b+c+d+e+f)^2+
        4*r^2*(a*f+b*e+c*d)+r*hollowCubic a b c d e f+
        (a*f+b*e+c*d)^2)*z^4 := by
  rw [permanent_four]
  simp [hollowMatrix,hollowCubic]
  ring

lemma shifted_hollow_scalar_zero (r a b c d e f : ℂ)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1 + z * (r + hollowMatrix a b c d e f i j)) = 24) : r = 0 := by
  let s := a+b+c+d+e+f
  let q := a*f+b*e+c*d
  let h := hollowCubic a b c d e f
  let aa := 96*r+12*s
  let bb := 144*r^2+36*r*s+2*s^2+4*q
  let cc := 96*r^3+36*r^2*s+4*r*s^2+8*r*q+h
  let dd := 24*r^4+12*r^3*s+2*r^2*s^2+4*r^2*q+r*h+q^2
  have hpoly : ∀ z : ℂ, aa*z+bb*z^2+cc*z^3+dd*z^4=0 := by
    intro z
    have hz := hp z
    rw [permanent_shifted_hollow_scaled] at hz
    dsimp [aa,bb,cc,dd,s,q,h]
    linear_combination hz
  obtain ⟨haa,hbb⟩ := quartic_first_coefficients aa bb cc dd hpoly
  have hcc : cc = 0 := by
    have h₁ := hpoly 1
    have h₂ := hpoly (-1)
    linear_combination h₁/2-h₂/2-haa
  have hdd : dd = 0 := by
    have h₁ := hpoly 1
    linear_combination h₁-haa-hbb-hcc
  have hs : s = -8*r := by
    dsimp [aa] at haa
    linear_combination haa/12
  have hq : q = 4*r^2 := by
    dsimp [bb] at hbb
    rw [hs] at hbb
    linear_combination hbb/4
  have hr : r^4 = 0 := by
    dsimp [cc,dd] at hcc hdd
    rw [hs,hq] at hcc hdd
    linear_combination (r*hcc-hdd)/8
  exact eq_zero_of_pow_eq_zero hr

lemma constant_diagonal_zero (V : Fin 4 × Fin 4 → ℂ) (r : ℂ)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hd : ∀ i : Fin 4, V (i,i) = r)
    (hp : ∀ z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + z * V (i,j)) = 24) : r = 0 := by
  let a := V (0,1)-r
  let b := V (0,2)-r
  let c := V (0,3)-r
  let d := V (1,2)-r
  let e := V (1,3)-r
  let f := V (2,3)-r
  have hs10 := hs 1 0
  have hs20 := hs 2 0
  have hs30 := hs 3 0
  have hs21 := hs 2 1
  have hs31 := hs 3 1
  have hs32 := hs 3 2
  have heq : V = fun p => r+hollowMatrix a b c d e f p.1 p.2 := by
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [hollowMatrix,a,b,c,d,e,f,hd,hs10,hs20,hs30,hs21,hs31,hs32] <;> ring
  apply shifted_hollow_scalar_zero r a b c d e f
  intro z
  simpa only [heq] using hp z

lemma level_flat_constant_diagonal_zero
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j)) = 24)
    (V : Fin 4 × Fin 4 → ℂ) (hV : V ∈ L) (r : ℂ)
    (hd : ∀ i : Fin 4, V (i,i) = r) : r = 0 := by
  apply constant_diagonal_zero V r (hs V hV) hd
  intro z
  simpa only [Pi.smul_apply,smul_eq_mul] using hp (z • V) (L.smul_mem z hV)

end PEqualNP.Outside.L_gct_231
