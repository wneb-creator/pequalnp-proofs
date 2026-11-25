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

end PEqualNP.Outside.L_gct_231.DenseStar
