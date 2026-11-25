import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination

namespace PEqualNP.Outside.L_gct_231_aux.FrameGramFactor

set_option maxRecDepth 2048 in
set_option maxHeartbeats 0 in
theorem factor_entries (u0 u1 u2 v0 v1 v2 a b c d e f : ℂ)
    (hu : a*u0^2 + 2*b*u0*u1 + 2*c*u0*u2 + d*u1^2 + 2*e*u1*u2 + f*u2^2 = 0)
    (hv : a*v0^2 + 2*b*v0*v1 + 2*c*v0*v2 + d*v1^2 + 2*e*v1*v2 + f*v2^2 = 0)
    (huv : a*u0*v0 + b*(u0*v1+u1*v0) + c*(u0*v2+u2*v0) +
      d*u1*v1 + e*(u1*v2+u2*v1) + f*u2*v2 = 0)
    (hj : a+d+f+2*b+2*c+2*e = 0)
    (hn : (u1*v2-u2*v1)+(u2*v0-u0*v2)+(u0*v1-u1*v0) ≠ 0) :
    let n0 := u1*v2-u2*v1
    let n1 := u2*v0-u0*v2
    let n2 := u0*v1-u1*v0
    (n0+n1+n2)*a = n0*(a+b+c)+n0*(a+b+c) ∧
    (n0+n1+n2)*b = n0*(b+d+e)+n1*(a+b+c) ∧
    (n0+n1+n2)*c = n0*(c+e+f)+n2*(a+b+c) ∧
    (n0+n1+n2)*d = n1*(b+d+e)+n1*(b+d+e) ∧
    (n0+n1+n2)*e = n1*(c+e+f)+n2*(b+d+e) ∧
    (n0+n1+n2)*f = n2*(c+e+f)+n2*(c+e+f) := by
  let n0 := u1*v2-u2*v1
  let n1 := u2*v0-u0*v2
  let n2 := u0*v1-u1*v0
  let N := n0+n1+n2
  have hN : N ≠ 0 := hn
  change N*a = n0*(a+b+c)+n0*(a+b+c) ∧
    N*b = n0*(b+d+e)+n1*(a+b+c) ∧
    N*c = n0*(c+e+f)+n2*(a+b+c) ∧
    N*d = n1*(b+d+e)+n1*(b+d+e) ∧
    N*e = n1*(c+e+f)+n2*(b+d+e) ∧
    N*f = n2*(c+e+f)+n2*(c+e+f)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hh : N*(N*a-(n0*(a+b+c)+n0*(a+b+c))) = 0 := by
      dsimp [N,n0,n1,n2]
      linear_combination (v1-v2)^2*hu + 2*(v1-v2)*(u2-u1)*huv +
        (u2-u1)^2*hv - (u1*v2-u2*v1)^2*hj
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hN)
  · have hh : N*(N*b-(n0*(b+d+e)+n1*(a+b+c))) = 0 := by
      dsimp [N,n0,n1,n2]
      linear_combination (v1-v2)*(v2-v0)*hu +
        ((v1-v2)*(u0-u2)+(u2-u1)*(v2-v0))*huv +
        (u2-u1)*(u0-u2)*hv - (u1*v2-u2*v1)*(u2*v0-u0*v2)*hj
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hN)
  · have hh : N*(N*c-(n0*(c+e+f)+n2*(a+b+c))) = 0 := by
      dsimp [N,n0,n1,n2]
      linear_combination (v1-v2)*(v0-v1)*hu +
        ((v1-v2)*(u1-u0)+(u2-u1)*(v0-v1))*huv +
        (u2-u1)*(u1-u0)*hv - (u1*v2-u2*v1)*(u0*v1-u1*v0)*hj
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hN)
  · have hh : N*(N*d-(n1*(b+d+e)+n1*(b+d+e))) = 0 := by
      dsimp [N,n0,n1,n2]
      linear_combination (v2-v0)^2*hu + 2*(v2-v0)*(u0-u2)*huv +
        (u0-u2)^2*hv - (u2*v0-u0*v2)^2*hj
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hN)
  · have hh : N*(N*e-(n1*(c+e+f)+n2*(b+d+e))) = 0 := by
      dsimp [N,n0,n1,n2]
      linear_combination (v2-v0)*(v0-v1)*hu +
        ((v2-v0)*(u1-u0)+(u0-u2)*(v0-v1))*huv +
        (u0-u2)*(u1-u0)*hv - (u2*v0-u0*v2)*(u0*v1-u1*v0)*hj
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hN)
  · have hh : N*(N*f-(n2*(c+e+f)+n2*(c+e+f))) = 0 := by
      dsimp [N,n0,n1,n2]
      linear_combination (v0-v1)^2*hu + 2*(v0-v1)*(u1-u0)*huv +
        (u1-u0)^2*hv - (u0*v1-u1*v0)^2*hj
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hN)

end PEqualNP.Outside.L_gct_231_aux.FrameGramFactor
