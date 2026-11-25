import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination

namespace PEqualNP.Outside.L_gct_231_aux.AllZeroSkewReconstruction

theorem skew_reconstruction
    (h a b c c0 c1 c2 U00 U01 U02 U10 U11 U12 U20 U21 U22 : ℂ)
    (hQ : ∀ x y z : ℂ,
      x * (U00 * x + U01 * y + U02 * z) +
        y * (U10 * x + U11 * y + U12 * z) +
        z * (U20 * x + U21 * y + U22 * z) = (a * x + b * y + c * z) ^ 2)
    (hL : ∀ x y z : ℂ,
      2 * h * (x + y + z) + c0 * x + c1 * y + c2 * z +
        2 * ((U00 * x + U01 * y + U02 * z) +
          (U10 * x + U11 * y + U12 * z) +
          (U20 * x + U21 * y + U22 * z)) = 16 * (a * x + b * y + c * z)) :
    ∃ l m n : ℂ,
      U00 = a ^ 2 ∧ U11 = b ^ 2 ∧ U22 = c ^ 2 ∧
      U01 = a * b + l ∧ U10 = a * b - l ∧
      U02 = a * c + m ∧ U20 = a * c - m ∧
      U12 = b * c + n ∧ U21 = b * c - n ∧
      c0 = 16 * a - 2 * h - 2 * (a + b + c) * a + 2 * l + 2 * m ∧
      c1 = 16 * b - 2 * h - 2 * (a + b + c) * b - 2 * l + 2 * n ∧
      c2 = 16 * c - 2 * h - 2 * (a + b + c) * c - 2 * m - 2 * n := by
  have h00 := hQ 1 0 0
  have h11 := hQ 0 1 0
  have h22 := hQ 0 0 1
  norm_num at h00 h11 h22
  have h01 : U01 + U10 = 2 * a * b := by
    have hh := hQ 1 1 0
    norm_num at hh
    linear_combination hh - h00 - h11
  have h02 : U02 + U20 = 2 * a * c := by
    have hh := hQ 1 0 1
    norm_num at hh
    linear_combination hh - h00 - h22
  have h12 : U12 + U21 = 2 * b * c := by
    have hh := hQ 0 1 1
    norm_num at hh
    linear_combination hh - h11 - h22
  have hL0 := hL 1 0 0
  have hL1 := hL 0 1 0
  have hL2 := hL 0 0 1
  norm_num at hL0 hL1 hL2
  refine ⟨U01 - a * b, U02 - a * c, U12 - b * c,
    h00, h11, h22, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ring
  · linear_combination h01
  · ring
  · linear_combination h02
  · ring
  · linear_combination h12
  · linear_combination hL0 - 2 * h00 - 2 * h01 - 2 * h02
  · linear_combination hL1 - 2 * h11 - 2 * h12
  · linear_combination hL2 - 2 * h22

end PEqualNP.Outside.L_gct_231_aux.AllZeroSkewReconstruction
