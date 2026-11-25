import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination

namespace PEqualNP.Outside.L_gct_231_aux.FramePathPairedCases

set_option maxRecDepth 2048 in
set_option maxHeartbeats 0 in
lemma case0 (r u12 u23 : ℂ)
    (hr : r ^ 2 = 2)
    (h0 : -12*r*u12*u23 - 12*r*u23 ^ 2 - 27*u12 ^ 2 - 18*u12*u23 - 15*u23 ^ 2 = 0)
    (h1 : -12*r*u12 ^ 2 + 12*r*u12*u23 + 24*r*u23 ^ 2 + 24*u12 ^ 2 + 24*u12*u23 + 30*u23 ^ 2 = 0)
    (h2 : 12*r*u12 ^ 2 + 12*r*u12*u23 + 12*u12 ^ 2 + 18*u12*u23 + 6*u12 = 0)
    (h3 : 12*r*u12 ^ 2 - 12*r*u23 ^ 2 - 15*u12 ^ 2 - 6*u12*u23 - 15*u23 ^ 2 = 0)
    (h4 : -12*r*u12*u23 + 12*r*u12 - 6*u12 ^ 2 - 18*u12*u23 - 18*u12 = 0)
    (h5 : -12*r*u12 ^ 2 + 12*r - 15*u12 ^ 2 - 6*u12 - 15 = 0)
    : False := by
  have hz : (126 : ℂ) = 0 := by
    linear_combination
      (-21*r - 28) * h0
      + (-48*r - 67) * h1
      + (24*r + 30) * h2
      + (-75*r - 106) * h3
      + (0) * h4
      + (24*r + 30) * h5
      - (-324*u12 ^ 2 - 36*u12*u23 + 288) * hr
  norm_num at hz

set_option maxRecDepth 2048 in
set_option maxHeartbeats 0 in
lemma case1 (r u12 u23 : ℂ)
    (hr : r ^ 2 = 2)
    (h0 : -32*r*u12 ^ 2 - 36*r*u12*u23 - 12*r*u23 ^ 2 - 43*u12 ^ 2 - 50*u12*u23 - 15*u23 ^ 2 = 0)
    (h1 : 164*r*u12 ^ 2 + 108*r*u12*u23 + 24*r*u23 ^ 2 + 232*u12 ^ 2 + 152*u12*u23 + 30*u23 ^ 2 = 0)
    (h2 : -116*r*u12 ^ 2 - 44*r*u12*u23 - 164*u12 ^ 2 - 62*u12*u23 + 6*u12 = 0)
    (h3 : 804*r*u12 ^ 2 - 72*r*u12*u23 - 12*r*u23 ^ 2 + 1137*u12 ^ 2 - 102*u12*u23 - 15*u23 ^ 2 = 0)
    (h4 : -1656*r*u12 ^ 2 + 44*r*u12*u23 - 12*r*u12 - 2342*u12 ^ 2 + 62*u12*u23 - 18*u12 = 0)
    (h5 : 804*r*u12 ^ 2 + 8*r*u12 + 12*r + 1137*u12 ^ 2 + 10*u12 - 15 = 0)
    : False := by
  have hz : (4914 : ℂ) = 0 := by
    linear_combination
      (-8295*r - 11732) * h0
      + (-4512*r - 6389) * h1
      + (-3120*r - 4446) * h2
      + (-729*r - 1046) * h3
      + (0) * h4
      + (936*r + 1170) * h5
      - (53820*u12 ^ 2 + 1092*u12*u23 + 7488*u12 + 11232) * hr
  norm_num at hz

set_option maxRecDepth 2048 in
set_option maxHeartbeats 0 in
lemma case2 (r u12 u23 : ℂ)
    (hr : r ^ 2 = 2)
    (h0 : 20*r*u12*u23 + 12*r*u23 ^ 2 - 27*u12 ^ 2 - 34*u12*u23 - 15*u23 ^ 2 = 0)
    (h1 : -12*r*u12 ^ 2 - 36*r*u12*u23 - 24*r*u23 ^ 2 + 24*u12 ^ 2 + 56*u12*u23 + 30*u23 ^ 2 = 0)
    (h2 : 12*r*u12 ^ 2 + 4*r*u12*u23 - 8*r*u12 + 12*u12 ^ 2 + 2*u12*u23 - 10*u12 = 0)
    (h3 : 12*r*u12 ^ 2 + 16*r*u12*u23 + 12*r*u23 ^ 2 - 15*u12 ^ 2 - 22*u12*u23 - 15*u23 ^ 2 = 0)
    (h4 : -4*r*u12*u23 + 4*r*u12 - 6*u12 ^ 2 - 2*u12*u23 - 2*u12 = 0)
    (h5 : -12*r*u12 ^ 2 - 16*r*u12 - 12*r - 15*u12 ^ 2 - 22*u12 - 15 = 0)
    : False := by
  have hz : (882 : ℂ) = 0 := by
    linear_combination
      (132 - 23*r) * h0
      + (75 - 32*r) * h1
      + (96*r - 78) * h2
      + (18 - 41*r) * h3
      + (0) * h4
      + (210 - 168*r) * h5
      - (3060*u12 ^ 2 + 420*u12*u23 + 1920*u12 + 2016) * hr
  norm_num at hz

set_option maxRecDepth 2048 in
set_option maxHeartbeats 0 in
lemma case3 (r u12 u23 : ℂ)
    (hr : r ^ 2 = 2)
    (h0 : -32*r*u12 ^ 2 - 4*r*u12*u23 + 12*r*u23 ^ 2 - 43*u12 ^ 2 - 2*u12*u23 - 15*u23 ^ 2 = 0)
    (h1 : 164*r*u12 ^ 2 - 4*r*u12*u23 - 24*r*u23 ^ 2 + 232*u12 ^ 2 - 8*u12*u23 + 30*u23 ^ 2 = 0)
    (h2 : -116*r*u12 ^ 2 + 12*r*u12*u23 - 8*r*u12 - 164*u12 ^ 2 + 18*u12*u23 - 10*u12 = 0)
    (h3 : 804*r*u12 ^ 2 + 8*r*u12*u23 + 12*r*u23 ^ 2 + 1137*u12 ^ 2 + 10*u12*u23 - 15*u23 ^ 2 = 0)
    (h4 : -1656*r*u12 ^ 2 - 12*r*u12*u23 + 44*r*u12 - 2342*u12 ^ 2 - 18*u12*u23 + 62*u12 = 0)
    (h5 : 804*r*u12 ^ 2 - 72*r*u12 - 12*r + 1137*u12 ^ 2 - 102*u12 - 15 = 0)
    : False := by
  have hz : (3822 : ℂ) = 0 := by
    linear_combination
      (1003*r + 1436) * h0
      + (496*r + 773) * h1
      + (312*r + 702) * h2
      + (110 - 11*r) * h3
      + (0) * h4
      + (910 - 728*r) * h5
      - (-581100*u12 ^ 2 - 2340*u12*u23 + 49920*u12 + 8736) * hr
  norm_num at hz

end PEqualNP.Outside.L_gct_231_aux.FramePathPairedCases
