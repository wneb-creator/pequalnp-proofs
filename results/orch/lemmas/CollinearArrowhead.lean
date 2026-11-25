import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination

import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_gct_231

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in

lemma collinearArrowhead_mid_annihilated (g i k d e f : ℂ)
    (hq0 : ((e ^ 2) + (f ^ 2) + ((-1) * (i ^ 2)) + ((-1) * (k ^ 2)) + ((-1) * i * k) + ((-2) * e * i) + ((-2) * f * k) + (2 * e * f)) = 0)
    (hq1 : (((-2) * (f ^ 2)) + (2 * (k ^ 2)) + (i * k) + ((-1) * g * i) + ((-1) * g * k) + ((-2) * e * f) + (2 * d * e) + (2 * d * f) + (4 * f * k)) = 0)
    (hq2 : ((d ^ 2) + (f ^ 2) + ((-1) * (g ^ 2)) + ((-1) * (k ^ 2)) + (g * k) + ((-2) * d * f) + ((-2) * d * g) + ((-2) * f * k)) = 0)
    (hc0 : ((i * (f ^ 2)) + (k * (e ^ 2)) + ((-1) * i * (k ^ 2)) + ((-1) * k * (i ^ 2)) + ((-2) * e * i * k) + ((-2) * f * i * k)) = 0)
    (hc1 : ((g * (e ^ 2)) + (g * (f ^ 2)) + (k * (i ^ 2)) + ((-1) * g * (i ^ 2)) + ((-1) * g * (k ^ 2)) + ((-1) * k * (e ^ 2)) + ((-2) * i * (f ^ 2)) + (2 * i * (k ^ 2)) + ((-2) * e * g * i) + ((-2) * f * g * k) + ((-2) * g * i * k) + (2 * d * e * k) + (2 * d * f * i) + (2 * e * f * g) + (2 * e * i * k) + (4 * f * i * k)) = 0)
    (hc2 : ((i * (d ^ 2)) + (i * (f ^ 2)) + (k * (d ^ 2)) + ((-1) * i * (g ^ 2)) + ((-1) * i * (k ^ 2)) + ((-1) * k * (g ^ 2)) + ((-2) * g * (f ^ 2)) + (2 * g * (k ^ 2)) + ((-2) * d * e * k) + ((-2) * d * f * i) + ((-2) * d * g * i) + ((-2) * d * g * k) + ((-2) * e * f * g) + ((-2) * f * i * k) + (2 * g * i * k) + (4 * f * g * k)) = 0)
    (hc3 : ((g * (f ^ 2)) + (k * (g ^ 2)) + ((-1) * g * (k ^ 2)) + ((-1) * k * (d ^ 2)) + ((-2) * f * g * k) + (2 * d * g * k)) = 0)
    : e ^ 2 * f ^ 3 * i = 0 := by
  linear_combination
    ((-1 / 123480 : ℂ) * (((-8079) * (f ^ 4)) + ((-142929) * (d ^ 2) * (f ^ 2)) + ((-42948) * i * (f ^ 3)) + ((-42176) * i * (d ^ 3)) + ((-42176) * k * (d ^ 3)) + ((-31342) * d * (e ^ 3)) + ((-31221) * (e ^ 2) * (f ^ 2)) + ((-22706) * e * (f ^ 3)) + ((-13166) * (f ^ 2) * (i ^ 2)) + ((-10270) * g * (i ^ 3)) + ((-2840) * e * (k ^ 3)) + ((-769) * (e ^ 2) * (k ^ 2)) + ((-96) * g * (f ^ 3)) + (1448 * i * (k ^ 3)) + (2342 * d * (f ^ 3)) + (4013 * (e ^ 2) * (g ^ 2)) + (4472 * f * (k ^ 3)) + (7374 * (d ^ 2) * (i ^ 2)) + (7983 * (f ^ 2) * (g ^ 2)) + (10270 * k * (i ^ 3)) + (11686 * k * (f ^ 3)) + (14614 * (i ^ 2) * (k ^ 2)) + (17023 * (f ^ 2) * (k ^ 2)) + (31342 * f * (e ^ 3)) + (42176 * d * (k ^ 3)) + (42889 * (d ^ 2) * (e ^ 2)) + (148666 * e * (d ^ 3)) + (148666 * f * (d ^ 3)) + (168704 * (d ^ 2) * (k ^ 2)) + ((-113172) * e * i * (f ^ 2)) + ((-93808) * d * i * (f ^ 2)) + ((-93672) * e * f * (d ^ 2)) + ((-78704) * f * i * (e ^ 2)) + ((-59304) * d * g * (i ^ 2)) + ((-42176) * d * g * (k ^ 2)) + ((-39352) * e * g * (i ^ 2)) + ((-37436) * d * k * (f ^ 2)) + ((-35462) * f * k * (e ^ 2)) + ((-32288) * d * e * (f ^ 2)) + ((-24208) * f * g * (i ^ 2)) + ((-20540) * e * f * (i ^ 2)) + ((-20038) * d * e * (g ^ 2)) + ((-20038) * d * f * (g ^ 2)) + ((-15671) * i * k * (e ^ 2)) + ((-11906) * d * g * (f ^ 2)) + ((-11718) * g * k * (i ^ 2)) + ((-11668) * d * f * (e ^ 2)) + ((-4424) * f * g * (k ^ 2)) + ((-2488) * g * k * (e ^ 2)) + ((-1780) * e * g * (k ^ 2)) + ((-1448) * g * i * (k ^ 2)) + ((-96) * f * i * (g ^ 2)) + ((-48) * f * k * (g ^ 2)) + (96 * g * k * (f ^ 2)) + (1272 * e * g * (f ^ 2)) + (4620 * e * i * (g ^ 2)) + (4620 * e * k * (g ^ 2)) + (5372 * e * f * (g ^ 2)) + (5792 * d * f * (i ^ 2)) + (7220 * e * f * (k ^ 2)) + (9335 * g * i * (f ^ 2)) + (9674 * d * g * (e ^ 2)) + (11240 * e * k * (d ^ 2)) + (15671 * g * i * (e ^ 2)) + (15856 * e * k * (f ^ 2)) + (20038 * g * i * (d ^ 2)) + (20038 * g * k * (d ^ 2)) + (20540 * d * e * (i ^ 2)) + (37740 * e * i * (k ^ 2)) + (39352 * e * k * (i ^ 2)) + (44276 * e * g * (d ^ 2)) + (44276 * f * g * (d ^ 2)) + (44556 * d * k * (i ^ 2)) + (45796 * f * i * (k ^ 2)) + (50292 * d * k * (e ^ 2)) + (50540 * f * k * (i ^ 2)) + (57200 * f * g * (e ^ 2)) + (78704 * d * i * (e ^ 2)) + (82202 * d * f * (k ^ 2)) + (92431 * i * k * (f ^ 2)) + (97230 * d * e * (k ^ 2)) + (103060 * e * i * (d ^ 2)) + (111764 * i * k * (d ^ 2)) + (128908 * d * i * (k ^ 2)) + (178932 * f * i * (d ^ 2)) + (417192 * f * k * (d ^ 2)) + ((-143656) * d * g * i * k) + ((-92932) * d * e * g * k) + ((-65954) * d * e * g * i) + ((-58914) * d * f * g * i) + ((-34036) * e * f * g * k) + ((-26108) * f * g * i * k) + ((-16504) * d * e * f * g) + ((-10236) * e * g * i * k) + ((-4524) * d * f * g * k) + (9972 * e * f * g * i) + (10112 * d * e * f * i) + (58606 * d * e * i * k) + (98992 * e * f * i * k) + (145108 * d * e * f * k) + (247234 * d * f * i * k))) * hq0 +
    ((1 / 123480 : ℂ) * (((-15671) * (e ^ 4)) + ((-10270) * (i ^ 4)) + ((-84352) * (d ^ 2) * (i ^ 2)) + ((-84352) * (d ^ 2) * (k ^ 2)) + ((-59892) * e * (i ^ 3)) + ((-52763) * (e ^ 2) * (i ^ 2)) + ((-44556) * d * (i ^ 3)) + ((-24208) * f * (i ^ 3)) + ((-23936) * k * (e ^ 3)) + ((-18568) * g * (e ^ 3)) + ((-11718) * k * (i ^ 3)) + ((-10573) * (f ^ 2) * (i ^ 2)) + ((-2674) * f * (e ^ 3)) + ((-1448) * (i ^ 2) * (k ^ 2)) + (4013 * (e ^ 2) * (g ^ 2)) + (4520 * g * (f ^ 3)) + (4520 * i * (f ^ 3)) + (5680 * (e ^ 2) * (k ^ 2)) + (7374 * g * (i ^ 3)) + (7983 * (f ^ 2) * (g ^ 2)) + (18750 * e * (f ^ 3)) + (20038 * e * (d ^ 3)) + (20038 * f * (d ^ 3)) + (24058 * d * (e ^ 3)) + (24910 * d * (f ^ 3)) + (25123 * (e ^ 2) * (f ^ 2)) + (36293 * (d ^ 2) * (f ^ 2)) + (70694 * i * (e ^ 3)) + (80339 * (d ^ 2) * (e ^ 2)) + ((-173324) * e * i * (d ^ 2)) + ((-168656) * f * k * (d ^ 2)) + ((-113170) * d * e * (i ^ 2)) + ((-104390) * i * k * (d ^ 2)) + ((-89348) * d * k * (i ^ 2)) + ((-78672) * d * e * (k ^ 2)) + ((-56544) * e * f * (i ^ 2)) + ((-45072) * d * i * (k ^ 2)) + ((-42176) * d * g * (i ^ 2)) + ((-42176) * d * g * (k ^ 2)) + ((-40076) * e * g * (d ^ 2)) + ((-40076) * f * g * (d ^ 2)) + ((-38868) * f * g * (e ^ 2)) + ((-20038) * d * e * (g ^ 2)) + ((-20038) * d * f * (g ^ 2)) + ((-18312) * e * k * (i ^ 2)) + ((-17984) * d * k * (f ^ 2)) + ((-17023) * g * k * (f ^ 2)) + ((-17023) * i * k * (f ^ 2)) + ((-14422) * g * i * (f ^ 2)) + ((-8944) * d * f * (k ^ 2)) + ((-8944) * e * f * (k ^ 2)) + ((-5104) * e * k * (f ^ 2)) + ((-4472) * f * g * (k ^ 2)) + ((-4472) * f * i * (k ^ 2)) + ((-3560) * d * i * (e ^ 2)) + ((-3180) * e * g * (f ^ 2)) + ((-1448) * g * i * (k ^ 2)) + ((-1351) * g * k * (e ^ 2)) + ((-96) * f * i * (g ^ 2)) + ((-56) * e * i * (k ^ 2)) + ((-48) * f * k * (g ^ 2)) + (552 * f * k * (i ^ 2)) + (2840 * e * g * (k ^ 2)) + (3898 * d * f * (i ^ 2)) + (4620 * e * i * (g ^ 2)) + (4620 * e * k * (g ^ 2)) + (5372 * e * f * (g ^ 2)) + (5372 * f * g * (i ^ 2)) + (5926 * g * k * (i ^ 2)) + (8436 * d * k * (e ^ 2)) + (19062 * e * i * (f ^ 2)) + (26404 * f * k * (e ^ 2)) + (29762 * g * i * (e ^ 2)) + (32380 * d * e * (f ^ 2)) + (33316 * e * g * (i ^ 2)) + (44776 * d * f * (e ^ 2)) + (45576 * f * i * (e ^ 2)) + (50052 * d * i * (f ^ 2)) + (50202 * d * g * (e ^ 2)) + (58142 * d * g * (f ^ 2)) + (64991 * i * k * (e ^ 2)) + (75532 * e * k * (d ^ 2)) + (80248 * f * i * (d ^ 2)) + (123256 * e * f * (d ^ 2)) + ((-114390) * d * e * i * k) + ((-88216) * d * e * f * k) + ((-75112) * d * e * g * i) + ((-73566) * d * f * i * k) + ((-64410) * d * f * g * k) + ((-42176) * d * g * i * k) + ((-17444) * e * f * g * i) + ((-7224) * f * g * i * k) + (2376 * e * f * i * k) + (10572 * e * f * g * k) + (11052 * e * g * i * k) + (39884 * d * f * g * i) + (69354 * d * e * g * k) + (86548 * d * e * f * i) + (95096 * d * e * f * g))) * hq1 +
    ((-1 / 123480 : ℂ) * ((5227 * (e ^ 4)) + (7374 * (i ^ 4)) + (8079 * (f ^ 4)) + ((-42176) * d * (i ^ 3)) + ((-42176) * d * (k ^ 3)) + ((-36004) * d * (f ^ 3)) + ((-24402) * i * (e ^ 3)) + ((-17023) * (f ^ 2) * (k ^ 2)) + ((-13948) * k * (e ^ 3)) + ((-11686) * k * (f ^ 3)) + ((-10591) * (e ^ 2) * (k ^ 2)) + ((-4472) * f * (k ^ 3)) + ((-3034) * (e ^ 2) * (f ^ 2)) + ((-1448) * i * (k ^ 3)) + (1364 * e * (f ^ 3)) + (2840 * e * (k ^ 3)) + (3641 * (f ^ 2) * (i ^ 2)) + (4232 * i * (f ^ 3)) + (4478 * (i ^ 2) * (k ^ 2)) + (5468 * f * (i ^ 3)) + (8908 * f * (e ^ 3)) + (12012 * d * (e ^ 3)) + (13300 * k * (i ^ 3)) + (15295 * (e ^ 2) * (i ^ 2)) + (28696 * e * (i ^ 3)) + (40076 * (d ^ 2) * (e ^ 2)) + (40076 * (d ^ 2) * (f ^ 2)) + ((-104390) * d * e * (i ^ 2)) + ((-84352) * d * i * (k ^ 2)) + ((-84352) * d * k * (i ^ 2)) + ((-64314) * d * f * (k ^ 2)) + ((-46748) * d * e * (f ^ 2)) + ((-39286) * f * k * (e ^ 2)) + ((-11648) * f * i * (k ^ 2)) + ((-7680) * e * f * (i ^ 2)) + ((-7140) * d * i * (e ^ 2)) + ((-7112) * i * k * (f ^ 2)) + ((-1804) * f * k * (i ^ 2)) + ((-96) * f * g * (i ^ 2)) + ((-48) * f * g * (k ^ 2)) + (1268 * d * f * (e ^ 2)) + (3296 * e * k * (f ^ 2)) + (4013 * g * i * (e ^ 2)) + (4013 * g * k * (e ^ 2)) + (4620 * e * g * (i ^ 2)) + (4620 * e * g * (k ^ 2)) + (6220 * f * i * (e ^ 2)) + (7983 * g * i * (f ^ 2)) + (7983 * g * k * (f ^ 2)) + (9272 * e * i * (k ^ 2)) + (10668 * e * f * (k ^ 2)) + (12730 * i * k * (e ^ 2)) + (20038 * d * f * (i ^ 2)) + (21030 * e * i * (f ^ 2)) + (32936 * d * k * (e ^ 2)) + (35128 * e * k * (i ^ 2)) + (42368 * d * i * (f ^ 2)) + (60114 * d * e * (k ^ 2)) + (80152 * e * f * (d ^ 2)) + (82348 * d * k * (f ^ 2)) + ((-85120) * d * f * i * k) + ((-84352) * d * e * i * k) + ((-20038) * d * e * g * i) + ((-20038) * d * e * g * k) + ((-20038) * d * f * g * i) + ((-20038) * d * f * g * k) + ((-144) * f * g * i * k) + (5372 * e * f * g * i) + (5372 * e * f * g * k) + (9240 * e * g * i * k) + (13444 * e * f * i * k) + (47828 * d * e * f * i) + (127884 * d * e * f * k))) * hq2 +
    ((-1 / 30870 : ℂ) * ((2947 * (f ^ 3)) + ((-42908) * d * (f ^ 2)) + ((-33630) * d * (e ^ 2)) + ((-20785) * e * (k ^ 2)) + ((-10381) * i * (d ^ 2)) + ((-7270) * k * (e ^ 2)) + ((-7215) * k * (d ^ 2)) + ((-6284) * g * (f ^ 2)) + ((-3350) * k * (f ^ 2)) + ((-2963) * i * (k ^ 2)) + ((-2947) * f * (k ^ 2)) + (477 * i * (f ^ 2)) + (2760 * f * (e ^ 2)) + (4470 * g * (e ^ 2)) + (39523 * e * (f ^ 2)) + (39961 * f * (d ^ 2)) + (43029 * d * (k ^ 2)) + (43111 * e * (d ^ 2)) + ((-82634) * d * e * f) + ((-37362) * e * f * k) + ((-20278) * d * e * k) + ((-9102) * f * i * k) + ((-8100) * d * e * i) + ((-6332) * d * g * k) + ((-1680) * e * i * k) + ((-650) * e * f * g) + (219 * f * g * k) + (6672 * e * g * k) + (8100 * e * f * i) + (9904 * d * f * i) + (11156 * d * f * g) + (22407 * d * i * k) + (23852 * d * e * g) + (86654 * d * f * k))) * hc0 +
    ((-1 / 61740 : ℂ) * (((-4472) * (f ^ 3)) + ((-39590) * d * (f ^ 2)) + ((-18178) * d * (e ^ 2)) + ((-12080) * e * (k ^ 2)) + ((-10032) * f * (e ^ 2)) + ((-10019) * i * (d ^ 2)) + ((-10019) * k * (d ^ 2)) + ((-7935) * g * (f ^ 2)) + ((-7715) * i * (f ^ 2)) + ((-1867) * k * (e ^ 2)) + (607 * g * (e ^ 2)) + (1448 * i * (k ^ 2)) + (4472 * f * (k ^ 2)) + (12104 * e * (f ^ 2)) + (14032 * k * (f ^ 2)) + (40076 * e * (d ^ 2)) + (40076 * f * (d ^ 2)) + (42176 * d * (k ^ 2)) + ((-63796) * d * e * f) + ((-21834) * e * f * k) + ((-15748) * d * e * k) + ((-11946) * e * f * i) + ((-7472) * e * f * g) + ((-4900) * e * i * k) + ((-374) * d * e * i) + (48 * f * g * k) + (8900 * f * i * k) + (18564 * d * f * i) + (20038 * d * e * g) + (20038 * d * f * g) + (21228 * d * i * k) + (87094 * d * f * k))) * hc1 +
    ((1 / 5145 : ℂ) * (((-424) * k * (f ^ 2)) + ((-210) * e * (f ^ 2)) + (315 * f * (e ^ 2)) + (385 * e * (k ^ 2)) + (424 * i * (f ^ 2)) + ((-32) * d * f * k) + (525 * d * e * f) + (984 * e * f * k))) * hc2 +
    ((-8 / 5145 : ℂ) * f * k * ((4 * d) + (53 * f))) * hc3

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma collinearArrowhead_classification (g i k d e f : ℂ)
    (hq0 : ((e ^ 2) + (f ^ 2) + ((-1) * (i ^ 2)) + ((-1) * (k ^ 2)) + ((-1) * i * k) + ((-2) * e * i) + ((-2) * f * k) + (2 * e * f)) = 0)
    (hq1 : (((-2) * (f ^ 2)) + (2 * (k ^ 2)) + (i * k) + ((-1) * g * i) + ((-1) * g * k) + ((-2) * e * f) + (2 * d * e) + (2 * d * f) + (4 * f * k)) = 0)
    (hq2 : ((d ^ 2) + (f ^ 2) + ((-1) * (g ^ 2)) + ((-1) * (k ^ 2)) + (g * k) + ((-2) * d * f) + ((-2) * d * g) + ((-2) * f * k)) = 0)
    (hc0 : ((i * (f ^ 2)) + (k * (e ^ 2)) + ((-1) * i * (k ^ 2)) + ((-1) * k * (i ^ 2)) + ((-2) * e * i * k) + ((-2) * f * i * k)) = 0)
    (hc1 : ((g * (e ^ 2)) + (g * (f ^ 2)) + (k * (i ^ 2)) + ((-1) * g * (i ^ 2)) + ((-1) * g * (k ^ 2)) + ((-1) * k * (e ^ 2)) + ((-2) * i * (f ^ 2)) + (2 * i * (k ^ 2)) + ((-2) * e * g * i) + ((-2) * f * g * k) + ((-2) * g * i * k) + (2 * d * e * k) + (2 * d * f * i) + (2 * e * f * g) + (2 * e * i * k) + (4 * f * i * k)) = 0)
    (hc2 : ((i * (d ^ 2)) + (i * (f ^ 2)) + (k * (d ^ 2)) + ((-1) * i * (g ^ 2)) + ((-1) * i * (k ^ 2)) + ((-1) * k * (g ^ 2)) + ((-2) * g * (f ^ 2)) + (2 * g * (k ^ 2)) + ((-2) * d * e * k) + ((-2) * d * f * i) + ((-2) * d * g * i) + ((-2) * d * g * k) + ((-2) * e * f * g) + ((-2) * f * i * k) + (2 * g * i * k) + (4 * f * g * k)) = 0)
    (hc3 : ((g * (f ^ 2)) + (k * (g ^ 2)) + ((-1) * g * (k ^ 2)) + ((-1) * k * (d ^ 2)) + ((-2) * f * g * k) + (2 * d * g * k)) = 0)
    (hrow0 : g ≠ 0 ∨ d ≠ 0) (hrow1 : i ≠ 0 ∨ e ≠ 0)
    (hrow2 : k ≠ 0 ∨ f ≠ 0)
    : g = 0 ∧ i = 0 ∧ k = 0 ∧ d = f ∧ e = -f := by
  have hd : d ≠ 0 := by
    intro hz
    have hp : g ^ 3 = 0 := by
      subst d
      linear_combination hc3 - g * hq2
    exact hrow0.elim (fun h => h (eq_zero_of_pow_eq_zero hp)) (fun h => h hz)
  have he : e ≠ 0 := by
    intro hz
    have hp : i ^ 3 = 0 := by
      subst e
      linear_combination hc0 - i * hq0
    exact hrow1.elim (fun h => h (eq_zero_of_pow_eq_zero hp)) (fun h => h hz)
  have hf : f ≠ 0 := by
    intro hz
    have hp : k ^ 3 = 0 := by
      subst f
      linear_combination hc0 - k * hq0
    exact hrow2.elim (fun h => h (eq_zero_of_pow_eq_zero hp)) (fun h => h hz)
  have hi : i = 0 := by
    have hp := collinearArrowhead_mid_annihilated g i k d e f hq0 hq1 hq2 hc0 hc1 hc2 hc3
    exact (mul_eq_zero.mp hp).resolve_left (mul_ne_zero (pow_ne_zero 2 he) (pow_ne_zero 3 hf))
  have hg : g = 0 := by
    have hp := collinearArrowhead_mid_annihilated i g (-k) e d (-f)
      (by linear_combination 1 * hq2)
      (by linear_combination 1 * hq1)
      (by linear_combination 1 * hq0)
      (by linear_combination 1 * hc3)
      (by linear_combination 1 * hc2)
      (by linear_combination 1 * hc1)
      (by linear_combination 1 * hc0)
    exact (mul_eq_zero.mp hp).resolve_left (mul_ne_zero (pow_ne_zero 2 hd) (pow_ne_zero 3 (neg_ne_zero.mpr hf)))
  have hk : k = 0 := by
    have hp := collinearArrowhead_mid_annihilated (-g) k i (-d) f e
      (by linear_combination 1 * hq0)
      (by linear_combination (-2) * hq0 + (-1) * hq1)
      (by linear_combination 1 * hq0 + 1 * hq1 + 1 * hq2)
      (by linear_combination 1 * hc0)
      (by linear_combination (-3) * hc0 + (-1) * hc1)
      (by linear_combination 3 * hc0 + 2 * hc1 + 1 * hc2)
      (by linear_combination (-1) * hc0 + (-1) * hc1 + (-1) * hc2 + (-1) * hc3)
    exact (mul_eq_zero.mp hp).resolve_left (mul_ne_zero (pow_ne_zero 2 hf) (pow_ne_zero 3 he))
  have hdf : d = f := by
    have hp : (d - f) ^ 2 = 0 := by
      subst g; subst i; subst k
      linear_combination hq2
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hp)
  have hef : e = -f := by
    have hp : (e + f) ^ 2 = 0 := by
      subst g; subst i; subst k
      linear_combination hq0
    exact eq_neg_of_add_eq_zero_left (eq_zero_of_pow_eq_zero hp)
  exact ⟨hg, hi, hk, hdf, hef⟩


namespace ArrowheadMatrix

lemma sum_perm_succ {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma perm4 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix.permanent M =
    (M 0 0 * M 1 1 + M 0 1 * M 1 0) * (M 2 2 * M 3 3 + M 2 3 * M 3 2) + (M 0 0 * M 1 2 + M 0 2 * M 1 0) * (M 2 1 * M 3 3 + M 2 3 * M 3 1) + (M 0 0 * M 1 3 + M 0 3 * M 1 0) * (M 2 1 * M 3 2 + M 2 2 * M 3 1) + (M 0 1 * M 1 2 + M 0 2 * M 1 1) * (M 2 0 * M 3 3 + M 2 3 * M 3 0) + (M 0 1 * M 1 3 + M 0 3 * M 1 1) * (M 2 0 * M 3 2 + M 2 2 * M 3 0) + (M 0 2 * M 1 3 + M 0 3 * M 1 2) * (M 2 0 * M 3 1 + M 2 1 * M 3 0) := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring


def arrowhead (g i k d e f m n x y : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![g*y, 0, 0, d*y], ![0, i*x, 0, e*x],
    ![0, 0, k*(x-y), f*(x-y)], ![d*y, e*x, f*(x-y), m*x+n*y]]

def star3 (u v : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0, 0, 0, u], ![0, 0, 0, v], ![0, 0, 0, -u-v], ![u, v, -u-v, 0]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma normalized_level_classification (g i k d e f : ℂ)
    (hp : ∀ x y : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + arrowhead g i k d e f (-i-k-2*e-2*f) (-g+k-2*d+2*f) x y r s) = 24)
    (hrow0 : g ≠ 0 ∨ d ≠ 0) (hrow1 : i ≠ 0 ∨ e ≠ 0)
    (hrow2 : k ≠ 0 ∨ f ≠ 0) :
    g = 0 ∧ i = 0 ∧ k = 0 ∧ d = f ∧ e = -f := by
  have hap := hp (1) (0)
  have ham := hp (-1) (0)
  have happ := hp (2) (0)
  have hamm := hp (-2) (0)
  have hbp := hp (0) (1)
  have hbm := hp (0) (-1)
  have hbpp := hp (0) (2)
  have hbmm := hp (0) (-2)
  have hcp := hp (1) (1)
  have hcm := hp (-1) (-1)
  have hcpp := hp (2) (2)
  have hcmm := hp (-2) (-2)
  have hdp := hp (1) (-1)
  have hdm := hp (-1) (1)
  have hdpp := hp (2) (-2)
  have hdmm := hp (-2) (2)
  simp [perm4, Matrix.of_apply, arrowhead] at hap ham happ hamm hbp hbm hbpp hbmm hcp hcm hcpp hcmm hdp hdm hdpp hdmm
  have hq0 : ((e ^ 2) + (f ^ 2) + ((-1) * (i ^ 2)) + ((-1) * (k ^ 2)) + ((-1) * i * k) + ((-2) * e * i) + ((-2) * f * k) + (2 * e * f)) = 0 := by
    linear_combination (1/3 : ℂ)*hap + (1/3 : ℂ)*ham - (1/48 : ℂ)*happ - (1/48 : ℂ)*hamm
  have hq2 : ((d ^ 2) + (f ^ 2) + ((-1) * (g ^ 2)) + ((-1) * (k ^ 2)) + (g * k) + ((-2) * d * f) + ((-2) * d * g) + ((-2) * f * k)) = 0 := by
    linear_combination (1/3 : ℂ)*hbp + (1/3 : ℂ)*hbm - (1/48 : ℂ)*hbpp - (1/48 : ℂ)*hbmm
  have hq1 : (((-2) * (f ^ 2)) + (2 * (k ^ 2)) + (i * k) + ((-1) * g * i) + ((-1) * g * k) + ((-2) * e * f) + (2 * d * e) + (2 * d * f) + (4 * f * k)) = 0 := by
    linear_combination (1/3 : ℂ)*hcp + (1/3 : ℂ)*hcm - (1/48 : ℂ)*hcpp - (1/48 : ℂ)*hcmm - hq0 - hq2
  have hc0 : ((i * (f ^ 2)) + (k * (e ^ 2)) + ((-1) * i * (k ^ 2)) + ((-1) * k * (i ^ 2)) + ((-2) * e * i * k) + ((-2) * f * i * k)) = 0 := by
    linear_combination (1/12 : ℂ)*happ - (1/12 : ℂ)*hamm - (1/6 : ℂ)*hap + (1/6 : ℂ)*ham
  have hc3 : ((g * (f ^ 2)) + (k * (g ^ 2)) + ((-1) * g * (k ^ 2)) + ((-1) * k * (d ^ 2)) + ((-2) * f * g * k) + (2 * d * g * k)) = 0 := by
    linear_combination (1/12 : ℂ)*hbpp - (1/12 : ℂ)*hbmm - (1/6 : ℂ)*hbp + (1/6 : ℂ)*hbm
  have hc1 : ((g * (e ^ 2)) + (g * (f ^ 2)) + (k * (i ^ 2)) + ((-1) * g * (i ^ 2)) + ((-1) * g * (k ^ 2)) + ((-1) * k * (e ^ 2)) + ((-2) * i * (f ^ 2)) + (2 * i * (k ^ 2)) + ((-2) * e * g * i) + ((-2) * f * g * k) + ((-2) * g * i * k) + (2 * d * e * k) + (2 * d * f * i) + (2 * e * f * g) + (2 * e * i * k) + (4 * f * i * k)) = 0 := by
    linear_combination (1/2 : ℂ)*((1/12 : ℂ)*hcpp - (1/12 : ℂ)*hcmm - (1/6 : ℂ)*hcp + (1/6 : ℂ)*hcm) - (1/2 : ℂ)*((1/12 : ℂ)*hdpp - (1/12 : ℂ)*hdmm - (1/6 : ℂ)*hdp + (1/6 : ℂ)*hdm) - hc3
  have hc2 : ((i * (d ^ 2)) + (i * (f ^ 2)) + (k * (d ^ 2)) + ((-1) * i * (g ^ 2)) + ((-1) * i * (k ^ 2)) + ((-1) * k * (g ^ 2)) + ((-2) * g * (f ^ 2)) + (2 * g * (k ^ 2)) + ((-2) * d * e * k) + ((-2) * d * f * i) + ((-2) * d * g * i) + ((-2) * d * g * k) + ((-2) * e * f * g) + ((-2) * f * i * k) + (2 * g * i * k) + (4 * f * g * k)) = 0 := by
    linear_combination (1/2 : ℂ)*((1/12 : ℂ)*hcpp - (1/12 : ℂ)*hcmm - (1/6 : ℂ)*hcp + (1/6 : ℂ)*hcm) + (1/2 : ℂ)*((1/12 : ℂ)*hdpp - (1/12 : ℂ)*hdmm - (1/6 : ℂ)*hdp + (1/6 : ℂ)*hdm) - hc0
  exact collinearArrowhead_classification g i k d e f hq0 hq1 hq2 hc0 hc1 hc2 hc3 hrow0 hrow1 hrow2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma level_classification (g i k d e f m n : ℂ)
    (hp : ∀ x y : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + arrowhead g i k d e f m n x y r s) = 24)
    (hrow0 : g ≠ 0 ∨ d ≠ 0) (hrow1 : i ≠ 0 ∨ e ≠ 0)
    (hrow2 : k ≠ 0 ∨ f ≠ 0) :
    g = 0 ∧ i = 0 ∧ k = 0 ∧ d = f ∧ e = -f ∧ m = 0 ∧ n = 0 := by
  have ha1 := hp 1 0
  have ham1 := hp (-1) 0
  have ha2 := hp 2 0
  have ham2 := hp (-2) 0
  have hb1 := hp 0 1
  have hbm1 := hp 0 (-1)
  have hb2 := hp 0 2
  have hbm2 := hp 0 (-2)
  simp [perm4, Matrix.of_apply, arrowhead] at ha1 ham1 ha2 ham2 hb1 hbm1 hb2 hbm2
  have hm : m = -i-k-2*e-2*f := by
    linear_combination (1/9 : ℂ)*ha1 - (1/9 : ℂ)*ham1 - (1/72 : ℂ)*ha2 + (1/72 : ℂ)*ham2
  have hn : n = -g+k-2*d+2*f := by
    linear_combination (1/9 : ℂ)*hb1 - (1/9 : ℂ)*hbm1 - (1/72 : ℂ)*hb2 + (1/72 : ℂ)*hbm2
  rw [hm, hn] at hp
  rcases normalized_level_classification g i k d e f hp hrow0 hrow1 hrow2 with
    ⟨hg, hi, hk, hd, he⟩
  refine ⟨hg, hi, hk, hd, he, ?_, ?_⟩
  · linear_combination hm - hi - hk - 2*he
  · linear_combination hn - hg + hk - 2*hd

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma three_collinear_zero_rows (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hsA : ∀ r s : Fin 4, A r s = A s r)
    (hsB : ∀ r s : Fin 4, B r s = B s r)
    (hA0 : ∀ j : Fin 4, A 0 j = 0)
    (hB1 : ∀ j : Fin 4, B 1 j = 0)
    (hAB2 : ∀ j : Fin 4, A 2 j + B 2 j = 0)
    (hp : ∀ x y : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + x*A r s + y*B r s) = 24)
    (hrow0 : ∃ j : Fin 4, B 0 j ≠ 0)
    (hrow1 : ∃ j : Fin 4, A 1 j ≠ 0)
    (hrow2 : ∃ j : Fin 4, A 2 j ≠ 0) :
    ∃ f : ℂ, f ≠ 0 ∧ A = star3 0 (-f) ∧ B = star3 f 0 := by
  have hA12 : A 1 2 = 0 := by
    have h := hAB2 1
    rw [hsB 2 1, hB1 2, add_zero] at h
    exact (hsA 1 2).trans h
  have hB02 : B 0 2 = 0 := by
    have h := hAB2 0
    rw [hsA 2 0, hA0 2, zero_add] at h
    exact (hsB 0 2).trans h
  have hB22 : B 2 2 = -A 2 2 := by linear_combination hAB2 2
  have hB23 : B 2 3 = -A 2 3 := by linear_combination hAB2 3
  have hAshape : A =
      ![![0,0,0,0], ![0,A 1 1,0,A 1 3],
        ![0,0,A 2 2,A 2 3], ![0,A 1 3,A 2 3,A 3 3]] := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [hA0, hA12, hsA 1 0, hsA 2 0, hsA 3 0,
        hsA 2 1, hsA 3 1, hsA 3 2]
  have hBshape : B =
      ![![B 0 0,0,0,B 0 3], ![0,0,0,0],
        ![0,0,-A 2 2,-A 2 3], ![B 0 3,0,-A 2 3,B 3 3]] := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [hB1, hB02, hB22, hB23, hsB 0 1,
        hsB 2 0, hsB 3 0, hsB 2 1, hsB 3 1, hsB 3 2]
  have hfamily (x y : ℂ) :
      Matrix.of (fun (r s : Fin 4) => x*A r s + y*B r s) =
      arrowhead (B 0 0) (A 1 1) (A 2 2) (B 0 3) (A 1 3) (A 2 3)
        (A 3 3) (B 3 3) x y := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [Matrix.of_apply, arrowhead, hA0, hB1, hA12, hB02, hB22, hB23,
        hsA 1 0, hsA 2 0, hsA 3 0, hsA 2 1, hsA 3 1, hsA 3 2,
        hsB 0 1, hsB 2 0, hsB 3 0, hsB 2 1, hsB 3 1, hsB 3 2] <;> ring
  have hp' : ∀ x y : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + arrowhead (B 0 0) (A 1 1) (A 2 2) (B 0 3) (A 1 3) (A 2 3)
        (A 3 3) (B 3 3) x y r s) = 24 := by
    intro x y
    rw [← hfamily x y]
    simpa only [Matrix.of_apply, add_assoc] using hp x y
  have h0 : B 0 0 ≠ 0 ∨ B 0 3 ≠ 0 := by
    by_cases hg : B 0 0 = 0
    · right
      intro hd
      rcases hrow0 with ⟨j, hj⟩
      fin_cases j <;> simp [hg, hd, hB02, hsB 0 1, hB1] at hj
    · exact Or.inl hg
  have h1 : A 1 1 ≠ 0 ∨ A 1 3 ≠ 0 := by
    by_cases hi : A 1 1 = 0
    · right
      intro he
      rcases hrow1 with ⟨j, hj⟩
      fin_cases j <;> simp [hi, he, hA12, hsA 1 0, hA0] at hj
    · exact Or.inl hi
  have h2 : A 2 2 ≠ 0 ∨ A 2 3 ≠ 0 := by
    by_cases hk : A 2 2 = 0
    · right
      intro hf
      rcases hrow2 with ⟨j, hj⟩
      fin_cases j <;> simp [hk, hf, hA12, hsA 2 0, hsA 2 1, hA0] at hj
    · exact Or.inl hk
  rcases level_classification (B 0 0) (A 1 1) (A 2 2) (B 0 3) (A 1 3) (A 2 3)
      (A 3 3) (B 3 3) hp' h0 h1 h2 with ⟨hg, hi, hk, hd, he, hm, hn⟩
  refine ⟨A 2 3, h2.resolve_left (fun h => h hk), ?_, ?_⟩
  · apply hAshape.trans
    ext r s
    fin_cases r <;> fin_cases s <;> simp [star3, hi, hk, he, hm]
  · apply hBshape.trans
    ext r s
    fin_cases r <;> fin_cases s <;> simp [star3, hg, hk, hd, hn]

end ArrowheadMatrix

end PEqualNP.Outside.L_gct_231
