import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace PEqualNP.Outside.L_gct_231_aux.Case2SlopeBoundary

def scaleCurve (P B : ℂ) : ℂ :=
  -6*B^2*P^2 - 6*B^2*P + 6*B^2 + 5*B*P^4 + 4*B*P^3 + 4*B*P^2 + 8*B*P - 10*B - 8*P^4 - 8*P^3 + 8*P^2
def chartDet (P B : ℂ) : ℂ :=
  9*B^2 - 6*B*P^2 - 12*B + 10*P^2
def curveLeading (P : ℂ) : ℂ := P^2 + P - 1
def rA (P B : ℂ) : ℂ :=
  40*B*P^14 + 156*B*P^13 + 22*B*P^12 - 336*B*P^11 - 248*B*P^10 + 56*B*P^9 + 892*B*P^8 - 192*B*P^7 - 2704*B*P^6 + 1168*B*P^5 + 3304*B*P^4 - 1088*B*P^3 - 1728*B*P^2 + 160*B*P + 400*B - 64*P^14 - 288*P^13 - 16*P^12 + 688*P^11 - 464*P^10 - 576*P^9 + 1856*P^8 - 704*P^7 - 2752*P^6 + 768*P^5 + 1472*P^4 - 64*P^3 - 320*P^2
def rB (P B : ℂ) : ℂ :=
  25*B*P^14 - 10*B*P^13 - 120*B*P^12 + 224*B*P^11 + 586*B*P^10 - 436*B*P^9 - 1360*B*P^8 - 144*B*P^7 + 604*B*P^6 - 632*B*P^5 - 272*B*P^4 + 1248*B*P^3 + 88*B*P^2 - 624*B*P + 160*B - 40*P^14 + 8*P^13 + 184*P^12 - 336*P^11 - 896*P^10 + 352*P^9 + 1696*P^8 + 1152*P^7 - 544*P^6 - 1376*P^5 - 32*P^4 + 576*P^3 - 128*P^2

def boundaryQuartic (P : ℂ) : ℂ :=
  P^4 - 2*P^3 + 4*P + 2

def normA (P : ℂ) : ℂ :=
  20*P^13 + 62*P^12 - 173*P^11 - 664*P^10 + 94*P^9 + 1489*P^8 - 180*P^7 - 2008*P^6 + 320*P^5 + 1364*P^4 - 228*P^3 - 528*P^2 + 40*P + 100

def normB (P : ℂ) : ℂ :=
  25*P^13 - 10*P^12 - 216*P^11 + 180*P^10 + 1124*P^9 - 1112*P^8 - 4528*P^7 + 576*P^6 + 6340*P^5 - 136*P^4 - 4480*P^3 + 560*P^2 + 1184*P - 320

def affineMultiplier (P : ℂ) : ℂ :=
  88320*P^3 + 21632*P^2 - 92800*P - 48128

def affineRelation (P B : ℂ) : ℂ :=
  3*B + P^3 - 2*P^2

set_option maxHeartbeats 800000 in
theorem norms_inconsistent (P : ℂ) (hR : normA P = 0) (hS : normB P = 0) : False := by
  unfold normA at hR
  unfold normB at hS
  have h : (91612984850589100953600 : ℂ) = 0 := by
    linear_combination (-1052919594843191845275*P^12 + 593975870383886633735*P^11 + 8482679206891900632676*P^10 - 8715264505954999771530*P^9 - 41749621740444919668074*P^8 + 49676790555246700806962*P^7 + 161966764124092107152208*P^6 - 27857142540088439713756*P^5 - 182334381525912206960560*P^4 + 27619872417530455406016*P^3 + 97767827655230524191920*P^2 - 29528767614191324388640*P + 1318259783250408788416) * hR +
      (842335675874553476220*P^12 + 2472994169253827859782*P^11 - 7278429213122773748653*P^10 - 25529583173499415476599*P^9 + 4674238596094701615924*P^8 + 49246560789298355043199*P^7 - 14311917019195305362155*P^6 - 58573459826805411404028*P^5 + 17266894698438568857890*P^4 + 26275743411838909576274*P^3 - 6906443920890657716118*P^2 - 8597994669480139091068*P + 125665604607661805900) * hS
  norm_num at h

set_option maxHeartbeats 800000 in
theorem affine_multiplier_nonzero (P : ℂ) (hQ : boundaryQuartic P = 0) : affineMultiplier P ≠ 0 := by
  intro hA
  unfold affineMultiplier at hA
  unfold boundaryQuartic at hQ
  have h : (27406080 : ℂ) = 0 := by
    linear_combination (155217*P^3 - 341680*P^2 + 29850*P + 745898) * hA +
      (-13708765440*P^2 - 598007424*P + 17962992512) * hQ
  norm_num at h

set_option maxHeartbeats 1000000 in
theorem rA_norm_vanishes (P B : ℂ)
    (hF : scaleCurve P B = 0) (ha : rA P B = 0) :
    256 * P^4 * curveLeading P^3 * boundaryQuartic P^2 * normA P = 0 := by
  unfold scaleCurve at hF
  unfold rA at ha
  unfold curveLeading boundaryQuartic normA
  linear_combination (40*P^14 + 156*P^13 + 22*P^12 - 336*P^11 - 248*P^10 + 56*P^9 + 892*P^8 - 192*P^7 - 2704*P^6 + 1168*P^5 + 3304*P^4 - 1088*P^3 - 1728*P^2 + 160*P + 400)^2 * hF +
    (240*B*P^16 + 1176*B*P^15 + 828*B*P^14 - 2820*B*P^13 - 3636*B*P^12 + 864*B*P^11 + 7176*B*P^10 + 3864*B*P^9 - 22728*B*P^8 - 8064*B*P^7 + 43056*B*P^6 + 6288*B*P^5 - 36720*B*P^4 - 2880*B*P^3 + 13728*B*P^2 + 1440*B*P - 2400*B - 200*P^18 - 940*P^17 - 510*P^16 + 2760*P^15 + 3088*P^14 - 2320*P^13 - 2224*P^12 + 6160*P^11 - 2672*P^10 - 11200*P^9 + 31952*P^8 + 14944*P^7 - 66560*P^6 - 8128*P^5 + 57152*P^4 + 2240*P^3 - 22080*P^2 - 1600*P + 4000) * ha

set_option maxHeartbeats 1000000 in
theorem rB_norm_vanishes (P B : ℂ)
    (hF : scaleCurve P B = 0) (ha : rB P B = 0) :
    64 * P^3 * curveLeading P^3 * boundaryQuartic P^2 * normB P = 0 := by
  unfold scaleCurve at hF
  unfold rB at ha
  unfold curveLeading boundaryQuartic normB
  linear_combination (25*P^14 - 10*P^13 - 120*P^12 + 224*P^11 + 586*P^10 - 436*P^9 - 1360*P^8 - 144*P^7 + 604*P^6 - 632*P^5 - 272*P^4 + 1248*P^3 + 88*P^2 - 624*P + 160)^2 * hF +
    (150*B*P^16 + 90*B*P^15 - 930*B*P^14 + 684*B*P^13 + 5580*B*P^12 - 444*B*P^11 - 14292*B*P^10 - 6408*B*P^9 + 10920*B*P^8 + 696*B*P^7 - 9048*B*P^6 + 9648*B*P^5 + 9648*B*P^4 - 10704*B*P^3 - 3312*B*P^2 + 4704*B*P - 960*B - 125*P^18 - 50*P^17 + 780*P^16 - 608*P^15 - 4408*P^14 + 760*P^13 + 11704*P^12 + 6704*P^11 - 5320*P^10 - 7136*P^9 - 4448*P^8 + 9536*P^7 + 11936*P^6 - 17888*P^5 - 14240*P^4 + 17856*P^3 + 4464*P^2 - 7520*P + 1600) * ha

set_option maxHeartbeats 800000 in
theorem slopes_nonzero (P B : ℂ)
    (hF : scaleCurve P B = 0) (hn : P * B * chartDet P B ≠ 0) :
    rA P B ≠ 0 ∨ rB P B ≠ 0 := by
  have hP : P ≠ 0 := by
    intro h
    exact hn (by simp [h])
  have hB : B ≠ 0 := by
    intro h
    exact hn (by simp [h])
  have hW : chartDet P B ≠ 0 := by
    intro h
    exact hn (by simp [h])
  have hK : curveLeading P ≠ 0 := by
    intro hK
    have hpb : (3 : ℂ) * P * B = 0 := by
      unfold scaleCurve at hF
      unfold curveLeading at hK
      linear_combination -hF + (-6*B^2 + (5*P^2-P+10)*B - 8*P^2) * hK
    exact mul_ne_zero (mul_ne_zero (by norm_num) hP) hB hpb
  by_cases ha : rA P B = 0
  · right
    intro hb
    have hna := rA_norm_vanishes P B hF ha
    have hnb := rB_norm_vanishes P B hF hb
    have hQ : boundaryQuartic P = 0 := by
      by_contra hQ
      have hfa : (256 : ℂ) * P^4 * curveLeading P^3 * boundaryQuartic P^2 ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hP))
          (pow_ne_zero 3 hK)) (pow_ne_zero 2 hQ)
      have hfb : (64 : ℂ) * P^3 * curveLeading P^3 * boundaryQuartic P^2 ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hP))
          (pow_ne_zero 3 hK)) (pow_ne_zero 2 hQ)
      exact norms_inconsistent P ((mul_eq_zero.mp hna).resolve_left hfa)
        ((mul_eq_zero.mp hnb).resolve_left hfb)
    have hprod : affineMultiplier P * affineRelation P B = 0 := by
      unfold rA at ha
      unfold boundaryQuartic at hQ
      unfold affineMultiplier affineRelation
      linear_combination ha - (40*B*P^10 + 236*B*P^9 + 494*B*P^8 + 492*B*P^7 - 288*B*P^6 - 2968*B*P^5 - 8000*B*P^4 - 16024*B*P^3 - 22304*B*P^2 - 5504*B*P + 72392*B - 64*P^10 - 416*P^9 - 848*P^8 - 752*P^7 - 176*P^6 + 3296*P^5 + 13152*P^4 + 27808*P^3 - 48288*P^2) * hQ
    have hrel : affineRelation P B = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (affine_multiplier_nonzero P hQ)
    apply hW
    unfold chartDet
    unfold affineRelation at hrel
    unfold boundaryQuartic at hQ
    linear_combination (3*B-P^3-4) * hrel + P^2 * hQ
  · exact Or.inl ha

end PEqualNP.Outside.L_gct_231_aux.Case2SlopeBoundary

#print axioms PEqualNP.Outside.L_gct_231_aux.Case2SlopeBoundary.slopes_nonzero
