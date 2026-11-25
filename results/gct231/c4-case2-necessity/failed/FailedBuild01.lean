import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum

namespace PEqualNP.Outside.L_gct_231_aux

theorem resultant_zero_of_common_root {K : Type*} [Field K]
    (f g : Polynomial K) (z : K) (m n : ℕ)
    (hm : f.natDegree ≤ m) (hn : g.natDegree ≤ n) (hpos : 0 < m)
    (hf : f.eval z = 0) (hg : g.eval z = 0) :
    Polynomial.resultant f g m n = 0 := by
  classical
  by_cases hne : f ≠ 0 ∨ g ≠ 0
  · have hbase : Polynomial.resultant f g = 0 := by
      apply Polynomial.resultant_eq_zero_iff.mpr
      refine ⟨hne, ?_⟩
      rintro ⟨a, b, hab⟩
      have he := congrArg (Polynomial.eval z) hab
      simp [Polynomial.eval_add, Polynomial.eval_mul, hf, hg] at he
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le hn
    rw [hk, hl]
    rw [Polynomial.resultant_add_left_deg f g f.natDegree
      (g.natDegree + l) k (le_refl _)]
    rw [Polynomial.resultant_add_right_deg f g f.natDegree g.natDegree l (le_refl _)]
    rw [hbase]
    simp
  · have hf0 : f = 0 := by
      by_contra h
      exact hne (Or.inl h)
    have hg0 : g = 0 := by
      by_contra h
      exact hne (Or.inr h)
    have hsum : m + n ≠ 0 := by omega
    rw [hf0, hg0, Polynomial.resultant_zero_zero]
    exact zero_pow hsum

end PEqualNP.Outside.L_gct_231_aux

namespace PEqualNP.Outside.L_gct_231_aux.Case2Necessity

open Polynomial

def originalQ (P B U V : ℂ) : ℂ :=
  -6*B*U^2 + 3*B*V^2 + 36*B + 4*P^2*U^2 + 4*P*U*V - 4*V^2

def originalC (P B U V : ℂ) : ℂ :=
  9*B*V^2 - 36*B + 2*P^2*U^3 - 28*P^2*U^2 - 4*P*U^2*V - 2*P*U*V^2 + 20*P*U*V - V^3 - 2*V^2

def scaleCurve (P B : ℂ) : ℂ :=
  -6*B^2*P^2 - 6*B^2*P + 6*B^2 + 5*B*P^4 + 4*B*P^3 + 4*B*P^2 + 8*B*P - 10*B - 8*P^4 - 8*P^3 + 8*P^2

def originalR (P B U V : ℂ) : ℂ :=
  27*B^4*P^2*V - 54*B^4*P^2 - 108*B^4*P*U - 54*B^4*P*V - 540*B^4*P - 54*B^4*U - 756*B^4 - 72*B^3*P^4*U - 18*B^3*P^4*V + 252*B^3*P^4 + 144*B^3*P^3*U + 108*B^3*P^3*V + 720*B^3*P^3 + 36*B^3*P^2*U - 36*B^3*P^2*V + 1152*B^3*P^2 + 216*B^3*P*U + 144*B^3*P*V + 1440*B^3*P + 72*B^3*U + 72*B^3*V + 1764*B^3 + 66*B^2*P^6*U - 228*B^2*P^6 - 60*B^2*P^5*U - 60*B^2*P^5*V - 240*B^2*P^5 + 192*B^2*P^4*U + 36*B^2*P^4*V - 1032*B^2*P^4 - 264*B^2*P^3*U - 276*B^2*P^3*V - 2448*B^2*P^3 - 72*B^2*P^2*U - 168*B^2*P^2*V - 2784*B^2*P^2 - 120*B^2*P*U - 120*B^2*P*V - 960*B^2*P - 132*B^2*V - 888*B^2 + 8*B*P^7*U - 176*B*P^6*U + 4*B*P^6*V + 636*B*P^6 + 72*B*P^5*U + 160*B*P^5*V + 1104*B*P^5 - 136*B*P^4*U + 88*B*P^4*V + 1488*B*P^4 + 112*B*P^3*U + 168*B*P^3*V + 2064*B*P^3 - 16*B*P^2*U + 272*B*P^2*V + 1632*B*P^2 + 32*B*P*V - 16*P^7*U + 128*P^6*U - 8*P^6*V - 432*P^6 - 96*P^5*V - 1152*P^5 + 16*P^4*U - 160*P^4*V - 768*P^4 - 32*P^3*V

def originalL (P B U V : ℂ) : ℂ :=
  -18*B^2*P^2*U^2 + 9*B^2*P^2*U*V + 90*B^2*P^2*U + 18*B^2*P*U*V + 18*B^2*U*V - 9*B^2*V^2 + 36*B^2*V + 21*B*P^4*U^2 - 6*B*P^4*U*V - 144*B*P^4*U - 24*B*P^3*U*V - 3*B*P^3*V^2 + 12*B*P^3*V + 24*B*P^2*U^2 - 24*B*P^2*U*V - 120*B*P^2*U + 6*B*P^2*V^2 - 24*B*P^2*V + 12*B*P*U^2 - 12*B*P*U*V - 60*B*P*U - 24*B*U*V + 21*B*V^2 - 108*B*V - 28*P^4*U^2 + 14*P^4*U*V + 192*P^4*U - 14*P^3*U^2 + 28*P^3*U*V + 96*P^3*U + 7*P^3*V^2 - 36*P^3*V + 28*P^2*U*V - 14*P^2*V^2 + 72*P^2*V

def chartDet (P B : ℂ) : ℂ :=
  9*B^2 - 6*B*P^2 - 12*B + 10*P^2

def curveLeading (P : ℂ) : ℂ := P^2 + P - 1

def rA (P B : ℂ) : ℂ :=
  40*B*P^14 + 156*B*P^13 + 22*B*P^12 - 336*B*P^11 - 248*B*P^10 + 56*B*P^9 + 892*B*P^8 - 192*B*P^7 - 2704*B*P^6 + 1168*B*P^5 + 3304*B*P^4 - 1088*B*P^3 - 1728*B*P^2 + 160*B*P + 400*B - 64*P^14 - 288*P^13 - 16*P^12 + 688*P^11 - 464*P^10 - 576*P^9 + 1856*P^8 - 704*P^7 - 2752*P^6 + 768*P^5 + 1472*P^4 - 64*P^3 - 320*P^2

def rB (P B : ℂ) : ℂ :=
  25*B*P^14 - 10*B*P^13 - 120*B*P^12 + 224*B*P^11 + 586*B*P^10 - 436*B*P^9 - 1360*B*P^8 - 144*B*P^7 + 604*B*P^6 - 632*B*P^5 - 272*B*P^4 + 1248*B*P^3 + 88*B*P^2 - 624*B*P + 160*B - 40*P^14 + 8*P^13 + 184*P^12 - 336*P^11 - 896*P^10 + 352*P^9 + 1696*P^8 + 1152*P^7 - 544*P^6 - 1376*P^5 - 32*P^4 + 576*P^3 - 128*P^2

def rC (P B : ℂ) : ℂ :=
  -370*B*P^14 - 1316*B*P^13 + 68*B*P^12 + 3888*B*P^11 + 2500*B*P^10 - 1568*B*P^9 - 992*B*P^8 + 1312*B*P^7 + 1832*B*P^6 + 496*B*P^5 + 368*B*P^4 - 4032*B*P^3 - 2960*B*P^2 + 2368*B*P + 640*B + 592*P^14 + 2224*P^13 + 304*P^12 - 5952*P^11 - 3360*P^10 + 3776*P^9 + 384*P^8 - 3584*P^7 - 1536*P^6 + 4032*P^5 + 3136*P^4 - 1792*P^3 - 512*P^2

def l20 (P B : ℂ) : ℂ :=
  12*B*P^6 + 18*B*P^5 - 18*B*P^4 + 24*B*P^3 + 36*B*P^2 - 24*B*P - 8*P^6 - 36*P^5 - 20*P^4 + 28*P^3

def l11 (P B : ℂ) : ℂ :=
  3*B*P^6 - 18*B*P^5 - 18*B*P^4 + 48*B*P^3 + 18*B*P^2 - 36*B*P - 12*B + 4*P^6 + 12*P^5 + 12*P^4 - 8*P^2

def l10 (P B : ℂ) : ℂ :=
  -138*B*P^6 - 168*B*P^5 + 168*B*P^4 - 120*B*P^3 - 180*B*P^2 + 120*B*P + 144*P^6 + 336*P^5 + 48*P^4 - 192*P^3

def l02 (P B : ℂ) : ℂ :=
  -6*B*P^5 - 9*B*P^4 + 6*B*P^3 + 18*B*P^2 + 18*B*P - 12*B + 14*P^5 + 10*P^4 - 18*P^3 + 4*P^2

def l01 (P B : ℂ) : ℂ :=
  24*B*P^5 + 36*B*P^4 - 24*B*P^3 - 120*B*P^2 - 120*B*P + 96*B - 72*P^5 - 24*P^4 + 120*P^3 - 48*P^2

set_option maxHeartbeats 800000 in
theorem reduced_linear (P B U V : ℂ)
    (hF : scaleCurve P B = 0) (h : originalR P B U V = 0) :
    rA P B * U + rB P B * V + rC P B = 0 := by
  unfold scaleCurve originalR at *
  unfold rA rB rC 
  linear_combination (8*P^6 + 24*P^5 - 40*P^3 + 24*P - 8) * h + (36*B^2*P^6*V - 72*B^2*P^6 - 144*B^2*P^5*U - 864*B^2*P^5 - 360*B^2*P^4*U - 180*B^2*P^4*V - 2376*B^2*P^4 - 1152*B^2*P^3 + 360*B^2*P^2*U + 180*B^2*P^2*V + 2376*B^2*P^2 - 72*B^2*P*V + 1296*B^2*P - 72*B^2*U - 1008*B^2 - 96*B*P^8*U + 6*B*P^8*V + 276*B*P^8 - 120*B*P^7*U + 90*B*P^7*V + 924*B*P^7 + 252*B*P^6*U + 174*B*P^6*V + 1164*B*P^6 + 204*B*P^5*U + 12*B*P^5*V + 1392*B*P^5 - 84*B*P^4*U + 84*B*P^4*V + 1680*B*P^4 + 48*B*P^3*U + 204*B*P^3*V + 264*B*P^3 - 120*B*P^2*U - 252*B*P^2*V - 1608*B*P^2 + 72*B*P*U - 120*B*P*V - 960*B*P - 24*B*U + 96*B*V + 672*B + 8*P^10*U + 5*P^10*V - 74*P^10 + 12*P^9*U - 6*P^9*V - 204*P^9 + 78*P^8*U - 20*P^8*V - 340*P^8 + 232*P^7*U - 64*P^7*V - 1568*P^7 - 292*P^6*V - 2576*P^6 - 288*P^5*U - 288*P^5*V + 392*P^5 + 8*P^4*U + 168*P^4*V + 2744*P^4 + 112*P^3*U + 176*P^3*V + 640*P^3 + 112*P^2*U - 60*P^2*V - 728*P^2 - 48*P*U + 24*P*V - 288*P - 40*U - 16*V - 64) * hF

set_option maxHeartbeats 800000 in
theorem reduced_quadratic (P B U V : ℂ)
    (hF : scaleCurve P B = 0) (h : originalL P B U V = 0) :
    l20 P B * U^2 + (l11 P B * V + l10 P B) * U + l02 P B * V^2 + l01 P B * V = 0 := by
  unfold scaleCurve originalL at *
  unfold l20 l11 l10 l02 l01 
  linear_combination (2*P^2 + 2*P - 2) * h + (-6*P^2*U^2 + 3*P^2*U*V + 30*P^2*U + 6*P*U*V + 6*U*V - 3*V^2 + 12*V) * hF

theorem chart_nonzero (P B U V sat : ℂ)
    (hF : scaleCurve P B = 0)
    (hs : P * B * chartDet P B * sat - 1 = 0) :
    P ≠ 0 ∧ B ≠ 0 ∧ curveLeading P ≠ 0 ∧ chartDet P B ≠ 0 := by
  have hs' : P * B * chartDet P B * sat = 1 := sub_eq_zero.mp hs
  have hP : P ≠ 0 := by
    intro h
    simpa [h] using hs'
  have hB : B ≠ 0 := by
    intro h
    simpa [h] using hs'
  have hW : chartDet P B ≠ 0 := by
    intro h
    simpa [h] using hs'
  refine ⟨hP, hB, ?_, hW⟩
  intro hK
  have hpb : (3 : ℂ) * P * B = 0 := by
    unfold scaleCurve at hF
    unfold curveLeading at hK
    linear_combination -hF + (-6*B^2 + (5*P^2-P+10)*B - 8*P^2) * hK
  exact mul_ne_zero (mul_ne_zero (by norm_num) hP) hB hpb

theorem eliminate_quadratic (a t u A D E : ℂ)
    (hr : a*u+t=0) (hq : A*u^2+D*u+E=0) :
    A*t^2-a*D*t+a^2*E=0 := by
  linear_combination a^2*hq - (A*(a*u-t)+a*D)*hr

theorem eliminate_cubic (a t u A D E F : ℂ)
    (hr : a*u+t=0) (hc : A*u^3+D*u^2+E*u+F=0) :
    -A*t^3+a*D*t^2-a^2*E*t+a^3*F=0 := by
  linear_combination a^3*hc -
    (A*(a^2*u^2-a*u*t+t^2)+a*D*(a*u-t)+a^2*E)*hr

def affinePolynomial (P B : ℂ) : Polynomial ℂ :=
  C (rB P B) * X + C (rC P B)

def qEliminant (P B : ℂ) : Polynomial ℂ :=
  C (4*P^2-6*B) * affinePolynomial P B ^ 2 -
  C (rA P B) * (C (4*P) * X) * affinePolynomial P B +
  C (rA P B ^ 2) * (C (3*B-4) * X^2 + C (36*B))

def lEliminant (P B : ℂ) : Polynomial ℂ :=
  C (l20 P B) * affinePolynomial P B ^ 2 -
  C (rA P B) * (C (l11 P B) * X + C (l10 P B)) * affinePolynomial P B +
  C (rA P B ^ 2) * (C (l02 P B) * X^2 + C (l01 P B) * X)

def cEliminant (P B : ℂ) : Polynomial ℂ :=
  -C (2*P^2) * affinePolynomial P B ^ 3 +
  C (rA P B) * (C (-28*P^2) - C (4*P) * X) * affinePolynomial P B ^ 2 -
  C (rA P B ^ 2) * (-C (2*P) * X^2 + C (20*P) * X) * affinePolynomial P B +
  C (rA P B ^ 3) * (-X^3 + C (9*B-2) * X^2 - C (36*B))

theorem eliminant_degree_bounds (P B : ℂ) :
    (qEliminant P B).natDegree ≤ 2 ∧
    (lEliminant P B).natDegree ≤ 2 ∧
    (cEliminant P B).natDegree ≤ 3 := by
  unfold qEliminant lEliminant cEliminant affinePolynomial
  constructor
  · compute_degree
  constructor <;> compute_degree

set_option maxHeartbeats 600000 in
theorem eliminants_vanish (P B U V : ℂ)
    (hq : originalQ P B U V = 0) (hc : originalC P B U V = 0)
    (hF : scaleCurve P B = 0) (hr : originalR P B U V = 0)
    (hl : originalL P B U V = 0) :
    (qEliminant P B).eval V = 0 ∧
    (lEliminant P B).eval V = 0 ∧
    (cEliminant P B).eval V = 0 := by
  have hr' := reduced_linear P B U V hF hr
  have hl' := reduced_quadratic P B U V hF hl
  have hline : rA P B * U + (rB P B * V + rC P B) = 0 := by
    simpa [add_assoc] using hr'
  have hq' : (4*P^2-6*B)*U^2+(4*P*V)*U+((3*B-4)*V^2+36*B)=0 := by
    unfold originalQ at hq
    linear_combination hq
  have hc' : (2*P^2)*U^3+(-28*P^2-4*P*V)*U^2+
      (-2*P*V^2+20*P*V)*U+(-V^3+(9*B-2)*V^2-36*B)=0 := by
    unfold originalC at hc
    linear_combination hc
  have hqe := eliminate_quadratic (rA P B) (rB P B * V + rC P B) U _ _ _ hline hq'
  have hl'' : l20 P B * U^2 + (l11 P B * V + l10 P B) * U +
      (l02 P B * V^2 + l01 P B * V) = 0 := by
    simpa [add_assoc] using hl'
  have hle := eliminate_quadratic (rA P B) (rB P B * V + rC P B) U _ _ _ hline hl''
  have hce := eliminate_cubic (rA P B) (rB P B * V + rC P B) U _ _ _ _ hline hc'
  simp only [qEliminant, lEliminant, cEliminant, affinePolynomial,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_X]
  exact ⟨hqe, hle, hce⟩


def originalSaturation (P B sat : ℂ) : ℂ :=
  9*B^3*P*sat - 6*B^2*P^3*sat - 12*B^2*P*sat + 10*B*P^3*sat - 1

theorem raw_resultants_vanish (P B U V : ℂ)
    (hq : originalQ P B U V = 0) (hc : originalC P B U V = 0)
    (hF : scaleCurve P B = 0) (hr : originalR P B U V = 0)
    (hl : originalL P B U V = 0) :
    Polynomial.resultant (qEliminant P B) (lEliminant P B) 2 2 = 0 ∧
    Polynomial.resultant (qEliminant P B) (cEliminant P B) 2 3 = 0 := by
  obtain ⟨hqe, hle, hce⟩ := eliminants_vanish P B U V hq hc hF hr hl
  obtain ⟨hqdeg, hldeg, hcdeg⟩ := eliminant_degree_bounds P B
  exact ⟨resultant_zero_of_common_root _ _ V 2 2 hqdeg hldeg (by decide) hqe hle,
    resultant_zero_of_common_root _ _ V 2 3 hqdeg hcdeg (by decide) hqe hce⟩

theorem six_equations_necessary (P B U V sat : ℂ)
    (hq : originalQ P B U V = 0) (hc : originalC P B U V = 0)
    (hF : scaleCurve P B = 0) (hr : originalR P B U V = 0)
    (hl : originalL P B U V = 0) (hs : originalSaturation P B sat = 0) :
    P ≠ 0 ∧ B ≠ 0 ∧ curveLeading P ≠ 0 ∧ chartDet P B ≠ 0 ∧
    Polynomial.resultant (qEliminant P B) (lEliminant P B) 2 2 = 0 ∧
    Polynomial.resultant (qEliminant P B) (cEliminant P B) 2 3 = 0 := by
  have hs' : P * B * chartDet P B * sat - 1 = 0 := by
    unfold originalSaturation at hs
    unfold chartDet
    linear_combination hs
  obtain ⟨hP, hB, hK, hW⟩ := chart_nonzero P B U V sat hF hs'
  obtain ⟨hql, hqc⟩ := raw_resultants_vanish P B U V hq hc hF hr hl
  exact ⟨hP, hB, hK, hW, hql, hqc⟩

end PEqualNP.Outside.L_gct_231_aux.Case2Necessity
