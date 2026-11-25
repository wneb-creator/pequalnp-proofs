import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.FinCases


namespace PEqualNP.Outside.L_gct_231_aux.AllZeroSignGluing

theorem binary_coefficients (A B C p q : ℂ)
    (H : ∀ x y : ℂ, (A * x ^ 2 + B * x * y + C * y ^ 2) ^ 2 = 24 * (p * x + q * y) ^ 4) :
    A ^ 2 = 24 * p ^ 4 ∧ 2 * A * B = 96 * p ^ 3 * q ∧
      B ^ 2 + 2 * A * C = 144 * p ^ 2 * q ^ 2 ∧ C ^ 2 = 24 * q ^ 4 := by
  have h0 := H 1 0
  have h1 := H 1 1
  have hn1 := H 1 (-1)
  have h2 := H 1 2
  have hn2 := H 1 (-2)
  have hi := H 0 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination h0
  · linear_combination (2 / 3 : ℂ) * (h1 - hn1) - (1 / 12 : ℂ) * (h2 - hn2)
  · linear_combination (2 / 3 : ℂ) * (h1 + hn1) - (1 / 24 : ℂ) * (h2 + hn2) - (5 / 4 : ℂ) * h0
  · linear_combination hi

theorem binary_first (A B C p q h : ℂ) (hh : h ^ 2 = 24) (hp : p ≠ 0)
    (hA : A = h * p ^ 2)
    (H : ∀ x y : ℂ, (A * x ^ 2 + B * x * y + C * y ^ 2) ^ 2 = 24 * (p * x + q * y) ^ 4) :
    B = 2 * h * p * q ∧ C = h * q ^ 2 := by
  obtain ⟨_, h3, h2, _⟩ := binary_coefficients A B C p q H
  have hn : h ≠ 0 := by
    intro hz
    rw [hz] at hh
    norm_num at hh
  have hs : 2 * h * p ^ 2 ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hn) (pow_ne_zero 2 hp)
  rw [hA] at h3 h2
  have hB0 : (2 * h * p ^ 2) * (B - 2 * h * p * q) = 0 := by
    linear_combination h3 - 4 * p ^ 3 * q * hh
  have hB : B = 2 * h * p * q := sub_eq_zero.mp ((mul_eq_zero.mp hB0).resolve_left hs)
  rw [hB] at h2
  have hC0 : (2 * h * p ^ 2) * (C - h * q ^ 2) = 0 := by
    linear_combination h2 - 6 * p ^ 2 * q ^ 2 * hh
  exact ⟨hB, sub_eq_zero.mp ((mul_eq_zero.mp hC0).resolve_left hs)⟩

theorem binary_mixed (A B C p q h : ℂ) (hh : h ^ 2 = 24)
    (hA : A = h * p ^ 2)
    (H : ∀ x y : ℂ, (A * x ^ 2 + B * x * y + C * y ^ 2) ^ 2 = 24 * (p * x + q * y) ^ 4) :
    B = 2 * h * p * q := by
  by_cases hp : p = 0
  · obtain ⟨_, _, h2, _⟩ := binary_coefficients A B C p q H
    have hB : B ^ 2 = 0 := by
      rw [hA, hp] at h2
      simpa using h2
    simpa [hp] using eq_zero_of_pow_eq_zero hB
  · exact (binary_first A B C p q h hh hp hA H).1

theorem anchored_known (A B C D E F p q r h : ℂ) (hh : h ^ 2 = 24) (hp : p ≠ 0)
    (hA : A = h * p ^ 2)
    (Hxy : ∀ x y : ℂ, (A * x ^ 2 + 2 * D * x * y + B * y ^ 2) ^ 2 = 24 * (p * x + q * y) ^ 4)
    (Hxz : ∀ x z : ℂ, (A * x ^ 2 + 2 * E * x * z + C * z ^ 2) ^ 2 = 24 * (p * x + r * z) ^ 4)
    (Hyz : ∀ y z : ℂ, (B * y ^ 2 + 2 * F * y * z + C * z ^ 2) ^ 2 = 24 * (q * y + r * z) ^ 4) :
    A = h * p ^ 2 ∧ B = h * q ^ 2 ∧ C = h * r ^ 2 ∧
      D = h * p * q ∧ E = h * p * r ∧ F = h * q * r := by
  have hAB := binary_first A (2 * D) B p q h hh hp hA Hxy
  have hAC := binary_first A (2 * E) C p r h hh hp hA Hxz
  have hF := binary_mixed B (2 * F) C q r h hh hAB.2 Hyz
  refine ⟨hA, hAB.2, hAC.2, ?_, ?_, ?_⟩
  · linear_combination (1 / 2 : ℂ) * hAB.1
  · linear_combination (1 / 2 : ℂ) * hAC.1
  · linear_combination (1 / 2 : ℂ) * hF

theorem anchored_glue (A B C D E F p q r h : ℂ) (hh : h ^ 2 = 24) (hp : p ≠ 0)
    (Hxy : ∀ x y : ℂ, (A * x ^ 2 + 2 * D * x * y + B * y ^ 2) ^ 2 = 24 * (p * x + q * y) ^ 4)
    (Hxz : ∀ x z : ℂ, (A * x ^ 2 + 2 * E * x * z + C * z ^ 2) ^ 2 = 24 * (p * x + r * z) ^ 4)
    (Hyz : ∀ y z : ℂ, (B * y ^ 2 + 2 * F * y * z + C * z ^ 2) ^ 2 = 24 * (q * y + r * z) ^ 4) :
    ∃ k : ℂ, k ^ 2 = 24 ∧ A = k * p ^ 2 ∧ B = k * q ^ 2 ∧ C = k * r ^ 2 ∧
      D = k * p * q ∧ E = k * p * r ∧ F = k * q * r := by
  have hAA := (binary_coefficients A (2 * D) B p q Hxy).1
  have hf : (A - h * p ^ 2) * (A + h * p ^ 2) = 0 := by
    linear_combination hAA - p ^ 4 * hh
  rcases mul_eq_zero.mp hf with hf | hf
  · exact ⟨h, hh, anchored_known A B C D E F p q r h hh hp (sub_eq_zero.mp hf) Hxy Hxz Hyz⟩
  · have hn : (-h) ^ 2 = 24 := by simpa using hh
    have hA : A = (-h) * p ^ 2 := by linear_combination hf
    exact ⟨-h, hn, anchored_known A B C D E F p q r (-h) hn hp hA Hxy Hxz Hyz⟩

theorem glue (A B C D E F p q r h : ℂ) (hh : h ^ 2 = 24)
    (Hxy : ∀ x y : ℂ, (A * x ^ 2 + 2 * D * x * y + B * y ^ 2) ^ 2 = 24 * (p * x + q * y) ^ 4)
    (Hxz : ∀ x z : ℂ, (A * x ^ 2 + 2 * E * x * z + C * z ^ 2) ^ 2 = 24 * (p * x + r * z) ^ 4)
    (Hyz : ∀ y z : ℂ, (B * y ^ 2 + 2 * F * y * z + C * z ^ 2) ^ 2 = 24 * (q * y + r * z) ^ 4) :
    ∃ k : ℂ, k ^ 2 = 24 ∧ A = k * p ^ 2 ∧ B = k * q ^ 2 ∧ C = k * r ^ 2 ∧
      D = k * p * q ∧ E = k * p * r ∧ F = k * q * r := by
  by_cases hp : p = 0
  · by_cases hq : q = 0
    · by_cases hr : r = 0
      · have hA : A = 0 := by simpa [hp] using Hxy 1 0
        have hB : B = 0 := by simpa [hq] using Hxy 0 1
        have hC : C = 0 := by simpa [hr] using Hxz 0 1
        have hD := binary_mixed A (2 * D) B p q h hh (by simp [hA, hp]) Hxy
        have hE := binary_mixed A (2 * E) C p r h hh (by simp [hA, hp]) Hxz
        have hF := binary_mixed B (2 * F) C q r h hh (by simp [hB, hq]) Hyz
        refine ⟨h, hh, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [hp] using hA
        · simpa [hq] using hB
        · simpa [hr] using hC
        · linear_combination (1 / 2 : ℂ) * hD
        · linear_combination (1 / 2 : ℂ) * hE
        · linear_combination (1 / 2 : ℂ) * hF
      · have Hzy : ∀ z y : ℂ, (C * z ^ 2 + 2 * F * z * y + B * y ^ 2) ^ 2 = 24 * (r * z + q * y) ^ 4 := by
          intro z y
          convert Hyz y z using 1 <;> ring
        have Hzx : ∀ z x : ℂ, (C * z ^ 2 + 2 * E * z * x + A * x ^ 2) ^ 2 = 24 * (r * z + p * x) ^ 4 := by
          intro z x
          convert Hxz x z using 1 <;> ring
        have Hyx : ∀ y x : ℂ, (B * y ^ 2 + 2 * D * y * x + A * x ^ 2) ^ 2 = 24 * (q * y + p * x) ^ 4 := by
          intro y x
          convert Hxy x y using 1 <;> ring
        obtain ⟨k, hk, hC, hB, hA, hF, hE, hD⟩ := anchored_glue C B A F E D r q p h hh hr Hzy Hzx Hyx
        refine ⟨k, hk, hA, hB, hC, ?_, ?_, ?_⟩
        · linear_combination hD
        · linear_combination hE
        · linear_combination hF
    · have Hyx : ∀ y x : ℂ, (B * y ^ 2 + 2 * D * y * x + A * x ^ 2) ^ 2 = 24 * (q * y + p * x) ^ 4 := by
        intro y x
        convert Hxy x y using 1 <;> ring
      obtain ⟨k, hk, hB, hA, hC, hD, hF, hE⟩ := anchored_glue B A C D F E q p r h hh hq Hyx Hyz Hxz
      refine ⟨k, hk, hA, hB, hC, ?_, hE, hF⟩
      linear_combination hD
  · exact anchored_glue A B C D E F p q r h hh hp Hxy Hxz Hyz

end PEqualNP.Outside.L_gct_231_aux.AllZeroSignGluing

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
namespace PEqualNP.Outside.L_gct_231_aux.TopAllZeroBridge
noncomputable def ca (x y : ℂ) : ℂ := x+y
noncomputable def cm (x y : ℂ) : ℂ := x*y
noncomputable def cp (x : ℂ) (n : ℕ) : ℂ := x^n
noncomputable def cz (z : ℤ) : ℂ := z

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


noncomputable def model (a b c l m n h x y z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![(0 : ℂ), cm (cm ((cz (1))) x) h, cm (cm ((cz (1))) y) h, cm (cm ((cz (1))) z) h], ![cm (cm ((cz (1))) x) h, ca (cm (ca (cm (cm ((cz (-2))) x) a) (ca (cm (cm ((cz (-2))) x) b) (ca (cm (cm ((cz (-2))) x) c) (cm ((cz (16))) x)))) a) (ca (cm (cm ((cz (2))) x) l) (ca (cm (cm ((cz (2))) x) m) (cm (cm ((cz (-2))) x) h))), ca (cm (cm (cm ((cz (1))) x) c) a) (ca (cm (cm (cm ((cz (1))) y) c) b) (ca (cm (cm ((cz (1))) z) (cp c 2)) (ca (cm (cm ((cz (-1))) x) m) (cm (cm ((cz (-1))) y) n)))), ca (cm (cm (cm ((cz (1))) x) b) a) (ca (cm (ca (cm (cm ((cz (1))) y) b) (cm (cm ((cz (1))) z) c)) b) (ca (cm (cm ((cz (-1))) x) l) (cm (cm ((cz (1))) z) n)))], ![cm (cm ((cz (1))) y) h, ca (cm (cm (cm ((cz (1))) x) c) a) (ca (cm (cm (cm ((cz (1))) y) c) b) (ca (cm (cm ((cz (1))) z) (cp c 2)) (ca (cm (cm ((cz (-1))) x) m) (cm (cm ((cz (-1))) y) n)))), ca (cm (cm (cm ((cz (-2))) y) b) a) (ca (cm (ca (cm (cm ((cz (-2))) y) b) (ca (cm (cm ((cz (-2))) y) c) (cm ((cz (16))) y))) b) (ca (cm (cm ((cz (-2))) y) l) (ca (cm (cm ((cz (2))) y) n) (cm (cm ((cz (-2))) y) h)))), ca (cm (ca (cm (cm ((cz (1))) x) a) (ca (cm (cm ((cz (1))) y) b) (cm (cm ((cz (1))) z) c))) a) (ca (cm (cm ((cz (1))) y) l) (cm (cm ((cz (1))) z) m))], ![cm (cm ((cz (1))) z) h, ca (cm (cm (cm ((cz (1))) x) b) a) (ca (cm (ca (cm (cm ((cz (1))) y) b) (cm (cm ((cz (1))) z) c)) b) (ca (cm (cm ((cz (-1))) x) l) (cm (cm ((cz (1))) z) n))), ca (cm (ca (cm (cm ((cz (1))) x) a) (ca (cm (cm ((cz (1))) y) b) (cm (cm ((cz (1))) z) c))) a) (ca (cm (cm ((cz (1))) y) l) (cm (cm ((cz (1))) z) m)), ca (cm (cm (cm ((cz (-2))) z) c) a) (ca (cm (cm (cm ((cz (-2))) z) c) b) (ca (cm (ca (cm (cm ((cz (-2))) z) c) (cm ((cz (16))) z)) c) (ca (cm (cm ((cz (-2))) z) m) (ca (cm (cm ((cz (-2))) z) n) (cm (cm ((cz (-2))) z) h)))))]]


end PEqualNP.Outside.L_gct_231_aux.TopAllZeroBridge

namespace PEqualNP.Outside.L_gct_231_aux.AllZeroGeneral

open TopAllZeroBridge

noncomputable def raw (x y z d0 d1 d2 B0 B1 B2 : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0,x,y,z],![x,d0,B2,B1],![y,B2,d1,B0],![z,B1,B0,d2]]

set_option maxHeartbeats 0 in
lemma raw_polars (x y z d0 d1 d2 B0 B1 B2 ell : ℂ)
    (HP : ∀ w : ℂ, Matrix.permanent (Matrix.of fun i j =>
      (1:ℂ)+w*raw x y z d0 d1 d2 B0 B1 B2 i j)=24*(1+w*ell)^4) :
    2*(x+y+z)+d0+d1+d2+2*(B0+B1+B2)=16*ell ∧
      Matrix.permanent (raw x y z d0 d1 d2 B0 B1 B2)=24*ell^4 := by
  have h1 := HP 1
  have hn1 := HP (-1)
  have h2 := HP 2
  have hn2 := HP (-2)
  simp [perm4,raw,Matrix.of_apply] at h1 hn1 h2 hn2
  constructor
  · linear_combination (1/9:ℂ)*(h1-hn1)-(1/72:ℂ)*(h2-hn2)
  · rw [perm4]
    simp [raw]
    linear_combination (1/24:ℂ)*(h2+hn2-4*h1-4*hn1)

lemma raw_xy (x y d0 d1 B0 B1 B2 : ℂ) :
    Matrix.permanent (raw x y 0 d0 d1 0 B0 B1 B2)=(x*B0+y*B1)^2 := by
  rw [perm4]
  simp [raw]
  ring

lemma raw_xz (x z d0 d2 B0 B1 B2 : ℂ) :
    Matrix.permanent (raw x 0 z d0 0 d2 B0 B1 B2)=(x*B0+z*B2)^2 := by
  rw [perm4]
  simp [raw]
  ring

lemma raw_yz (y z d1 d2 B0 B1 B2 : ℂ) :
    Matrix.permanent (raw 0 y z 0 d1 d2 B0 B1 B2)=(y*B1+z*B2)^2 := by
  rw [perm4]
  simp [raw]
  ring

noncomputable def pencil
    (c0 c1 c2 U00 U01 U02 U10 U11 U12 U20 U21 U22 x y z : ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  raw x y z (c0*x) (c1*y) (c2*z)
    (U00*x+U01*y+U02*z) (U10*x+U11*y+U12*z) (U20*x+U21*y+U22*z)

set_option maxHeartbeats 0 in
lemma reconstruct
    (p q r c0 c1 c2 U00 U01 U02 U10 U11 U12 U20 U21 U22 h0 : ℂ)
    (hh0 : h0^2=24)
    (HP : ∀ x y z w : ℂ, Matrix.permanent (Matrix.of fun i j =>
      (1:ℂ)+w*pencil c0 c1 c2 U00 U01 U02 U10 U11 U12 U20 U21 U22 x y z i j)=
        24*(1+w*(p*x+q*y+r*z))^4) :
    ∃ h l m n : ℂ, h^2=24 ∧
      (∀ x y z : ℂ, Matrix.of (fun i j =>
        h*pencil c0 c1 c2 U00 U01 U02 U10 U11 U12 U20 U21 U22 x y z i j)=
          model (h*p) (h*q) (h*r) l m n h x y z) ∧
      (∀ x y z w : ℂ, Matrix.permanent (Matrix.of fun i j =>
        h+w*model (h*p) (h*q) (h*r) l m n h x y z i j)=
          24*(h+w*((h*p)*x+(h*q)*y+(h*r)*z))^4) := by
  have hpol (x y z : ℂ) := raw_polars x y z (c0*x) (c1*y) (c2*z)
    (U00*x+U01*y+U02*z) (U10*x+U11*y+U12*z) (U20*x+U21*y+U22*z)
    (p*x+q*y+r*z) (HP x y z)
  have Hxy (x y : ℂ) :
      (U00*x^2+2*((U01+U10)/2)*x*y+U11*y^2)^2=24*(p*x+q*y)^4 := by
    have he := (hpol x y 0).2
    simp only [mul_zero,add_zero,raw_xy] at he
    convert he using 1 <;> ring
  have Hxz (x z : ℂ) :
      (U00*x^2+2*((U02+U20)/2)*x*z+U22*z^2)^2=24*(p*x+r*z)^4 := by
    have he := (hpol x 0 z).2
    simp only [mul_zero,add_zero,zero_add,raw_xz] at he
    convert he using 1 <;> ring
  have Hyz (y z : ℂ) :
      (U11*y^2+2*((U12+U21)/2)*y*z+U22*z^2)^2=24*(q*y+r*z)^4 := by
    have he := (hpol 0 y z).2
    simp only [mul_zero,add_zero,zero_add,raw_yz] at he
    convert he using 1 <;> ring
  obtain ⟨h,hh,h00,h11,h22,h01,h02,h12⟩ :=
    AllZeroSignGluing.glue U00 U11 U22 ((U01+U10)/2) ((U02+U20)/2)
      ((U12+U21)/2) p q r h0 hh0 Hxy Hxz Hyz
  have hQ (x y z : ℂ) :
      x*((h*U00)*x+(h*U01)*y+(h*U02)*z)+
      y*((h*U10)*x+(h*U11)*y+(h*U12)*z)+
      z*((h*U20)*x+(h*U21)*y+(h*U22)*z)=((h*p)*x+(h*q)*y+(h*r)*z)^2 := by
    linear_combination h*x^2*h00+h*y^2*h11+h*z^2*h22+
      2*h*x*y*h01+2*h*x*z*h02+2*h*y*z*h12
  have hL (x y z : ℂ) :
      2*h*(x+y+z)+(h*c0)*x+(h*c1)*y+(h*c2)*z+
        2*(((h*U00)*x+(h*U01)*y+(h*U02)*z)+
          ((h*U10)*x+(h*U11)*y+(h*U12)*z)+
          ((h*U20)*x+(h*U21)*y+(h*U22)*z))=
        16*((h*p)*x+(h*q)*y+(h*r)*z) := by
    have he := (hpol x y z).1
    linear_combination h*he
  obtain ⟨l,m,n,k00,k11,k22,k01,k10,k02,k20,k12,k21,kd0,kd1,kd2⟩ :=
    AllZeroSkewReconstruction.skew_reconstruction h (h*p) (h*q) (h*r)
      (h*c0) (h*c1) (h*c2) (h*U00) (h*U01) (h*U02)
      (h*U10) (h*U11) (h*U12) (h*U20) (h*U21) (h*U22) hQ hL
  have hmatrix (x y z : ℂ) : Matrix.of (fun i j =>
      h*pencil c0 c1 c2 U00 U01 U02 U10 U11 U12 U20 U21 U22 x y z i j)=
        model (h*p) (h*q) (h*r) l m n h x y z := by
    have hB0 : h*(U00*x+U01*y+U02*z)=
        (h*p)*((h*p)*x+(h*q)*y+(h*r)*z)+l*y+m*z := by
      linear_combination x*k00+y*k01+z*k02
    have hB1 : h*(U10*x+U11*y+U12*z)=
        (h*q)*((h*p)*x+(h*q)*y+(h*r)*z)-l*x+n*z := by
      linear_combination x*k10+y*k11+z*k12
    have hB2 : h*(U20*x+U21*y+U22*z)=
        (h*r)*((h*p)*x+(h*q)*y+(h*r)*z)-m*x-n*y := by
      linear_combination x*k20+y*k21+z*k22
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pencil,raw,model,ca,cm,cp,cz]
    all_goals first
      | (solve | ring)
      | (solve | linear_combination x*kd0)
      | (solve | linear_combination y*kd1)
      | (solve | linear_combination z*kd2)
      | (solve | linear_combination hB0)
      | (solve | linear_combination hB1)
      | (solve | linear_combination hB2)
  refine ⟨h,l,m,n,hh,hmatrix,?_⟩
  intro x y z w
  have heq : Matrix.of (fun i j => h+w*model (h*p) (h*q) (h*r) l m n h x y z i j)=
      h • Matrix.of (fun i j => (1:ℂ)+
        w*pencil c0 c1 c2 U00 U01 U02 U10 U11 U12 U20 U21 U22 x y z i j) := by
    ext i j
    have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i j) (hmatrix x y z)
    simp only [Matrix.of_apply] at he
    simp only [Matrix.of_apply,Matrix.smul_apply,smul_eq_mul]
    rw [←he]
    ring
  rw [heq,Matrix.permanent_smul,HP]
  norm_num only [Fintype.card_fin]
  ring

end PEqualNP.Outside.L_gct_231_aux.AllZeroGeneral
