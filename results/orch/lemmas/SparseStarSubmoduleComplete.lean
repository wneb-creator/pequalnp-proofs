import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.GroupTheory.Perm.Fin


namespace PEqualNP.Outside.L_gct_231.Projective

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

lemma collinear_nonzero_coefficients (A B D : V)
    (hD : D ∈ Submodule.span ℂ ({A,B} : Set V))
    (hDA : D ∉ Submodule.span ℂ ({A} : Set V))
    (hDB : D ∉ Submodule.span ℂ ({B} : Set V)) :
    ∃ a b : ℂ, a≠0 ∧ b≠0 ∧ D=a • A+b • B := by
  obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hD
  refine ⟨a,b,?_,?_,he.symm⟩
  · intro ha
    apply hDB
    apply Submodule.mem_span_singleton.mpr
    exact ⟨b,by simpa only [ha,zero_smul,zero_add] using he⟩
  · intro hb
    apply hDA
    apply Submodule.mem_span_singleton.mpr
    exact ⟨a,by simpa only [hb,zero_smul,add_zero] using he⟩

lemma frame_nonzero_coefficients [FiniteDimensional ℂ V]
    (h3 : Module.finrank ℂ V=3) (A B C D : V)
    (hABC : LinearIndependent ℂ ![A,B,C])
    (hDBC : LinearIndependent ℂ ![D,B,C])
    (hADC : LinearIndependent ℂ ![A,D,C])
    (hABD : LinearIndependent ℂ ![A,B,D]) :
    ∃ a b c : ℂ, a≠0 ∧ b≠0 ∧ c≠0 ∧ D=a • A+b • B+c • C := by
  classical
  let bas := basisOfLinearIndependentOfCardEqFinrank hABC (by simpa using h3.symm)
  have hbas (i : Fin 3) : bas i=(![A,B,C] : Fin 3 → V) i := by
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hABC _) i
  have hre : (bas.repr D 0) • A+(bas.repr D 1) • B+(bas.repr D 2) • C=D := by
    simpa [Fin.sum_univ_three,hbas] using bas.sum_repr D
  let a := bas.repr D 0
  let b := bas.repr D 1
  let c := bas.repr D 2
  have he : D=a • A+b • B+c • C := hre.symm
  refine ⟨a,b,c,?_,?_,?_,he⟩
  · intro ha
    have hz : ∑ i : Fin 3, (![1,-b,-c] : Fin 3 → ℂ) i • (![D,B,C] : Fin 3 → V) i=0 := by
      rw [Fin.sum_univ_three]
      change (1:ℂ) • D+(-b) • B+(-c) • C=0
      simp only [one_smul]
      rw [he,ha,zero_smul,zero_add]
      simp only [neg_smul]
      abel
    have hh := Fintype.linearIndependent_iff.mp hDBC (![1,-b,-c] : Fin 3 → ℂ) hz 0
    norm_num at hh
  · intro hb
    have hz : ∑ i : Fin 3, (![-a,1,-c] : Fin 3 → ℂ) i • (![A,D,C] : Fin 3 → V) i=0 := by
      rw [Fin.sum_univ_three]
      change (-a) • A+(1:ℂ) • D+(-c) • C=0
      simp only [one_smul]
      rw [he,hb,zero_smul,add_zero]
      simp only [neg_smul]
      abel
    have hh := Fintype.linearIndependent_iff.mp hADC (![-a,1,-c] : Fin 3 → ℂ) hz 1
    norm_num at hh
  · intro hc
    have hz : ∑ i : Fin 3, (![-a,-b,1] : Fin 3 → ℂ) i • (![A,B,D] : Fin 3 → V) i=0 := by
      rw [Fin.sum_univ_three]
      change (-a) • A+(-b) • B+(1:ℂ) • D=0
      simp only [one_smul]
      rw [he,hc,zero_smul,add_zero]
      simp only [neg_smul]
      abel
    have hh := Fintype.linearIndependent_iff.mp hABD (![-a,-b,1] : Fin 3 → ℂ) hz 2
    norm_num at hh

lemma finrank_le_two_of_pair_span [FiniteDimensional ℂ V]
    (L : Submodule ℂ V) (A B : V)
    (hspan : ∀ T ∈ L, ∃ a b : ℂ, T=a • A+b • B) :
    Module.finrank ℂ L≤2 := by
  classical
  have hle : L≤Submodule.span ℂ ({A,B} : Set V) := by
    intro T hT
    obtain ⟨a,b,he⟩ := hspan T hT
    exact Submodule.mem_span_pair.mpr ⟨a,b,he.symm⟩
  have hh : Module.finrank ℂ (Submodule.span ℂ ({A,B} : Set V))≤({A,B} : Finset V).card := by
    have hc : (↑({A,B} : Finset V) : Set V)=({A,B} : Set V) := by ext x; simp
    have hx := finrank_span_finset_le_card (R := ℂ) ({A,B} : Finset V)
    change Module.finrank ℂ (Submodule.span ℂ (↑({A,B} : Finset V) : Set V))≤_ at hx
    rw [hc] at hx
    exact hx
  have hc : ({A,B} : Finset V).card≤2 := by
    by_cases he : A=B <;> simp [he]
  exact (Submodule.finrank_mono hle).trans (hh.trans hc)

lemma no_three_dimensional_pair_span [FiniteDimensional ℂ V]
    (L : Submodule ℂ V) (h3 : Module.finrank ℂ L=3) (A B : V)
    (hspan : ∀ T ∈ L, ∃ a b : ℂ, T=a • A+b • B) : False := by
  have hh := finrank_le_two_of_pair_span L A B hspan
  rw [h3] at hh
  norm_num at hh

end PEqualNP.Outside.L_gct_231.Projective


namespace PEqualNP.Outside.L_gct_231_aux.SparseStar

theorem equal_scalar_impossible (z : ℂ) (h4 : z ^ 4 = 6)
    (h2 : z ^ 2 + z - 4 = 0) : False := by
  have hl : -9 * z + 14 = 0 := by
    linear_combination h4 - (z ^ 2 - z + 5) * h2
  have hh : (2 : ℂ) = 0 := by
    linear_combination -81 * h2 - (9 * z + 23) * hl
  norm_num at hh

theorem twisted_scalar_impossible (m : ℂ) (h4 : m ^ 4 = 96)
    (h2 : m ^ 2 - 10 * m - 16 = 0) : False := by
  have hl : 3 * m + 4 = 0 := by
    linear_combination (1 / 440 : ℂ) * (h4 - (m ^ 2 + 10 * m + 116) * h2)
  have hh : (8 : ℂ) = 0 := by
    linear_combination -9 * h2 + (3 * m - 34) * hl
  norm_num at hh

theorem sparse_scalar_obstruction (p c a d k : ℂ)
    (hk : k ^ 2 = 2) (hH : (p * c) ^ 2 = 6)
    (hS : a + d = 16 - 4 * (p + c))
    (hD : k * (d - a) = a + d - 4 * k * (c - p))
    (hN : (c - p) * (k * (p + c) - (c - p)) = 0)
    (hE : a * c ^ 2 + d * p ^ 2 + 2 * (p * c) * (p + c - 2 * (p * c)) = 0) :
    False := by
  rcases mul_eq_zero.mp hN with hN | hN
  · have hcp : c = p := sub_eq_zero.mp hN
    subst c
    have h4 : p ^ 4 = 6 := by linear_combination hH
    have hp : p ≠ 0 := by
      intro hp
      subst p
      norm_num at h4
    have hq : p ^ 2 * (p ^ 2 + p - 4) = 0 := by
      linear_combination (-1 / 4 : ℂ) * hE + (p ^ 2 / 4) * hS
    exact equal_scalar_impossible p h4 ((mul_eq_zero.mp hq).resolve_left (pow_ne_zero 2 hp))
  · have hN : c - p = k * (p + c) := (sub_eq_zero.mp hN).symm
    let m := p + c
    have hp : p = (1 - k) * m / 2 := by
      dsimp [m]
      linear_combination (-1 / 2 : ℂ) * hN
    have hc : c = (1 + k) * m / 2 := by
      dsimp [m]
      linear_combination (1 / 2 : ℂ) * hN
    have ha : a = 8 - 2 * m - 4 * k + 3 * k * m := by
      dsimp [m]
      linear_combination (-k / 4) * hD + ((d - a) / 4 + (c - p)) * hk +
        (1 / 2 - k / 4) * hS + 2 * hN
    have hd : d = 8 - 2 * m + 4 * k - 3 * k * m := by
      dsimp [m] at ha ⊢
      linear_combination hS - ha
    have h4 : m ^ 4 = 96 := by
      rw [hp, hc] at hH
      linear_combination 16 * hH - (k ^ 2 * m ^ 4) * hk
    have hm : m ≠ 0 := by
      intro hm
      rw [hm] at h4
      norm_num at h4
    have hq : m ^ 2 * (m ^ 2 - 10 * m - 16) = 0 := by
      change a * c ^ 2 + d * p ^ 2 + 2 * (p * c) * (m - 2 * (p * c)) = 0 at hE
      rw [hp, hc, ha, hd] at hE
      linear_combination -4 * hE + (-k ^ 2 * m ^ 4 + 6 * m ^ 3) * hk
    exact twisted_scalar_impossible m h4
      ((mul_eq_zero.mp hq).resolve_left (pow_ne_zero 2 hm))

def pairedPermanent (b p c a r d : ℂ) : ℂ :=
  2 * b ^ 2 * (a * d + r ^ 2) + 4 * b * (a * c ^ 2 + d * p ^ 2 + 2 * p * c * r) +
    4 * p ^ 2 * c ^ 2

def pairedPlane (p c a d k b t : ℂ) : ℂ :=
  pairedPermanent b (p + (1 - p) * b) (c + (1 - c) * b)
    (a + (1 - a) * b + (k - 1) * t) (b + t)
    (d + (1 - d) * b - (1 + k) * t)

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000 in
theorem paired_plane_impossible (p c a d k : ℂ)
    (h : ∀ b t : ℂ, pairedPlane p c a d k b t = 24) : False := by
  have h00 := h 0 0
  have h10 := h 1 0
  have hn10 := h (-1) 0
  have h20 := h 2 0
  have hn20 := h (-2) 0
  have h30 := h 3 0
  have h11 := h 1 1
  have h1n1 := h 1 (-1)
  have hn11 := h (-1) 1
  have hn1n1 := h (-1) (-1)
  have h21 := h 2 1
  have h2n1 := h 2 (-1)
  have hn21 := h (-2) 1
  have hn2n1 := h (-2) (-1)
  have hh1 := h (1 / 2) 1
  have hhn1 := h (1 / 2) (-1)
  simp only [pairedPlane, pairedPermanent] at h00 h10 hn10 h20 hn20 h30 h11 h1n1 hn11 hn1n1 h21 h2n1 hn21 hn2n1 hh1 hhn1
  have hk : k ^ 2 = 2 := by
    linear_combination (-1 / 4 : ℂ) * (h11 + h1n1 - 2 * h10)
  have hH : (p * c) ^ 2 = 6 := by
    linear_combination (1 / 4 : ℂ) * h00
  have hS : a + d = 16 - 4 * (p + c) := by
    linear_combination (-1 / 72 : ℂ) * hn10 + (1 / 9 : ℂ) * h00 -
      (1 / 9 : ℂ) * h20 + (1 / 72 : ℂ) * h30
  have hN : (c - p) * (k * (p + c) - (c - p)) = 0 := by
    linear_combination (1 / 12 : ℂ) * (h11 - h1n1 - hn11 + hn1n1) -
      (1 / 96 : ℂ) * (h21 - h2n1 - hn21 + hn2n1)
  have hD : k * (d - a) = a + d - 4 * k * (c - p) := by
    linear_combination 2 * (hh1 - hhn1) - 2 * hN
  have hE : a * c ^ 2 + d * p ^ 2 + 2 * (p * c) * (p + c - 2 * (p * c)) = 0 := by
    linear_combination (1 / 6 : ℂ) * (h10 - hn10) - (1 / 48 : ℂ) * (h20 - hn20)
  exact sparse_scalar_obstruction p c a d k hk hH hS hD hN hE

def constantBPlane (a d r A D R x y : ℂ) : ℂ :=
  pairedPermanent 1 1 (1 + x) (1 + a * x + A * y)
    (1 + r * x + R * y) (1 + d * x + D * y)

set_option maxHeartbeats 10000000 in
theorem constant_b_varying_c_degenerate (a d r A D R : ℂ)
    (h : ∀ x y : ℂ, constantBPlane a d r A D R x y = 24) :
    A = 0 ∧ R = 0 ∧ D = 0 := by
  have h11 := h 1 1
  have h1n1 := h 1 (-1)
  have hn11 := h (-1) 1
  have hn1n1 := h (-1) (-1)
  have h01 := h 0 1
  have h0n1 := h 0 (-1)
  have h00 := h 0 0
  simp only [constantBPlane, pairedPermanent] at h11 h1n1 hn11 hn1n1 h01 h0n1 h00
  have hA : A = 0 := by
    linear_combination (1 / 16 : ℂ) * (h11 - h1n1 + hn11 - hn1n1 - 2 * h01 + 2 * h0n1)
  have hR2 : R ^ 2 = 0 := by
    linear_combination (1 / 4 : ℂ) * (h01 + h0n1 - 2 * h00) - D * hA
  have hR : R = 0 := eq_zero_of_pow_eq_zero hR2
  have hD : D = 0 := by
    linear_combination (1 / 12 : ℂ) * (h01 - h0n1) - hA - 2 * hR
  exact ⟨hA, hR, hD⟩

def constantBCPlane (a d r A D R x y : ℂ) : ℂ :=
  pairedPermanent 1 1 1 (1 + a * x + A * y)
    (1 + r * x + R * y) (1 + d * x + D * y)

set_option maxHeartbeats 10000000 in
theorem constant_b_c_degenerate (a d r A D R : ℂ)
    (h : ∀ x y : ℂ, constantBCPlane a d r A D R x y = 24) :
    d = -a - 2 * r ∧ D = -A - 2 * R ∧ a * R - A * r = 0 := by
  have h00 := h 0 0
  have h10 := h 1 0
  have hn10 := h (-1) 0
  have h01 := h 0 1
  have h0n1 := h 0 (-1)
  have h11 := h 1 1
  simp only [constantBCPlane, pairedPermanent] at h00 h10 hn10 h01 h0n1 h11
  have hd : d = -a - 2 * r := by
    linear_combination (1 / 12 : ℂ) * (h10 - hn10)
  have hD : D = -A - 2 * R := by
    linear_combination (1 / 12 : ℂ) * (h01 - h0n1)
  have hq : -a ^ 2 - 2 * a * r + r ^ 2 = 0 := by
    linear_combination (1 / 4 : ℂ) * (h10 + hn10 - 2 * h00) - a * hd
  have hQ : -A ^ 2 - 2 * A * R + R ^ 2 = 0 := by
    linear_combination (1 / 4 : ℂ) * (h01 + h0n1 - 2 * h00) - A * hD
  have hb : -2 * a * A - 2 * a * R - 2 * A * r + 2 * r * R = 0 := by
    linear_combination (1 / 2 : ℂ) * (h11 - h10 - h01 + h00) - A * hd - a * hD
  have hm : (a * R - A * r) ^ 2 = 0 := by
    linear_combination ((-2 * a * A - 2 * a * R - 2 * A * r + 2 * r * R) / 8) * hb -
      ((-A ^ 2 - 2 * A * R + R ^ 2) / 2) * hq
  exact ⟨hd, hD, eq_zero_of_pow_eq_zero hm⟩

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

def pairedMatrix (b p c a r d : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![b, b, p, c], ![b, b, p, c], ![p, p, a, r], ![c, c, r, d]]

theorem permanent_pairedMatrix (b p c a r d : ℂ) :
    Matrix.permanent (pairedMatrix b p c a r d) = pairedPermanent b p c a r d := by
  rw [perm4]
  simp [pairedMatrix, pairedPermanent]
  ring

theorem paired_matrix_plane_impossible (p c a d k : ℂ)
    (h : ∀ b t : ℂ, Matrix.permanent
      (pairedMatrix b (p + (1 - p) * b) (c + (1 - c) * b)
        (a + (1 - a) * b + (k - 1) * t) (b + t)
        (d + (1 - d) * b - (1 + k) * t)) = 24) : False := by
  apply paired_plane_impossible p c a d k
  intro b t
  simpa only [permanent_pairedMatrix, pairedPlane] using h b t

lemma square_product_constant (p c P C : ℂ)
    (hp : ∀ t : ℂ, (p+P*t)^2*(c+C*t)^2=6) : P=0 ∧ C=0 := by
  have h0 := hp 0
  have h1 := hp 1
  have hn1 := hp (-1)
  have h2 := hp 2
  have hn2 := hp (-2)
  have hPC2 : (P*C)^2=0 := by
    linear_combination (1/24:ℂ)*(h2-4*h1+6*h0-4*hn1+hn2)
  have hPC : P*C=0 := eq_zero_of_pow_eq_zero hPC2
  have hL2 : (p*C+c*P)^2=0 := by
    linear_combination (1/2:ℂ)*(h1+hn1-2*h0)-(2*p*c+P*C)*hPC
  have hL : p*C+c*P=0 := eq_zero_of_pow_eq_zero hL2
  have hp0 : p≠0 := by intro h; subst p; norm_num at h0
  have hc0 : c≠0 := by intro h; subst c; norm_num at h0
  rcases mul_eq_zero.mp hPC with hP | hC
  · refine ⟨hP,?_⟩
    have h : p*C=0 := by linear_combination hL-c*hP
    exact (mul_eq_zero.mp h).resolve_left hp0
  · refine ⟨?_,hC⟩
    have h : c*P=0 := by linear_combination hL-p*hC
    exact (mul_eq_zero.mp h).resolve_left hc0

def varyingBPlane (p c a r d P C A R D x y : ℂ) : ℂ :=
  pairedPermanent (1+x) (1+p*x+P*y) (1+c*x+C*y)
    (1+a*x+A*y) (1+r*x+R*y) (1+d*x+D*y)

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000 in
lemma varying_b_plane_degenerate (p c a r d P C A R D : ℂ)
    (hp : ∀ x y : ℂ, varyingBPlane p c a r d P C A R D x y=24) :
    P=0 ∧ C=0 ∧ A=0 ∧ R=0 ∧ D=0 := by
  have hprod (t : ℂ) : (1-p+P*t)^2*(1-c+C*t)^2=6 := by
    have ht := hp (-1) t
    simp only [varyingBPlane,pairedPermanent] at ht
    linear_combination (1/4:ℂ)*ht
  obtain ⟨hP,hC⟩ := square_product_constant (1-p) (1-c) P C hprod
  subst P
  subst C
  have h1 := hp 0 1
  have hn1 := hp 0 (-1)
  have h0 := hp 0 0
  simp only [varyingBPlane,pairedPermanent] at h1 hn1 h0
  have hS : A+D+2*R=0 := by linear_combination (1/12:ℂ)*(h1-hn1)
  have hQ : A*D+R^2=0 := by linear_combination (1/4:ℂ)*(h1+hn1-2*h0)
  by_cases hR : R=0
  · subst R
    have hA2 : A^2=0 := by linear_combination A*hS-hQ
    have hA : A=0 := eq_zero_of_pow_eq_zero hA2
    have hD : D=0 := by linear_combination hS-hA
    exact ⟨rfl,rfl,hA,rfl,hD⟩
  · have hD : D= -A-2*R := by linear_combination hS
    have hplane (b t : ℂ) :
        pairedPlane (1-p) (1-c) (1-a+A*(r-1)/R) (1-d+D*(r-1)/R)
          (A/R+1) b t=24 := by
      have he := hp (b-1) (((r-1)*(1-b)+t)/R)
      simp only [pairedPlane,varyingBPlane,zero_mul,add_zero] at he ⊢
      convert he using 1
      congr 1 <;> try ring
      all_goals field_simp [hR]
      all_goals try simp only [hD]
      all_goals ring
    exact False.elim (paired_plane_impossible (1-p) (1-c)
      (1-a+A*(r-1)/R) (1-d+D*(r-1)/R) (A/R+1) hplane)

lemma constant_b_top_product_zero (p c a r d : ℂ)
    (hp : ∀ t : ℂ, pairedPermanent 1 (1+p*t) (1+c*t)
      (1+a*t) (1+r*t) (1+d*t)=24) : p*c=0 := by
  have h0 := hp 0
  have h1 := hp 1
  have hn1 := hp (-1)
  have h2 := hp 2
  have hn2 := hp (-2)
  simp only [pairedPermanent] at h0 h1 hn1 h2 hn2
  have hsq : (p*c)^2=0 := by
    linear_combination (1/96:ℂ)*(h2-4*h1+6*h0-4*hn1+hn2)
  exact eq_zero_of_pow_eq_zero hsq

lemma linear_product_alternative (p P c C : ℂ)
    (h0 : p*c=0) (h1 : P*C=0) (h2 : (p+P)*(c+C)=0) :
    (p=0 ∧ P=0) ∨ (c=0 ∧ C=0) := by
  by_cases hp : p=0
  · by_cases hP : P=0
    · exact Or.inl ⟨hp,hP⟩
    · have hC : C=0 := (mul_eq_zero.mp h1).resolve_left hP
      have hc : c=0 := by
        have ht : P*c=0 := by linear_combination h2-c*hp-p*hC-h1
        exact (mul_eq_zero.mp ht).resolve_left hP
      exact Or.inr ⟨hc,hC⟩
  · have hc : c=0 := (mul_eq_zero.mp h0).resolve_left hp
    have hC : C=0 := by
      have ht : p*C=0 := by linear_combination h2-h0-P*hc-h1
      exact (mul_eq_zero.mp ht).resolve_left hp
    exact Or.inr ⟨hc,hC⟩

def pairedAffine (b p c a r d B P C A R D x y : ℂ) : ℂ :=
  pairedPermanent (1+b*x+B*y) (1+p*x+P*y) (1+c*x+C*y)
    (1+a*x+A*y) (1+r*x+R*y) (1+d*x+D*y)

lemma paired_permanent_swap (b p c a r d : ℂ) :
    pairedPermanent b p c a r d=pairedPermanent b c p d r a := by
  simp only [pairedPermanent]
  ring

set_option maxHeartbeats 10000000 in
lemma varying_b_injective_impossible (b p c a r d B P C A R D : ℂ) (hb : b≠0)
    (hp : ∀ x y : ℂ, pairedAffine b p c a r d B P C A R D x y=24)
    (hi : ∀ x y : ℂ, b*x+B*y=0 → p*x+P*y=0 → c*x+C*y=0 →
      a*x+A*y=0 → r*x+R*y=0 → d*x+D*y=0 → x=0 ∧ y=0) : False := by
  have hn (x y : ℂ) : varyingBPlane (p/b) (c/b) (a/b) (r/b) (d/b)
      (P-p*B/b) (C-c*B/b) (A-a*B/b) (R-r*B/b) (D-d*B/b) x y=24 := by
    have he := hp (x/b-B*y/b) y
    simp only [pairedAffine,varyingBPlane] at he ⊢
    convert he using 1
    congr 1 <;> field_simp [hb] <;> ring
  obtain ⟨hP,hC,hA,hR,hD⟩ := varying_b_plane_degenerate
    (p/b) (c/b) (a/b) (r/b) (d/b)
    (P-p*B/b) (C-c*B/b) (A-a*B/b) (R-r*B/b) (D-d*B/b) hn
  have hz := hi (-B/b) 1
    (by field_simp [hb]; ring)
    (by linear_combination hP)
    (by linear_combination hC)
    (by linear_combination hA)
    (by linear_combination hR)
    (by linear_combination hD)
  norm_num at hz

set_option maxHeartbeats 10000000 in
lemma constant_p_varying_c_impossible (c C a r d A R D : ℂ) (hc : c≠0)
    (hp : ∀ x y : ℂ, pairedPermanent 1 1 (1+c*x+C*y)
      (1+a*x+A*y) (1+r*x+R*y) (1+d*x+D*y)=24)
    (hi : ∀ x y : ℂ, c*x+C*y=0 → a*x+A*y=0 →
      r*x+R*y=0 → d*x+D*y=0 → x=0 ∧ y=0) : False := by
  have hn (x y : ℂ) : constantBPlane (a/c) (d/c) (r/c)
      (A-a*C/c) (D-d*C/c) (R-r*C/c) x y=24 := by
    have he := hp (x/c-C*y/c) y
    simp only [constantBPlane] at he ⊢
    convert he using 1
    congr 1 <;> field_simp [hc] <;> ring
  obtain ⟨hA,hR,hD⟩ := constant_b_varying_c_degenerate
    (a/c) (d/c) (r/c) (A-a*C/c) (D-d*C/c) (R-r*C/c) hn
  have hz := hi (-C/c) 1
    (by field_simp [hc]; ring)
    (by linear_combination hA)
    (by linear_combination hR)
    (by linear_combination hD)
  norm_num at hz

set_option maxHeartbeats 10000000 in
lemma constant_p_injective_impossible (c C a r d A R D : ℂ)
    (hp : ∀ x y : ℂ, pairedPermanent 1 1 (1+c*x+C*y)
      (1+a*x+A*y) (1+r*x+R*y) (1+d*x+D*y)=24)
    (hi : ∀ x y : ℂ, c*x+C*y=0 → a*x+A*y=0 →
      r*x+R*y=0 → d*x+D*y=0 → x=0 ∧ y=0) : False := by
  by_cases hc : c≠0
  · exact constant_p_varying_c_impossible c C a r d A R D hc hp hi
  have hc0 : c=0 := not_ne_iff.mp hc
  by_cases hC : C≠0
  · apply constant_p_varying_c_impossible C c A R D a r d hC
    · intro x y
      simpa only [add_assoc,add_left_comm,add_comm] using hp y x
    · intro x y hcv hav hrv hdv
      have he := hi y x
        (by linear_combination hcv)
        (by linear_combination hav)
        (by linear_combination hrv)
        (by linear_combination hdv)
      exact ⟨he.2,he.1⟩
  have hC0 : C=0 := not_ne_iff.mp hC
  subst c
  subst C
  have hn (x y : ℂ) : constantBCPlane a d r A D R x y=24 := by
    simpa only [constantBCPlane,zero_mul,add_zero] using hp x y
  obtain ⟨hd,hD,hm⟩ := constant_b_c_degenerate a d r A D R hn
  by_cases ha : a≠0
  · have hz := hi (-A) a
      (by ring)
      (by ring)
      (by linear_combination hm)
      (by rw [hd,hD]; linear_combination -2*hm)
    exact ha hz.2
  have ha0 : a=0 := not_ne_iff.mp ha
  by_cases hr : r≠0
  · have hz := hi (-R) r
      (by ring)
      (by linear_combination -hm)
      (by ring)
      (by rw [hd,hD]; linear_combination hm)
    exact hr hz.2
  have hr0 : r=0 := not_ne_iff.mp hr
  have hd0 : d=0 := by rw [hd,ha0,hr0]; ring
  have hz := hi 1 0 (by ring) (by simp [ha0]) (by simp [hr0]) (by simp [hd0])
  norm_num at hz

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000 in
lemma paired_affine_plane_impossible (b p c a r d B P C A R D : ℂ)
    (hp : ∀ x y : ℂ, pairedAffine b p c a r d B P C A R D x y=24)
    (hi : ∀ x y : ℂ, b*x+B*y=0 → p*x+P*y=0 → c*x+C*y=0 →
      a*x+A*y=0 → r*x+R*y=0 → d*x+D*y=0 → x=0 ∧ y=0) : False := by
  by_cases hb : b≠0
  · exact varying_b_injective_impossible b p c a r d B P C A R D hb hp hi
  have hb0 : b=0 := not_ne_iff.mp hb
  by_cases hB : B≠0
  · apply varying_b_injective_impossible B P C A R D b p c a r d hB
    · intro x y
      simpa only [pairedAffine,add_assoc,add_left_comm,add_comm] using hp y x
    · intro x y hbv hpv hcv hav hrv hdv
      have he := hi y x
        (by linear_combination hbv)
        (by linear_combination hpv)
        (by linear_combination hcv)
        (by linear_combination hav)
        (by linear_combination hrv)
        (by linear_combination hdv)
      exact ⟨he.2,he.1⟩
  have hB0 : B=0 := not_ne_iff.mp hB
  subst b
  subst B
  have hpc : p*c=0 := by
    apply constant_b_top_product_zero p c a r d
    intro t
    simpa only [pairedAffine,mul_zero,zero_mul,add_zero] using hp t 0
  have hPC : P*C=0 := by
    apply constant_b_top_product_zero P C A R D
    intro t
    simpa only [pairedAffine,mul_zero,zero_mul,add_zero] using hp 0 t
  have hsum : (p+P)*(c+C)=0 := by
    apply constant_b_top_product_zero (p+P) (c+C) (a+A) (r+R) (d+D)
    intro t
    have he := hp t t
    simp only [pairedAffine,zero_mul,add_zero] at he
    convert he using 1
    congr 1 <;> ring
  rcases linear_product_alternative p P c C hpc hPC hsum with ⟨hp0,hP0⟩ | ⟨hc0,hC0⟩
  · subst p
    subst P
    apply constant_p_injective_impossible c C a r d A R D
    · intro x y
      simpa only [pairedAffine,zero_mul,add_zero] using hp x y
    · intro x y hcv hav hrv hdv
      exact hi x y (by ring) (by ring) hcv hav hrv hdv
  · subst c
    subst C
    apply constant_p_injective_impossible p P d r a D R A
    · intro x y
      rw [paired_permanent_swap]
      simpa only [pairedAffine,zero_mul,add_zero] using hp x y
    · intro x y hpv hdv hrv hav
      exact hi x y (by ring) hpv (by ring) hav hrv hdv

def sparseStar : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0,1,-1,0],![1,0,0,0],![-1,0,0,0],![0,0,0,0]]

def symmetricEntries (a u v w b m c d e f : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![a,u,v,w],![u,b,m,c],![v,m,d,e],![w,c,e,f]]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000 in
lemma sparse_star_entries (a u v w b m c d e f : ℂ)
    (hp : ∀ X Y : ℂ, Matrix.permanent (Matrix.of fun r s => (1:ℂ)+
      X*sparseStar r s+Y*symmetricEntries a u v w b m c d e f r s)=24) :
    b=m ∧ d=m ∧ c=e := by
  have h11 := hp 1 1
  have hn11 := hp (-1) 1
  have h01 := hp 0 1
  have h1n1 := hp 1 (-1)
  have hn1n1 := hp (-1) (-1)
  have h0n1 := hp 0 (-1)
  have h12 := hp 1 2
  have hn12 := hp (-1) 2
  have h1n2 := hp 1 (-2)
  have hn1n2 := hp (-1) (-2)
  simp [perm4,sparseStar,symmetricEntries,Matrix.of_apply] at h11 hn11 h01 h1n1 hn1n1 h0n1 h12 hn12 h1n2 hn1n2
  have hQ : b+d-2*m=0 := by
    linear_combination (1/4:ℂ)*(h11+hn11-2*h01-h1n1-hn1n1+2*h0n1)
  have hK : (b+d-2*m)*f+(c-e)^2=0 := by
    linear_combination (1/4:ℂ)*(h11+hn11-2*h01+h1n1+hn1n1-2*h0n1)
  have hL : b-d+c-e=0 := by
    linear_combination (-1/12:ℂ)*(h11-hn11-h1n1+hn1n1)+
      (1/96:ℂ)*(h12-hn12-h1n2+hn1n2)
  have hce2 : (c-e)^2=0 := by linear_combination hK-f*hQ
  have hce : c=e := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hce2)
  refine ⟨?_,?_,hce⟩
  · linear_combination (1/2:ℂ)*(hQ+hL-hce)
  · linear_combination (1/2:ℂ)*(hQ-hL+hce)

lemma sparse_star_lower_equal (M : Matrix (Fin 4) (Fin 4) ℂ)
    (hs : ∀ r s : Fin 4, M r s=M s r)
    (hp : ∀ X Y : ℂ, Matrix.permanent (Matrix.of fun r s => (1:ℂ)+
      X*sparseStar r s+Y*M r s)=24) :
    M 1 1=M 1 2 ∧ M 2 2=M 1 2 ∧ M 1 3=M 2 3 := by
  have heq : M=symmetricEntries (M 0 0) (M 0 1) (M 0 2) (M 0 3)
      (M 1 1) (M 1 2) (M 1 3) (M 2 2) (M 2 3) (M 3 3) := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [symmetricEntries,hs 1 0,hs 2 0,hs 3 0,hs 2 1,hs 3 1,hs 3 2]
  apply sparse_star_entries (M 0 0) (M 0 1) (M 0 2) (M 0 3)
    (M 1 1) (M 1 2) (M 1 3) (M 2 2) (M 2 3) (M 3 3)
  intro X Y
  have he := hp X Y
  rw [heq] at he
  exact he

noncomputable def sparseGauge (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun r s => M r s-((M 0 1-M 0 2)/2)*sparseStar r s

def starPairedMatrix (b p c a r d : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![a,p,p,r],![p,b,b,c],![p,b,b,c],![r,c,c,d]]

lemma permanent_starPairedMatrix (b p c a r d : ℂ) :
    Matrix.permanent (starPairedMatrix b p c a r d)=pairedPermanent b p c a r d := by
  rw [perm4]
  simp only [starPairedMatrix,pairedPermanent]
  simp
  ring

lemma sparse_gauge_shape (M : Matrix (Fin 4) (Fin 4) ℂ)
    (hs : ∀ r s : Fin 4, M r s=M s r)
    (h11 : M 1 1=M 1 2) (h22 : M 2 2=M 1 2) (h13 : M 1 3=M 2 3) :
    sparseGauge M=starPairedMatrix (M 1 2) ((M 0 1+M 0 2)/2) (M 2 3)
      (M 0 0) (M 0 3) (M 3 3) := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [sparseGauge,sparseStar,starPairedMatrix,Matrix.of_apply,h11,h22,h13,
      hs 1 0,hs 2 0,hs 3 0,hs 2 1,hs 3 1,hs 3 2] <;> ring

lemma star_paired_affine (b p c a r d B P C A R D x y : ℂ) :
    Matrix.of (fun i j => (1:ℂ)+x*starPairedMatrix b p c a r d i j+
      y*starPairedMatrix B P C A R D i j)=
    starPairedMatrix (1+b*x+B*y) (1+p*x+P*y) (1+c*x+C*y)
      (1+a*x+A*y) (1+r*x+R*y) (1+d*x+D*y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [starPairedMatrix,Matrix.of_apply] <;> ring

lemma independent_three_coefficients (S A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hi : LinearIndependent ℂ ![S,A,B]) (u v w : ℂ)
    (hrel : ∀ r s, u*S r s+v*A r s+w*B r s=0) : u=0 ∧ v=0 ∧ w=0 := by
  have hz : ∑ n : Fin 3, (![u,v,w] : Fin 3 → ℂ) n •
      (![S,A,B] : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ) n=0 := by
    ext r s
    simpa [Fin.sum_univ_succ,Matrix.smul_apply,add_assoc] using hrel r s
  have h := Fintype.linearIndependent_iff.mp hi (![u,v,w] : Fin 3 → ℂ) hz
  exact ⟨h 0,h 1,h 2⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000 in
lemma sparse_star_three_matrices_impossible (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hsA : ∀ r s : Fin 4, A r s=A s r) (hsB : ∀ r s : Fin 4, B r s=B s r)
    (hi : LinearIndependent ℂ ![sparseStar,A,B])
    (hp : ∀ u x y : ℂ, Matrix.permanent (Matrix.of fun r s =>
      (1:ℂ)+u*sparseStar r s+x*A r s+y*B r s)=24) : False := by
  obtain ⟨hA11,hA22,hA13⟩ := sparse_star_lower_equal A hsA
    (by intro u x; simpa only [zero_mul,add_zero] using hp u x 0)
  obtain ⟨hB11,hB22,hB13⟩ := sparse_star_lower_equal B hsB
    (by intro u y; simpa only [zero_mul,add_zero] using hp u 0 y)
  have hA := sparse_gauge_shape A hsA hA11 hA22 hA13
  have hB := sparse_gauge_shape B hsB hB11 hB22 hB13
  have hpGauge (x y : ℂ) : Matrix.permanent (Matrix.of fun r s =>
      (1:ℂ)+x*sparseGauge A r s+y*sparseGauge B r s)=24 := by
    have he := hp (-x*((A 0 1-A 0 2)/2)-y*((B 0 1-B 0 2)/2)) x y
    convert he using 1
    congr 1
    ext r s
    simp only [sparseGauge,Matrix.of_apply]
    ring
  apply paired_affine_plane_impossible
    (A 1 2) ((A 0 1+A 0 2)/2) (A 2 3) (A 0 0) (A 0 3) (A 3 3)
    (B 1 2) ((B 0 1+B 0 2)/2) (B 2 3) (B 0 0) (B 0 3) (B 3 3)
  · intro x y
    have he := hpGauge x y
    rw [hA,hB,star_paired_affine,permanent_starPairedMatrix] at he
    exact he
  · intro x y hbv hpv hcv hav hrv hdv
    have hGauge : Matrix.of (fun r s => x*sparseGauge A r s+y*sparseGauge B r s)=0 := by
      rw [hA,hB]
      ext r s
      fin_cases r <;> fin_cases s <;> simp only [Matrix.of_apply,Pi.zero_apply]
      all_goals simp [starPairedMatrix]
      all_goals first
        | linear_combination hbv
        | linear_combination hpv
        | linear_combination hcv
        | linear_combination hav
        | linear_combination hrv
        | linear_combination hdv
    have hrel (r s : Fin 4) :
        (-x*((A 0 1-A 0 2)/2)-y*((B 0 1-B 0 2)/2))*sparseStar r s+
          x*A r s+y*B r s=0 := by
      have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M r s) hGauge
      simp only [sparseGauge,Matrix.of_apply,Matrix.zero_apply] at he
      linear_combination he
    have hz := independent_three_coefficients sparseStar A B hi
      (-x*((A 0 1-A 0 2)/2)-y*((B 0 1-B 0 2)/2)) x y hrel
    exact ⟨hz.2.1,hz.2.2⟩

lemma exists_independent_extension_of_three
    (L : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ)) (hL : Module.finrank ℂ L=3)
    (S : Matrix (Fin 4) (Fin 4) ℂ) (hS : S∈L) (hSn : S≠0) :
    ∃ A∈L, ∃ B∈L, LinearIndependent ℂ ![S,A,B] := by
  classical
  have hAex : ∃ A∈L, A∉Submodule.span ℂ ({S} : Set (Matrix (Fin 4) (Fin 4) ℂ)) := by
    by_contra hn
    push_neg at hn
    apply PEqualNP.Outside.L_gct_231.Projective.no_three_dimensional_pair_span L hL S S
    intro T hT
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hn T hT)
    exact ⟨c,0,by simpa only [zero_smul,add_zero] using hc.symm⟩
  obtain ⟨A,hA,hAn⟩ := hAex
  have hBex : ∃ B∈L, B∉Submodule.span ℂ ({S,A} : Set (Matrix (Fin 4) (Fin 4) ℂ)) := by
    by_contra hn
    push_neg at hn
    apply PEqualNP.Outside.L_gct_231.Projective.no_three_dimensional_pair_span L hL S A
    intro T hT
    obtain ⟨c,d,hcd⟩ := Submodule.mem_span_pair.mp (hn T hT)
    exact ⟨c,d,hcd.symm⟩
  obtain ⟨B,hB,hBn⟩ := hBex
  have hSA : LinearIndependent ℂ ![S,A] := by
    apply (LinearIndependent.pair_iff' hSn).mpr
    intro c hc
    exact hAn (Submodule.mem_span_singleton.mpr ⟨c,hc⟩)
  have hBn' : B∉Submodule.span ℂ (Set.range (![S,A] : Fin 2 → Matrix (Fin 4) (Fin 4) ℂ)) := by
    intro he
    apply hBn
    apply Submodule.span_mono ?_ he
    rintro T ⟨i,rfl⟩
    fin_cases i <;> simp
  have hi := hSA.finSnoc hBn'
  have heq : Fin.snoc (![S,A] : Fin 2 → Matrix (Fin 4) (Fin 4) ℂ) B=![S,A,B] := by
    funext i
    fin_cases i <;> rfl
  rw [heq] at hi
  exact ⟨A,hA,B,hB,hi⟩

lemma sparse_star_submodule_impossible
    (L : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ)) (hL : Module.finrank ℂ L=3)
    (hs : ∀ T∈L, ∀ r s : Fin 4, T r s=T s r)
    (hp : ∀ T∈L, Matrix.permanent (Matrix.of fun r s => (1:ℂ)+T r s)=24)
    (hstar : sparseStar∈L) : False := by
  have hSn : sparseStar≠0 := by
    intro he
    have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 1) he
    norm_num [sparseStar] at h01
  obtain ⟨A,hA,B,hB,hi⟩ := exists_independent_extension_of_three L hL sparseStar hstar hSn
  apply sparse_star_three_matrices_impossible A B (hs A hA) (hs B hB) hi
  intro u x y
  have hT : u • sparseStar+x • A+y • B∈L :=
    L.add_mem (L.add_mem (L.smul_mem u hstar) (L.smul_mem x hA)) (L.smul_mem y hB)
  have he := hp (u • sparseStar+x • A+y • B) hT
  simpa only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,add_assoc] using he

end PEqualNP.Outside.L_gct_231_aux.SparseStar
