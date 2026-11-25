import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Basic.Complex.Basic
import PEqualNP.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

namespace PEqualNP.Outside.L_gct_231

def threeParameterMap (A B C : Fin 4 × Fin 4 → ℂ) :
    (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun v := v 0 • A + v 1 • B + v 2 • C
  map_add' v w := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]

lemma range_finrank_three
    (f : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ))
    (hf : Function.Injective f) :
    Module.finrank ℂ (LinearMap.range f) = 3 := by
  rw [LinearMap.finrank_range_of_inj hf]
  simp

lemma range_coordinates
    (f : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ))
    (t : Fin 4 × Fin 4 → ℂ) :
    t ∈ LinearMap.range f ↔ ∃ v : Fin 3 → ℂ, f v = t := by
  rfl

lemma injective_of_coordinate_recovery
    (f : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ))
    (p : Fin 3 → Fin 4 × Fin 4)
    (hp : ∀ v i, f v (p i) = v i) :
    Function.Injective f := by
  intro v w h
  funext i
  simpa only [hp] using congrArg (fun t => t (p i)) h

lemma range_level_space
    (f : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ))
    (hf : Function.Injective f)
    (hs : ∀ v i j, f v (i, j) = f v (j, i))
    (hp : ∀ v, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + f v (i, j)) = 24) :
    ∃ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ),
      Module.finrank ℂ L = 3 ∧
      (∀ t ∈ L, ∀ i j : Fin 4, t (i, j) = t (j, i)) ∧
      ∀ t ∈ L, Matrix.permanent
        (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + t (i, j)) = 24 := by
  refine ⟨LinearMap.range f, range_finrank_three f hf, ?_, ?_⟩
  · rintro t ⟨v, rfl⟩ i j
    exact hs v i j
  · rintro t ⟨v, rfl⟩
    exact hp v

lemma permanent_four {R : Type*} [CommSemiring R] (M : Matrix (Fin 4) (Fin 4) R) :
    Matrix.permanent M =
      M 0 0 * M 1 1 * M 2 2 * M 3 3 +
      M 0 0 * M 1 1 * M 3 2 * M 2 3 +
      M 0 0 * M 2 1 * M 1 2 * M 3 3 +
      M 0 0 * M 2 1 * M 3 2 * M 1 3 +
      M 0 0 * M 3 1 * M 1 2 * M 2 3 +
      M 0 0 * M 3 1 * M 2 2 * M 1 3 +
      M 1 0 * M 0 1 * M 2 2 * M 3 3 +
      M 1 0 * M 0 1 * M 3 2 * M 2 3 +
      M 1 0 * M 2 1 * M 0 2 * M 3 3 +
      M 1 0 * M 2 1 * M 3 2 * M 0 3 +
      M 1 0 * M 3 1 * M 0 2 * M 2 3 +
      M 1 0 * M 3 1 * M 2 2 * M 0 3 +
      M 2 0 * M 0 1 * M 1 2 * M 3 3 +
      M 2 0 * M 0 1 * M 3 2 * M 1 3 +
      M 2 0 * M 1 1 * M 0 2 * M 3 3 +
      M 2 0 * M 1 1 * M 3 2 * M 0 3 +
      M 2 0 * M 3 1 * M 0 2 * M 1 3 +
      M 2 0 * M 3 1 * M 1 2 * M 0 3 +
      M 3 0 * M 0 1 * M 1 2 * M 2 3 +
      M 3 0 * M 0 1 * M 2 2 * M 1 3 +
      M 3 0 * M 1 1 * M 0 2 * M 2 3 +
      M 3 0 * M 1 1 * M 2 2 * M 0 3 +
      M 3 0 * M 2 1 * M 0 2 * M 1 3 +
      M 3 0 * M 2 1 * M 1 2 * M 0 3 := by
  classical
  unfold Matrix.permanent
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 4))) =
      permsOfFinset (Finset.univ : Finset (Fin 4)) := by
    ext p
    simp [mem_perms_of_finset_iff]
  rw [hu]
  change ((permsOfList ([0, 1, 2, 3] : List (Fin 4))).map
    (fun p => ∏ i : Fin 4, M (p i) i)).sum = _
  simp [permsOfList, Fin.prod_univ_succ, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  ring


lemma permanent_star {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.permanent (!![1 + d, 1 + a, 1 + b, 1 + c;
                         1 + a, 1, 1, 1;
                         1 + b, 1, 1, 1;
                         1 + c, 1, 1, 1] : Matrix (Fin 4) (Fin 4) R) =
      24 + 6 * d + 12 * (a + b + c) + 2 * (a + b + c) ^ 2 := by
  rw [permanent_four]
  simp
  ring

def starMatrix {R : Type*} [CommRing R] (a b : R) : Fin 4 × Fin 4 → R :=
  fun p => (!![0, a, b, -a-b;
              a, 0, 0, 0;
              b, 0, 0, 0;
              -a-b, 0, 0, 0] : Matrix (Fin 4) (Fin 4) R) p.1 p.2

lemma starMatrix_symmetric {R : Type*} [CommRing R] (a b : R) (i j : Fin 4) :
    starMatrix a b (i, j) = starMatrix a b (j, i) := by
  fin_cases i <;> fin_cases j <;> simp [starMatrix]

lemma starMatrix_permanent {R : Type*} [CommRing R] (a b : R) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1 + starMatrix a b (i, j)) = 24 := by
  rw [permanent_four]
  simp [starMatrix]
  ring

def starMap : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun v := starMatrix (v 0) (v 1)
  map_add' v w := by
    funext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [starMatrix] <;> ring
  map_smul' c v := by
    funext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [starMatrix, smul_eq_mul] <;> ring

lemma starMap_injective : Function.Injective starMap := by
  intro v w h
  funext i
  fin_cases i
  · simpa [starMap, starMatrix] using congrFun h (0, 1)
  · simpa [starMap, starMatrix] using congrFun h (0, 2)

lemma starMap_finrank : Module.finrank ℂ (LinearMap.range starMap) = 2 := by
  rw [LinearMap.finrank_range_of_inj starMap_injective]
  simp

lemma star_two_dimensional :
    ∃ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ),
      Module.finrank ℂ L = 2 ∧
      (∀ t ∈ L, ∀ i j : Fin 4, t (i, j) = t (j, i)) ∧
      ∀ t ∈ L, Matrix.permanent
        (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + t (i, j)) = 24 := by
  refine ⟨LinearMap.range starMap, starMap_finrank, ?_, ?_⟩
  · rintro t ⟨v, rfl⟩ i j
    exact starMatrix_symmetric (v 0) (v 1) i j
  · rintro t ⟨v, rfl⟩
    exact starMatrix_permanent (v 0) (v 1)

def hollowMatrix {R : Type*} [CommRing R] (a b c d e f : R) :
    Matrix (Fin 4) (Fin 4) R :=
  !![0, a, b, c; a, 0, d, e; b, d, 0, f; c, e, f, 0]

def hollowCubic {R : Type*} [CommRing R] (a b c d e f : R) : R :=
  2 * (a ^ 2 * f + a*b*d + a*b*e + a*b*f + a*c*d + a*c*e + a*c*f +
    a*d*f + a*e*f + a*f^2 + b^2*e + b*c*d + b*c*e + b*c*f + b*d*e +
    b*e^2 + b*e*f + c^2*d + c*d^2 + c*d*e + c*d*f + d*e*f)

lemma permanent_hollow_scaled {R : Type*} [CommRing R] (a b c d e f z : R) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1 + z * hollowMatrix a b c d e f i j) =
    24 + 12 * (a+b+c+d+e+f) * z +
      (2 * (a+b+c+d+e+f)^2 + 4 * (a*f+b*e+c*d)) * z^2 +
      hollowCubic a b c d e f * z^3 + (a*f+b*e+c*d)^2 * z^4 := by
  rw [permanent_four]
  simp [hollowMatrix, hollowCubic]
  ring

lemma quartic_first_coefficients (a b c d : ℂ)
    (h : ∀ z : ℂ, a*z + b*z^2 + c*z^3 + d*z^4 = 0) : a = 0 ∧ b = 0 := by
  have h₁ := h 1
  have h₂ := h (-1)
  have h₃ := h 2
  have h₄ := h (-2)
  constructor
  · linear_combination (2 / 3 : ℂ) * h₁ - (2 / 3 : ℂ) * h₂ -
      (1 / 12 : ℂ) * h₃ + (1 / 12 : ℂ) * h₄
  · linear_combination (2 / 3 : ℂ) * h₁ + (2 / 3 : ℂ) * h₂ -
      (1 / 24 : ℂ) * h₃ - (1 / 24 : ℂ) * h₄

lemma hollow_coefficient_constraints (a b c d e f : ℂ)
    (h : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1 + z * hollowMatrix a b c d e f i j) = 24) :
    a+b+c+d+e+f = 0 ∧ a*f+b*e+c*d = 0 := by
  have hpoly : ∀ z : ℂ,
      (12 * (a+b+c+d+e+f))*z +
      (2*(a+b+c+d+e+f)^2 + 4*(a*f+b*e+c*d))*z^2 +
      hollowCubic a b c d e f*z^3 + (a*f+b*e+c*d)^2*z^4 = 0 := by
    intro z
    have hz := h z
    rw [permanent_hollow_scaled] at hz
    linear_combination hz
  obtain ⟨hs, hr⟩ := quartic_first_coefficients _ _ _ _ hpoly
  have hs' : a+b+c+d+e+f = 0 := by linear_combination hs / 12
  refine ⟨hs', ?_⟩
  rw [hs'] at hr
  linear_combination hr / 4

def hollowPair : LinearMap.BilinForm ℂ (Fin 6 → ℂ) :=
  LinearMap.mk₂ ℂ (fun v w =>
    v 0*w 5 + v 1*w 4 + v 2*w 3 + v 3*w 2 + v 4*w 1 + v 5*w 0)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)

lemma hollowPair_symmetric (v w : Fin 6 → ℂ) : hollowPair v w = hollowPair w v := by
  simp only [hollowPair, LinearMap.mk₂_apply]
  ring

lemma hollowPair_nondegenerate : hollowPair.Nondegenerate := by
  have hleft : ∀ v, (∀ w, hollowPair v w = 0) → v = 0 := by
    intro v h
    have h₀ : v 0 = 0 := by simpa [hollowPair] using h ![0,0,0,0,0,1]
    have h₁ : v 1 = 0 := by simpa [hollowPair] using h ![0,0,0,0,1,0]
    have h₂ : v 2 = 0 := by simpa [hollowPair] using h ![0,0,0,1,0,0]
    have h₃ : v 3 = 0 := by simpa [hollowPair] using h ![0,0,1,0,0,0]
    have h₄ : v 4 = 0 := by simpa [hollowPair] using h ![0,1,0,0,0,0]
    have h₅ : v 5 = 0 := by simpa [hollowPair] using h ![1,0,0,0,0,0]
    funext i
    fin_cases i <;> simp_all
  exact ⟨hleft, fun v h => hleft v fun w => (hollowPair_symmetric v w).trans (h w)⟩

lemma hollow_edges_finrank_le_two (W : Submodule ℂ (Fin 6 → ℂ))
    (hs : ∀ v ∈ W, v 0+v 1+v 2+v 3+v 4+v 5 = 0)
    (hq : ∀ v ∈ W, v 0*v 5+v 1*v 4+v 2*v 3 = 0) :
    Module.finrank ℂ W ≤ 2 := by
  have hle : W ≤ hollowPair.orthogonal W := by
    intro v hv w hw
    have hvq := hq v hv
    have hwq := hq w hw
    have hav := hq (v+w) (W.add_mem hv hw)
    simp only [Pi.add_apply] at hav
    simp only [hollowPair, LinearMap.mk₂_apply]
    linear_combination hav - hvq - hwq
  have hone : (fun _ : Fin 6 => (1 : ℂ)) ∈ hollowPair.orthogonal W := by
    intro v hv
    simpa [hollowPair] using hs v hv
  have hnot : (fun _ : Fin 6 => (1 : ℂ)) ∉ W := by
    intro h
    have hh := hq _ h
    norm_num at hh
  have hlt : W < hollowPair.orthogonal W := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    exact hnot (heq.symm ▸ hone)
  have hd := Submodule.finrank_lt_finrank_of_lt hlt
  rw [LinearMap.BilinForm.finrank_orthogonal hollowPair_nondegenerate] at hd
  have hdim : Module.finrank ℂ (Fin 6 → ℂ) = 6 := by simp
  rw [hdim] at hd
  omega

def hollowEdges : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) where
  toFun t := ![t (0,1), t (0,2), t (0,3), t (1,2), t (1,3), t (2,3)]
  map_add' t u := by ext i; fin_cases i <;> rfl
  map_smul' c t := by ext i; fin_cases i <;> rfl

lemma hollow_reconstruction (t : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j, t (i,j) = t (j,i)) (hz : ∀ i, t (i,i) = 0) (i j : Fin 4) :
    t (i,j) = hollowMatrix (t (0,1)) (t (0,2)) (t (0,3))
      (t (1,2)) (t (1,3)) (t (2,3)) i j := by
  fin_cases i <;> fin_cases j <;> simp [hollowMatrix, hz] <;> exact hs _ _

lemma hollow_member_constraints (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hs : ∀ t ∈ L, ∀ i j : Fin 4, t (i,j) = t (j,i))
    (hz : ∀ t ∈ L, ∀ i : Fin 4, t (i,i) = 0)
    (hp : ∀ t ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + t (i,j)) = 24)
    (t : Fin 4 × Fin 4 → ℂ) (ht : t ∈ L) :
    t (0,1)+t (0,2)+t (0,3)+t (1,2)+t (1,3)+t (2,3) = 0 ∧
      t (0,1)*t (2,3)+t (0,2)*t (1,3)+t (0,3)*t (1,2) = 0 := by
  apply hollow_coefficient_constraints
  intro z
  have h := hp (z • t) (L.smul_mem z ht)
  convert h using 1
  congr 1
  funext i j
  change 1 + z * hollowMatrix _ _ _ _ _ _ i j = 1 + z * t (i,j)
  rw [hollow_reconstruction t (hs t ht) (hz t ht) i j]

lemma hollow_flat_finrank_le_two (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hs : ∀ t ∈ L, ∀ i j : Fin 4, t (i,j) = t (j,i))
    (hz : ∀ t ∈ L, ∀ i : Fin 4, t (i,i) = 0)
    (hp : ∀ t ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + t (i,j)) = 24) :
    Module.finrank ℂ L ≤ 2 := by
  let f : L →ₗ[ℂ] (Fin 6 → ℂ) := hollowEdges.comp L.subtype
  have hf : Function.Injective f := by
    intro t u he
    have h₀ : t.val (0,1) = u.val (0,1) := congrFun he 0
    have h₁ : t.val (0,2) = u.val (0,2) := congrFun he 1
    have h₂ : t.val (0,3) = u.val (0,3) := congrFun he 2
    have h₃ : t.val (1,2) = u.val (1,2) := congrFun he 3
    have h₄ : t.val (1,3) = u.val (1,3) := congrFun he 4
    have h₅ : t.val (2,3) = u.val (2,3) := congrFun he 5
    apply Subtype.ext
    funext p
    rcases p with ⟨i,j⟩
    rw [hollow_reconstruction t.val (hs t.val t.property) (hz t.val t.property),
      hollow_reconstruction u.val (hs u.val u.property) (hz u.val u.property),
      h₀, h₁, h₂, h₃, h₄, h₅]
  have hsum : ∀ v ∈ LinearMap.range f, v 0+v 1+v 2+v 3+v 4+v 5 = 0 := by
    rintro v ⟨t,rfl⟩
    exact (hollow_member_constraints L hs hz hp t.val t.property).1
  have hquad : ∀ v ∈ LinearMap.range f, v 0*v 5+v 1*v 4+v 2*v 3 = 0 := by
    rintro v ⟨t,rfl⟩
    exact (hollow_member_constraints L hs hz hp t.val t.property).2
  have hdim := hollow_edges_finrank_le_two (LinearMap.range f) hsum hquad
  rwa [LinearMap.finrank_range_of_inj hf] at hdim

def starLinear (V : Fin 4 × Fin 4 → ℂ) (a b : ℂ) : ℂ :=
  a^2 * (V (1,1) - 2 * V (1,3) + V (3,3)) +
  2*a*b * (V (1,2) - V (1,3) - V (2,3) + V (3,3)) -
  4*a * (V (1,1) + V (1,2) - V (2,3) - V (3,3)) +
  b^2 * (V (2,2) - 2 * V (2,3) + V (3,3)) -
  4*b * (V (1,2) - V (1,3) + V (2,2) - V (3,3)) +
  6 * (V (0,0) + 2 * V (0,1) + 2 * V (0,2) + 2 * V (0,3) +
    V (1,1) + 2 * V (1,2) + 2 * V (1,3) + V (2,2) + 2 * V (2,3) + V (3,3))

set_option maxHeartbeats 2000000 in
lemma starLinear_zero (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ a b z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + starMatrix a b (i,j) + z * V (i,j)) = 24)
    (a b : ℂ) : starLinear V a b = 0 := by
  have hs10 := hs 1 0
  have hs20 := hs 2 0
  have hs30 := hs 3 0
  have hs21 := hs 2 1
  have hs31 := hs 3 1
  have hs32 := hs 3 2
  have h₁ := hp a b 1
  have h₂ := hp a b (-1)
  have h₃ := hp a b 2
  have h₄ := hp a b (-2)
  rw [permanent_four] at h₁ h₂ h₃ h₄
  simp [starMatrix, hs10, hs20, hs30, hs21, hs31, hs32] at h₁ h₂ h₃ h₄
  unfold starLinear
  linear_combination (2 / 3 : ℂ) * h₁ - (2 / 3 : ℂ) * h₂ -
    (1 / 12 : ℂ) * h₃ + (1 / 12 : ℂ) * h₄

set_option maxHeartbeats 4000000 in
lemma star_two_plane_maximal (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ a b z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + starMatrix a b (i,j) + z * V (i,j)) = 24) :
    V = starMatrix (V (0,1)) (V (0,2)) := by
  have h₀ := starLinear_zero V hs hp 0 0
  have h₁ := starLinear_zero V hs hp 1 0
  have h₂ := starLinear_zero V hs hp (-1) 0
  have h₃ := starLinear_zero V hs hp 0 1
  have h₄ := starLinear_zero V hs hp 0 (-1)
  have h₅ := starLinear_zero V hs hp 1 1
  simp only [starLinear] at h₀ h₁ h₂ h₃ h₄ h₅
  have h11 : V (1,1) = V (3,3) := by
    linear_combination (-2 / 3 : ℂ) * h₀ + (5 / 12 : ℂ) * h₁ +
      (1 / 4 : ℂ) * h₂ + (1 / 3 : ℂ) * h₃ - (1 / 3 : ℂ) * h₅
  have h12 : V (1,2) = V (3,3) := by
    linear_combination (5 / 6 : ℂ) * h₀ - (3 / 8 : ℂ) * h₁ -
      (1 / 8 : ℂ) * h₂ - (3 / 8 : ℂ) * h₃ - (1 / 8 : ℂ) * h₄ +
      (1 / 6 : ℂ) * h₅
  have h13 : V (1,3) = V (3,3) := by
    linear_combination (1 / 6 : ℂ) * h₀ - (1 / 24 : ℂ) * h₁ -
      (1 / 8 : ℂ) * h₂ + (1 / 6 : ℂ) * h₃ - (1 / 6 : ℂ) * h₅
  have h22 : V (2,2) = V (3,3) := by
    linear_combination (-2 / 3 : ℂ) * h₀ + (1 / 3 : ℂ) * h₁ +
      (5 / 12 : ℂ) * h₃ + (1 / 4 : ℂ) * h₄ - (1 / 3 : ℂ) * h₅
  have h23 : V (2,3) = V (3,3) := by
    linear_combination (1 / 6 : ℂ) * h₀ + (1 / 6 : ℂ) * h₁ -
      (1 / 24 : ℂ) * h₃ - (1 / 8 : ℂ) * h₄ - (1 / 6 : ℂ) * h₅
  have h00 : V (0,0) = -2 * (V (0,1) + V (0,2) + V (0,3)) - 9 * V (3,3) := by
    linear_combination (-5 / 6 : ℂ) * h₀ - (1 / 4 : ℂ) * h₁ +
      (1 / 4 : ℂ) * h₂ - (1 / 4 : ℂ) * h₃ + (1 / 4 : ℂ) * h₄ + h₅
  have hs10 := hs 1 0
  have hs20 := hs 2 0
  have hs30 := hs 3 0
  have hs21 := hs 2 1
  have hs31 := hs 3 1
  have hs32 := hs 3 2
  let s := V (0,1) + V (0,2) + V (0,3)
  let r := V (3,3)
  have hpoly : ∀ z : ℂ,
      2 * (s^2 - 6*s*r - 63*r^2) * z^2 +
      4*r * (s^2 - 6*s*r - 39*r^2) * z^3 +
      2*r^2 * (s-9*r) * (s+3*r) * z^4 = 0 := by
    intro z
    have hz := hp 0 0 z
    rw [permanent_four] at hz
    simp [starMatrix, hs10, hs20, hs30, hs21, hs31, hs32,
      h11, h12, h13, h22, h23, h00] at hz
    dsimp [s, r]
    linear_combination hz
  have hq : 2 * (s^2 - 6*s*r - 63*r^2) = 0 := by
    exact (quartic_first_coefficients 0 _ _ _ (by simpa using hpoly)).2
  have hc : 4*r * (s^2 - 6*s*r - 39*r^2) = 0 := by
    have h₁ := hpoly 1
    have h₂ := hpoly (-1)
    linear_combination (1 / 2 : ℂ) * h₁ - (1 / 2 : ℂ) * h₂
  have hr3 : r^3 = 0 := by
    linear_combination hc / 96 - r * hq / 48
  have hr : r = 0 := eq_zero_of_pow_eq_zero hr3
  have hs2 : s^2 = 0 := by
    rw [hr] at hq
    linear_combination hq / 2
  have hsz : s = 0 := eq_zero_of_pow_eq_zero hs2
  have h33 : V (3,3) = 0 := hr
  have h03 : V (0,3) = -V (0,1) - V (0,2) := by
    dsimp [s] at hsz
    linear_combination hsz
  have h00z : V (0,0) = 0 := by
    change V (0,0) = -2*s - 9*r at h00
    rw [hsz, hr] at h00
    simpa using h00
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [starMatrix, hs10, hs20, hs30, hs21, hs31, hs32,
      h11, h12, h13, h22, h23, h33, h03, h00z]

set_option maxHeartbeats 4000000 in
lemma constant_lower_block_is_star (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hb : V (1,1) = V (3,3) ∧ V (1,2) = V (3,3) ∧
      V (1,3) = V (3,3) ∧ V (2,2) = V (3,3) ∧ V (2,3) = V (3,3))
    (hp : ∀ z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + z * V (i,j)) = 24) :
    V = starMatrix (V (0,1)) (V (0,2)) := by
  rcases hb with ⟨h11,h12,h13,h22,h23⟩
  have hs10 := hs 1 0
  have hs20 := hs 2 0
  have hs30 := hs 3 0
  have hs21 := hs 2 1
  have hs31 := hs 3 1
  have hs32 := hs 3 2
  let s := V (0,1) + V (0,2) + V (0,3)
  let r := V (3,3)
  have h00 : V (0,0) = -2*s - 9*r := by
    have h₁ := hp 1
    have h₂ := hp (-1)
    have h₃ := hp 2
    have h₄ := hp (-2)
    rw [permanent_four] at h₁ h₂ h₃ h₄
    simp [hs10, hs20, hs30, hs21, hs31, hs32,
      h11, h12, h13, h22, h23] at h₁ h₂ h₃ h₄
    dsimp [s,r]
    linear_combination h₁ / 9 - h₂ / 9 - h₃ / 72 + h₄ / 72
  have hpoly : ∀ z : ℂ,
      2 * (s^2 - 6*s*r - 63*r^2) * z^2 +
      4*r * (s^2 - 6*s*r - 39*r^2) * z^3 +
      2*r^2 * (s-9*r) * (s+3*r) * z^4 = 0 := by
    intro z
    have hz := hp z
    rw [permanent_four] at hz
    simp [hs10, hs20, hs30, hs21, hs31, hs32,
      h11, h12, h13, h22, h23, h00] at hz
    dsimp [s, r] at hz ⊢
    linear_combination hz
  have hq : 2 * (s^2 - 6*s*r - 63*r^2) = 0 := by
    exact (quartic_first_coefficients 0 _ _ _ (by simpa using hpoly)).2
  have hc : 4*r * (s^2 - 6*s*r - 39*r^2) = 0 := by
    have h₁ := hpoly 1
    have h₂ := hpoly (-1)
    linear_combination h₁ / 2 - h₂ / 2
  have hr3 : r^3 = 0 := by
    linear_combination hc / 96 - r * hq / 48
  have hr : r = 0 := eq_zero_of_pow_eq_zero hr3
  have hs2 : s^2 = 0 := by
    rw [hr] at hq
    linear_combination hq / 2
  have hsz : s = 0 := eq_zero_of_pow_eq_zero hs2
  have h33 : V (3,3) = 0 := hr
  have h03 : V (0,3) = -V (0,1) - V (0,2) := by
    dsimp [s] at hsz
    linear_combination hsz
  have h00z : V (0,0) = 0 := by
    rw [hsz, hr] at h00
    simpa using h00
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [starMatrix, hs10, hs20, hs30, hs21, hs31, hs32,
      h11, h12, h13, h22, h23, h33, h03, h00z]

def starLineQuad (t e f g h i j : ℂ) : ℂ :=
  h*j+i^2+t^2*(e*j+g^2)+(1+t)^2*(e*h+f^2)+
    2*t*(f*j+g*i)-2*(1+t)*(f*i+g*h)-2*t*(1+t)*(e*i+f*g)

set_option maxHeartbeats 4000000 in
lemma star_line_constraints (t : ℂ) (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ a z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + starMatrix a (t*a) (i,j) +
        z * V (i,j)) = 24) :
    (t+1)*V (1,2)-t*V (1,3)+t*V (2,2)-(t+1)*V (3,3)+
        V (1,1)-V (2,3) = 0 ∧
    t^2*(V (2,2)-2*V (2,3)+V (3,3))+
        2*t*(V (1,2)-V (1,3)-V (2,3)+V (3,3))+
        V (1,1)-2*V (1,3)+V (3,3) = 0 ∧
    starLineQuad t (V (1,1)) (V (1,2)) (V (1,3))
      (V (2,2)) (V (2,3)) (V (3,3)) = 0 := by
  have hs10 := hs 1 0
  have hs20 := hs 2 0
  have hs30 := hs 3 0
  have hs21 := hs 2 1
  have hs31 := hs 3 1
  have hs32 := hs 3 2
  have hl : ∀ a : ℂ, starLinear V a (t*a) = 0 := by
    intro a
    have h₁ := hp a 1
    have h₂ := hp a (-1)
    have h₃ := hp a 2
    have h₄ := hp a (-2)
    rw [permanent_four] at h₁ h₂ h₃ h₄
    simp [starMatrix, hs10, hs20, hs30, hs21, hs31, hs32] at h₁ h₂ h₃ h₄
    unfold starLinear
    linear_combination (2 / 3 : ℂ) * h₁ - (2 / 3 : ℂ) * h₂ -
      (1 / 12 : ℂ) * h₃ + (1 / 12 : ℂ) * h₄
  have hl0 := hl 0
  have hl1 := hl 1
  have hlm := hl (-1)
  simp only [starLinear] at hl0 hl1 hlm
  refine ⟨?_,?_,?_⟩
  · linear_combination -hl1 / 8 + hlm / 8
  · linear_combination hl1 / 2 + hlm / 2 - hl0
  · have h₁ := hp 1 1
    have h₂ := hp (-1) 1
    have h₃ := hp 1 (-1)
    have h₄ := hp (-1) (-1)
    have h₅ := hp 0 1
    have h₆ := hp 0 (-1)
    rw [permanent_four] at h₁ h₂ h₃ h₄ h₅ h₆
    simp [starMatrix, hs10, hs20, hs30, hs21, hs31, hs32] at h₁ h₂ h₃ h₄ h₅ h₆
    unfold starLineQuad
    linear_combination h₁ / 4 + h₂ / 4 + h₃ / 4 + h₄ / 4 - h₅ / 2 - h₆ / 2

def starLineU (t f g h i : ℂ) : ℂ := t*(t+2)*((g-i)-(f-i)+(h-i))
def starLineV (t f h i : ℂ) : ℂ := (f-i)+t*(h-i)
def starLineW (t f h i : ℂ) : ℂ :=
  (t^2-8*t-2)*(f-i)+t*(7*t^2+10*t+10)*(h-i)

set_option maxHeartbeats 4000000 in
lemma star_line_congruence (t e f g h i j : ℂ)
    (ht1 : t+1 ≠ 0) (ht2 : t+2 ≠ 0)
    (h1 : (t+1)*f-t*g+t*h-(t+1)*j+e-i = 0)
    (h2 : t^2*(h-2*i+j)+2*t*(f-g-i+j)+e-2*g+j = 0) :
    (t+2)^2 * starLineQuad t e f g h i j =
      2 * ((starLineU t f g h i)^2 - starLineV t f h i * starLineW t f h i) := by
  have he : e = (-f*t^2-4*f*t-f+g*t^2+3*g*t+2*g-2*h*t^2-h*t+
      2*i*t^2+3*i*t+i)/(t+2) := by
    apply (eq_div_iff ht2).2
    linear_combination (t+1)*h1+h2
  have hj : j = (-f*t+f+g*t+2*g-h*t^2+h*t+2*i*t^2+2*i*t-i)/
      ((t+1)*(t+2)) := by
    apply (eq_div_iff (mul_ne_zero ht1 ht2)).2
    linear_combination h2-h1
  rw [he,hj]
  unfold starLineQuad starLineU starLineV starLineW
  field_simp
  <;> ring

lemma star_line_coordinate_kernel (t e f g h i j : ℂ)
    (ht : t ≠ 0) (ht1 : t+1 ≠ 0) (ht2 : t+2 ≠ 0)
    (h1 : (t+1)*f-t*g+t*h-(t+1)*j+e-i = 0)
    (h2 : t^2*(h-2*i+j)+2*t*(f-g-i+j)+e-2*g+j = 0)
    (hU : starLineU t f g h i = 0)
    (hV : starLineV t f h i = 0)
    (hW : starLineW t f h i = 0) : e=j ∧ f=j ∧ g=j ∧ h=j ∧ i=j := by
  simp only [starLineU, starLineV, starLineW] at hU hV hW
  have hh : 6*t*(t+1)*(t+2)*(h-i) = 0 := by
    linear_combination hW-(t^2-8*t-2)*hV
  have hhi : h = i := by
    have hz : h-i = 0 := (mul_eq_zero.mp hh).resolve_left
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ht) ht1) ht2)
    linear_combination hz
  have hfi : f = i := by rw [hhi] at hV; linear_combination hV
  have hgi : g = i := by
    rw [hhi,hfi] at hU
    have hz : t*(t+2)*(g-i) = 0 := by simpa using hU
    have hz' : g-i = 0 := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero ht ht2)
    linear_combination hz'
  have hji : j = i := by
    have hz : (t+1)*(t+2)*(j-i) = 0 := by
      rw [hfi,hgi,hhi] at h1 h2
      linear_combination h2-h1
    have hz' : j-i = 0 := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero ht1 ht2)
    linear_combination hz'
  have hei : e = i := by rw [hfi,hgi,hhi,hji] at h1; linear_combination h1
  exact ⟨hei.trans hji.symm,hfi.trans hji.symm,hgi.trans hji.symm,
    hhi.trans hji.symm,hji.symm⟩

lemma star_line_cone (t : ℂ) (V : Fin 4 × Fin 4 → ℂ)
    (ht1 : t+1 ≠ 0) (ht2 : t+2 ≠ 0)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ a z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + starMatrix a (t*a) (i,j) +
        z * V (i,j)) = 24) :
    (starLineU t (V (1,2)) (V (1,3)) (V (2,2)) (V (2,3)))^2 =
      starLineV t (V (1,2)) (V (2,2)) (V (2,3)) *
      starLineW t (V (1,2)) (V (2,2)) (V (2,3)) := by
  obtain ⟨h1,h2,hq⟩ := star_line_constraints t V hs hp
  have hc := star_line_congruence t (V (1,1)) (V (1,2)) (V (1,3))
    (V (2,2)) (V (2,3)) (V (3,3)) ht1 ht2 h1 h2
  rw [hq] at hc
  linear_combination -hc / 2

lemma star_line_zero_coordinates (t : ℂ) (V : Fin 4 × Fin 4 → ℂ)
    (ht : t ≠ 0) (ht1 : t+1 ≠ 0) (ht2 : t+2 ≠ 0)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ a z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + starMatrix a (t*a) (i,j) +
        z * V (i,j)) = 24)
    (hU : starLineU t (V (1,2)) (V (1,3)) (V (2,2)) (V (2,3)) = 0)
    (hV : starLineV t (V (1,2)) (V (2,2)) (V (2,3)) = 0)
    (hW : starLineW t (V (1,2)) (V (2,2)) (V (2,3)) = 0) :
    V = starMatrix (V (0,1)) (V (0,2)) := by
  obtain ⟨h1,h2,_⟩ := star_line_constraints t V hs hp
  have hb := star_line_coordinate_kernel t (V (1,1)) (V (1,2)) (V (1,3))
    (V (2,2)) (V (2,3)) (V (3,3)) ht ht1 ht2 h1 h2 hU hV hW
  apply constant_lower_block_is_star V hs hb
  intro z
  have hzstar : starMatrix (0 : ℂ) (t*0) = 0 := by
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [starMatrix]
  simpa only [hzstar, Pi.zero_apply, add_zero] using hp 0 z

def starConePair : LinearMap.BilinForm ℂ (Fin 3 → ℂ) :=
  LinearMap.mk₂ ℂ (fun v w => 2*v 0*w 0-v 1*w 2-v 2*w 1)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)

lemma starConePair_symmetric (v w : Fin 3 → ℂ) :
    starConePair v w = starConePair w v := by
  simp only [starConePair, LinearMap.mk₂_apply]
  ring

lemma starConePair_nondegenerate : starConePair.Nondegenerate := by
  have hleft : ∀ v, (∀ w, starConePair v w = 0) → v = 0 := by
    intro v h
    have h₀ : v 0 = 0 := by
      have hz := h ![1,0,0]
      simp [starConePair] at hz
      exact hz
    have h₁ : v 1 = 0 := by simpa [starConePair] using h ![0,0,1]
    have h₂ : v 2 = 0 := by simpa [starConePair] using h ![0,1,0]
    funext i
    fin_cases i <;> simp_all
  exact ⟨hleft, fun v h => hleft v fun w => (starConePair_symmetric v w).trans (h w)⟩

lemma star_cone_finrank_le_one (W : Submodule ℂ (Fin 3 → ℂ))
    (hq : ∀ v ∈ W, (v 0)^2 = v 1*v 2) : Module.finrank ℂ W ≤ 1 := by
  have hle : W ≤ starConePair.orthogonal W := by
    intro v hv w hw
    have hvq := hq v hv
    have hwq := hq w hw
    have hav := hq (v+w) (W.add_mem hv hw)
    simp only [Pi.add_apply] at hav
    simp only [starConePair, LinearMap.mk₂_apply]
    linear_combination hav - hvq - hwq
  have hd := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal starConePair_nondegenerate] at hd
  have hdim : Module.finrank ℂ (Fin 3 → ℂ) = 3 := by simp
  rw [hdim] at hd
  omega

def starLineCoordinates (t : ℂ) : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun V := ![starLineU t (V (1,2)) (V (1,3)) (V (2,2)) (V (2,3)),
    starLineV t (V (1,2)) (V (2,2)) (V (2,3)),
    starLineW t (V (1,2)) (V (2,2)) (V (2,3))]
  map_add' := by
    intro V W
    ext k
    fin_cases k <;> simp [starLineU,starLineV,starLineW] <;> ring
  map_smul' := by
    intro c V
    ext k
    fin_cases k <;> simp [starLineU,starLineV,starLineW] <;> ring

lemma star_line_closed_family (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (t : ℂ) (hA : starMatrix 1 t ∈ L)
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + V (i,j)) = 24)
    (V : Fin 4 × Fin 4 → ℂ) (hV : V ∈ L) (a z : ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1 + starMatrix a (t*a) (i,j) + z * V (i,j)) = 24 := by
  have heq : (fun p => starMatrix a (t*a) p + z * V p) =
      a • starMatrix 1 t + z • V := by
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [starMatrix] <;> ring
  have hm : (fun p => starMatrix a (t*a) p + z * V p) ∈ L := by
    rw [heq]
    exact L.add_mem (L.smul_mem a hA) (L.smul_mem z hV)
  simpa only [add_assoc] using hp _ hm

lemma star_line_image_finrank_le_one (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (t : ℂ) (ht1 : t+1 ≠ 0) (ht2 : t+2 ≠ 0)
    (hA : starMatrix 1 t ∈ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + V (i,j)) = 24) :
    Module.finrank ℂ (L.map (starLineCoordinates t)) ≤ 1 := by
  apply star_cone_finrank_le_one
  rintro v ⟨V,hV,rfl⟩
  simpa [starLineCoordinates] using star_line_cone t V ht1 ht2 (hs V hV)
    (star_line_closed_family L t hA hp V hV)

lemma star_line_kernel_is_star (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (t : ℂ) (ht : t ≠ 0) (ht1 : t+1 ≠ 0) (ht2 : t+2 ≠ 0)
    (hA : starMatrix 1 t ∈ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + V (i,j)) = 24) :
    L ⊓ LinearMap.ker (starLineCoordinates t) ≤ LinearMap.range starMap := by
  rintro V ⟨hV,hker⟩
  have hh : starLineCoordinates t V = 0 := hker
  have hU := congrFun hh 0
  have hV' := congrFun hh 1
  have hW := congrFun hh 2
  simp [starLineCoordinates] at hU hV' hW
  have hstar := star_line_zero_coordinates t V ht ht1 ht2 (hs V hV)
    (star_line_closed_family L t hA hp V hV) hU hV' hW
  refine ⟨![V (0,1),V (0,2)],?_⟩
  simpa [starMap] using hstar.symm

lemma containing_star_plane_finrank_le_two (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hstar : LinearMap.range starMap ≤ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + V (i,j)) = 24) :
    Module.finrank ℂ L ≤ 2 := by
  have hle : L ≤ LinearMap.range starMap := by
    intro V hV
    have heq : V = starMatrix (V (0,1)) (V (0,2)) := by
      apply star_two_plane_maximal V (hs V hV)
      intro a b z
      have hm : starMatrix a b ∈ L := hstar ⟨![a,b],by simp [starMap]⟩
      have hz := hp _ (L.add_mem hm (L.smul_mem z hV))
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_assoc] using hz
    refine ⟨![V (0,1),V (0,2)],?_⟩
    simpa [starMap] using heq.symm
  have hd := Submodule.finrank_mono hle
  simpa only [starMap_finrank] using hd

lemma finrank_le_two_of_small_image
    (L S : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (F : L →ₗ[ℂ] (Fin 3 → ℂ))
    (hS : Module.finrank ℂ S = 2)
    (hrange : Module.finrank ℂ (LinearMap.range F) ≤ 1)
    (hker : (LinearMap.ker F).map L.subtype ≤ S)
    (hmax : S ≤ L → Module.finrank ℂ L ≤ 2) : Module.finrank ℂ L ≤ 2 := by
  have hkdim : Module.finrank ℂ (LinearMap.ker F) ≤ 2 := by
    have h := Submodule.finrank_mono hker
    simpa only [Submodule.finrank_map_subtype_eq, hS] using h
  by_cases hk : Module.finrank ℂ (LinearMap.ker F) ≤ 1
  · have hn := F.finrank_range_add_finrank_ker
    omega
  · have hk2 : Module.finrank ℂ (LinearMap.ker F) = 2 := by omega
    have heq : (LinearMap.ker F).map L.subtype = S :=
      Submodule.eq_of_le_of_finrank_eq hker (by
        rw [Submodule.finrank_map_subtype_eq, hk2, hS])
    have hsL : S ≤ L := by
      rw [← heq]
      rintro x ⟨y, hy, rfl⟩
      exact y.property
    exact hmax hsL

lemma containing_generic_star_line_finrank_le_two
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (t : ℂ) (ht : t ≠ 0) (ht1 : t+1 ≠ 0) (ht2 : t+2 ≠ 0)
    (hA : starMatrix 1 t ∈ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + V (i,j)) = 24) :
    Module.finrank ℂ L ≤ 2 := by
  apply finrank_le_two_of_small_image L (LinearMap.range starMap)
    ((starLineCoordinates t).domRestrict L) starMap_finrank
  · rw [LinearMap.range_domRestrict]
    exact star_line_image_finrank_le_one L t ht1 ht2 hA hs hp
  · rintro V ⟨v,hv,rfl⟩
    apply star_line_kernel_is_star L t ht ht1 ht2 hA hs hp
    exact ⟨v.property,hv⟩
  · intro hstar
    exact containing_star_plane_finrank_le_two L hstar hs hp

def nonstarPlane1 (a b : ℂ) : Fin 4 × Fin 4 → ℂ :=
  fun p => (!![0, a, a, -2*a; a, 0, 0, b; a, 0, 0, -b; -2*a, b, -b, 0] : Matrix (Fin 4) (Fin 4) ℂ) p.1 p.2

set_option maxHeartbeats 4000000 in
lemma nonstar1_normalized_zero (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (h01 : V (0,1) = 0)
    (h13 : V (1,3) = 0)
    (hp : ∀ a b z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + nonstarPlane1 a b (i,j) + z * V (i,j)) = 24) :
    V = 0 := by
  have hs10 := hs 1 0
  have hs20 := hs 2 0
  have hs30 := hs 3 0
  have hs21 := hs 2 1
  have hs31 := hs 3 1
  have hs32 := hs 3 2
  have hl : ∀ a b : ℂ, 4*a^2*b*V (1,1) - 4*a^2*b*V (2,2) + a^2*V (1,1) + 2*a^2*V (1,2) + a^2*V (2,2) - 4*a^2*V (2,3) + 4*a^2*V (3,3) + 4*a*b*V (0,2) + 2*a*b*V (1,1) - 2*a*b*V (2,2) - 4*a*V (1,1) - 8*a*V (1,2) - 4*a*V (2,2) + 4*a*V (2,3) + 8*a*V (3,3) + b^2*V (1,1) - 2*b^2*V (1,2) + b^2*V (2,2) + 4*b*V (0,2) - 4*b*V (1,1) + 4*b*V (2,2) + 6*V (0,0) + 12*V (0,2) + 12*V (0,3) + 6*V (1,1) + 12*V (1,2) + 6*V (2,2) + 12*V (2,3) + 6*V (3,3) = 0 := by
    intro a b
    have h₁ := hp a b 1
    have h₂ := hp a b (-1)
    have h₃ := hp a b 2
    have h₄ := hp a b (-2)
    rw [permanent_four] at h₁ h₂ h₃ h₄
    simp [nonstarPlane1, hs10, hs20, hs30, hs21, hs31, hs32, h01, h13] at h₁ h₂ h₃ h₄
    linear_combination (2 / 3 : ℂ) * h₁ - (2 / 3 : ℂ) * h₂ -
      (1 / 12 : ℂ) * h₃ + (1 / 12 : ℂ) * h₄
  have h0 := hl (0) (0)
  have h1 := hl (1) (0)
  have h2 := hl (-1) (0)
  have h3 := hl (0) (1)
  have h4 := hl (0) (-1)
  have h5 := hl (1) (1)
  have hv00 : V (0,0) = -2*V (0,3) - 9*V (3,3) := by
    linear_combination (-31/30 : ℂ) * h0 + (19/20 : ℂ) * h1 + (1/4 : ℂ) * h2 + (1/20 : ℂ) * h3 + (3/20 : ℂ) * h4 + (-1/5 : ℂ) * h5
  have hv02 : V (0,2) = 0 := by
    linear_combination (1/10 : ℂ) * h0 + (-1/10 : ℂ) * h1 + (-1/40 : ℂ) * h3 + (-3/40 : ℂ) * h4 + (1/10 : ℂ) * h5
  have hv11 : V (1,1) = V (3,3) := by
    linear_combination (-7/60 : ℂ) * h0 + (-2/15 : ℂ) * h1 + (1/20 : ℂ) * h3 + (3/20 : ℂ) * h4 + (1/20 : ℂ) * h5
  have hv12 : V (1,2) = V (3,3) := by
    linear_combination (1/3 : ℂ) * h0 + (-1/12 : ℂ) * h1 + (-1/8 : ℂ) * h3 + (-1/8 : ℂ) * h4
  have hv22 : V (2,2) = V (3,3) := by
    linear_combination (-13/60 : ℂ) * h0 + (-1/30 : ℂ) * h1 + (1/5 : ℂ) * h3 + (1/10 : ℂ) * h4 + (-1/20 : ℂ) * h5
  have hv23 : V (2,3) = 2*V (3,3) := by
    linear_combination (1/3 : ℂ) * h0 + (-5/24 : ℂ) * h1 + (-1/8 : ℂ) * h2
  let r := V (3,3)
  let u := V (0,3)
  have hpoly : ∀ z : ℂ,
      2*(u^2-6*u*r-63*r^2)*z^2 + 4*r*(u^2-6*u*r-39*r^2)*z^3 +
      2*r^2*(u-9*r)*(u+3*r)*z^4 = 0 := by
    intro z
    have hz := hp 0 0 z
    rw [permanent_four] at hz
    simp [nonstarPlane1, hs10, hs20, hs30, hs21, hs31, hs32, h01, h13, hv00, hv02, hv11, hv12, hv22, hv23] at hz
    dsimp [u,r]
    linear_combination hz
  have hq : 2*(u^2-6*u*r-63*r^2) = 0 :=
    (quartic_first_coefficients 0 _ _ _ (by simpa using hpoly)).2
  have hc : 4*r*(u^2-6*u*r-39*r^2) = 0 := by
    have h₁ := hpoly 1
    have h₂ := hpoly (-1)
    linear_combination h₁ / 2 - h₂ / 2
  have hr3 : r^3 = 0 := by linear_combination hc / 96 - r * hq / 48
  have hr : r = 0 := eq_zero_of_pow_eq_zero hr3
  have hu2 : u^2 = 0 := by rw [hr] at hq; linear_combination hq / 2
  have hu : u = 0 := eq_zero_of_pow_eq_zero hu2
  have hv03 : V (0,3) = 0 := hu
  have hv33 : V (3,3) = 0 := hr
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [hs10, hs20, hs30, hs21, hs31, hs32, h01, h13, hv00, hv02, hv11, hv12, hv22, hv23, hv03, hv33]

def nonstarPlane2 (a b : ℂ) : Fin 4 × Fin 4 → ℂ :=
  fun p => (!![0, a, b, -a - b; a, 0, a - b, -2*a - b; b, a - b, 0, a + 2*b; -a - b, -2*a - b, a + 2*b, 0] : Matrix (Fin 4) (Fin 4) ℂ) p.1 p.2

set_option maxHeartbeats 4000000 in
lemma nonstar2_normalized_zero (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (h01 : V (0,1) = 0)
    (h02 : V (0,2) = 0)
    (hp : ∀ a b z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + nonstarPlane2 a b (i,j) + z * V (i,j)) = 24) :
    V = 0 := by
  have hs10 := hs 1 0
  have hs20 := hs 2 0
  have hs30 := hs 3 0
  have hs21 := hs 2 1
  have hs31 := hs 3 1
  have hs32 := hs 3 2
  have hl : ∀ a b : ℂ, -4*a^3*V (0,0) + 4*a^3*V (2,2) - 6*a^2*b*V (0,0) - 2*a^2*b*V (1,1) + 6*a^2*b*V (2,2) + 2*a^2*b*V (3,3) - 4*a^2*V (0,3) - 4*a^2*V (1,2) + 4*a^2*V (2,2) - 4*a^2*V (2,3) + 4*a^2*V (3,3) + 6*a*b^2*V (0,0) - 6*a*b^2*V (1,1) + 2*a*b^2*V (2,2) - 2*a*b^2*V (3,3) - 8*a*b*V (1,2) + 8*a*b*V (2,2) + 4*a*V (0,3) - 4*a*V (1,2) - 8*a*V (2,2) + 4*a*V (2,3) + 8*a*V (3,3) + 4*b^3*V (0,0) - 4*b^3*V (1,1) + 4*b^2*V (0,3) + 4*b^2*V (1,1) - 4*b^2*V (1,2) - 4*b^2*V (1,3) + 4*b^2*V (2,2) - 4*b*V (0,3) + 8*b*V (1,1) - 4*b*V (1,2) + 4*b*V (1,3) - 8*b*V (2,2) + 6*V (0,0) + 12*V (0,3) + 6*V (1,1) + 12*V (1,2) + 12*V (1,3) + 6*V (2,2) + 12*V (2,3) + 6*V (3,3) = 0 := by
    intro a b
    have h₁ := hp a b 1
    have h₂ := hp a b (-1)
    have h₃ := hp a b 2
    have h₄ := hp a b (-2)
    rw [permanent_four] at h₁ h₂ h₃ h₄
    simp [nonstarPlane2, hs10, hs20, hs30, hs21, hs31, hs32, h01, h02] at h₁ h₂ h₃ h₄
    linear_combination (2 / 3 : ℂ) * h₁ - (2 / 3 : ℂ) * h₂ -
      (1 / 12 : ℂ) * h₃ + (1 / 12 : ℂ) * h₄
  have h0 := hl (0) (0)
  have h1 := hl (1) (0)
  have h2 := hl (-1) (0)
  have h3 := hl (0) (1)
  have h4 := hl (0) (-1)
  have h5 := hl (1) (1)
  have h6 := hl (-1) (1)
  have hv00 : V (0,0) = V (3,3) := by
    linear_combination (-1/54 : ℂ) * h0 + (-1/18 : ℂ) * h1 + (1/18 : ℂ) * h2 + (1/12 : ℂ) * h3 + (-1/108 : ℂ) * h5 + (-1/18 : ℂ) * h6
  have hv03 : V (0,3) = -5*V (3,3) := by
    linear_combination (-65/72 : ℂ) * h0 + (19/24 : ℂ) * h1 + (1/3 : ℂ) * h2 + (1/4 : ℂ) * h3 + (1/8 : ℂ) * h4 + (-11/36 : ℂ) * h5 + (-5/24 : ℂ) * h6
  have hv11 : V (1,1) = V (3,3) := by
    linear_combination (1/9 : ℂ) * h0 + (-1/6 : ℂ) * h1 + (-1/12 : ℂ) * h2 + (1/18 : ℂ) * h5 + (1/12 : ℂ) * h6
  have hv12 : V (1,2) = V (3,3) := by
    linear_combination (29/216 : ℂ) * h0 + (-7/72 : ℂ) * h1 + (-1/36 : ℂ) * h2 + (-1/24 : ℂ) * h3 + (1/216 : ℂ) * h5 + (1/36 : ℂ) * h6
  have hv13 : V (1,3) = -4*V (3,3) := by
    linear_combination (-53/108 : ℂ) * h0 + (19/36 : ℂ) * h1 + (2/9 : ℂ) * h2 + (1/12 : ℂ) * h3 + (-35/216 : ℂ) * h5 + (-7/72 : ℂ) * h6
  have hv22 : V (2,2) = V (3,3) := by
    linear_combination (5/27 : ℂ) * h0 + (-7/36 : ℂ) * h1 + (-1/18 : ℂ) * h2 + (-1/12 : ℂ) * h3 + (5/54 : ℂ) * h5 + (1/18 : ℂ) * h6
  have hv23 : V (2,3) = 6*V (3,3) := by
    linear_combination (65/54 : ℂ) * h0 + (-73/72 : ℂ) * h1 + (-35/72 : ℂ) * h2 + (-7/24 : ℂ) * h3 + (-1/8 : ℂ) * h4 + (85/216 : ℂ) * h5 + (17/72 : ℂ) * h6
  let r := V (3,3)
  have hpoly : ∀ z : ℂ, -16*r^2*z^2 + 64*r^3*z^3 + 56*r^4*z^4 = 0 := by
    intro z
    have hz := hp 0 0 z
    rw [permanent_four] at hz
    simp [nonstarPlane2, hs10, hs20, hs30, hs21, hs31, hs32, h01, h02, hv00, hv03, hv11, hv12, hv13, hv22, hv23] at hz
    dsimp [r]
    linear_combination hz
  have hq : -16*r^2 = 0 :=
    (quartic_first_coefficients 0 _ _ _ (by simpa using hpoly)).2
  have hr2 : r^2 = 0 := by linear_combination -hq / 16
  have hr : r = 0 := eq_zero_of_pow_eq_zero hr2
  have hv33 : V (3,3) = 0 := hr
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [hs10, hs20, hs30, hs21, hs31, hs32, h01, h02, hv00, hv03, hv11, hv12, hv13, hv22, hv23, hv33]

def ogrG (A B K : ℂ) : ℂ :=
  9*A^4 + 9*A^3*B + 9*A^3 + 9*A^2*B^2 + 18*A^2*B - 3*A^2*K + 5*A^2 - 6*A*B*K + 3*A*B - 6*A*K + A + K^2 - K

def ogrF (A B K : ℂ) : ℂ :=
  27*A^4*B + 9*A^4 + 27*A^3*B^2 + 63*A^3*B + 6*A^3*K + 21*A^3 + 27*A^2*B^3 + 72*A^2*B^2 - 3*A^2*B*K + 42*A^2*B + 3*A^2*K + 9*A^2 + 18*A*B^3 - 12*A*B^2*K + 42*A*B^2 - 12*A*B*K + 15*A*B - A*K^2 + A - 6*B^2*K + 3*B^2 + B*K^2 - 7*B*K + B - K^2 - K

def ogrEvenRoots (A B K : ℂ) : Prop :=
  A = (-1) ∧ B = (-1) ∧ K = (-1) ∨
  A = (-1) ∧ B = (-1) ∧ K = (1) ∨
  A = (-1) ∧ B = (0) ∧ K = (-1) ∨
  A = (-1) ∧ B = (1) ∧ K = (-3) ∨
  A = (-1) ∧ B = (1) ∧ K = (-1) ∨
  A = (-2/3) ∧ B = (-1/3) ∧ K = (0) ∨
  A = (-2/3) ∧ B = (0) ∧ K = (-1) ∨
  A = (-1/3) ∧ B = (-2/3) ∧ K = (0) ∨
  A = (-1/3) ∧ B = (-1/3) ∧ K = (-1/3) ∨
  A = (-1/3) ∧ B = (-1/3) ∧ K = (1/3) ∨
  A = (-1/3) ∧ B = (0) ∧ K = (0) ∨
  A = (0) ∧ B = (-1) ∧ K = (1) ∨
  A = (0) ∧ B = (-2/3) ∧ K = (1) ∨
  A = (0) ∧ B = (-1/3) ∧ K = (0) ∨
  A = (0) ∧ B = (0) ∧ K = (0) ∨
  A = (1) ∧ B = (-1) ∧ K = (1) ∨
  A = (1) ∧ B = (-1) ∧ K = (3)

lemma ogr_even_roots_swap (A B K : ℂ) (h : ogrEvenRoots A B K) :
    ogrEvenRoots B A (-K) := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    rcases h with ⟨rfl, rfl, rfl⟩
    norm_num [ogrEvenRoots]

lemma ogr_equal_case (A K : ℂ)
    (h0 : ogrG A A K = 0) (h1 : ogrF A A K = 0)
    (h3 : ogrG A A (-K) = 0) : ogrEvenRoots A A K := by
  have hc : K * (3*A+1)^2 = 0 := by
    dsimp [ogrG] at h0 h3
    linear_combination (h3-h0)/2
  rcases mul_eq_zero.mp hc with hk | ha
  · have ha : A = 0 := by
      dsimp [ogrG,ogrF] at h0 h1
      rw [hk] at h0 h1
      linear_combination 3*(A+1)*h0-h1
    norm_num [ogrEvenRoots,ha,hk]
  · have ha' : 3*A+1 = 0 := eq_zero_of_pow_eq_zero ha
    have ha : A = -1/3 := by linear_combination ha'/3
    have hk : (3*K-1)*(3*K+1) = 0 := by
      rw [ha] at h0
      dsimp [ogrG] at h0
      linear_combination 9*h0
    rcases mul_eq_zero.mp hk with hk | hk
    · have hk : K = 1/3 := by linear_combination hk/3
      norm_num [ogrEvenRoots,ha,hk]
    · have hk : K = -1/3 := by linear_combination hk/3
      norm_num [ogrEvenRoots,ha,hk]

set_option maxHeartbeats 4000000 in
lemma ogr_minus_case (A B K : ℂ) (hb : B+1 ≠ 0)
    (hk : K = 3*(A-B)-1)
    (h0 : ogrG A B K = 0) (h1 : ogrF A B K = 0)
    (h2 : ogrF B A (-K) = 0) (h3 : ogrG B A (-K) = 0) :
    ogrEvenRoots A B K := by
  have hc : A*(3*A+1) = 0 := by
    rw [hk] at h0 h1 h2 h3
    dsimp [ogrG,ogrF] at h0 h1 h2 h3
    linear_combination
      (-(1152*A*B^3 + 3024*A*B^2 + 3024*A*B + 1152*A + 3078*B^4 + 10989*B^3 + 10348*B^2 + 2981*B)/48) * h0 +
      ((336*A + 2745*B^3 + 5688*B^2 + 3272*B + 161)/48) * h1 +
      ((288*A^3 + 672*A^2*B + 126*A^2 - 516*A*B^2 - 369*A*B - 168*A - 630*B^2 - 737*B)/16) * h2 +
      (-(2592*A^4 + 4896*A^3*B + 2142*A^3 + 513*A^2*B^2 + 5283*A^2*B + 755*A^2 + 568*A - 513*B^2 - 1071*B + 287)/48) * h3
  rcases mul_eq_zero.mp hc with ha | ha
  · have hbc : (3*B+1)*(3*B+2) = 0 := by
      rw [hk,ha] at h0
      dsimp [ogrG] at h0
      linear_combination h0
    rcases mul_eq_zero.mp hbc with hb' | hb'
    · have hb' : B = -1/3 := by linear_combination hb'/3
      norm_num [ha,hb'] at hk
      norm_num [ogrEvenRoots,ha,hb',hk]
    · have hb' : B = -2/3 := by linear_combination hb'/3
      norm_num [ha,hb'] at hk
      norm_num [ogrEvenRoots,ha,hb',hk]
  · have ha : A = -1/3 := by linear_combination ha/3
    have hbc : (B+1)*(3*B+2) = 0 := by
      rw [hk,ha] at h0
      dsimp [ogrG] at h0
      linear_combination 3*h0/4
    have hb' : 3*B+2 = 0 := (mul_eq_zero.mp hbc).resolve_left hb
    have hb' : B = -2/3 := by linear_combination hb'/3
    norm_num [ha,hb'] at hk
    norm_num [ogrEvenRoots,ha,hb',hk]

lemma ogr_boundary_roots (B K : ℂ)
    (hB : B*(B-1)*(B+1)=0) (hK : K = -1 ∨ K = -2*B-1) :
    ogrEvenRoots (-1) B K := by
  have hcases : B = 0 ∨ B = 1 ∨ B = -1 := by
    rcases mul_eq_zero.mp hB with hB | hB
    · rcases mul_eq_zero.mp hB with hB | hB
      · exact Or.inl hB
      · right; left; linear_combination hB
    · right; right; linear_combination hB
  rcases hcases with rfl | rfl | rfl <;>
    rcases hK with rfl | rfl <;> norm_num [ogrEvenRoots]

set_option maxHeartbeats 4000000 in
lemma ogr_boundary_case (B K : ℂ)
    (h1 : ogrF (-1) B K = 0) (h2 : ogrF B (-1) (-K) = 0)
    (h3 : (B+1)*ogrG B (-1) (-K) = 0) : ogrEvenRoots (-1) B K := by
  have hc : (K+1)*(2*B+K+1)=0 := by
    dsimp [ogrG,ogrF] at h1 h2 h3
    linear_combination
      -(18*B^3+18*B^2+3*B*K+6*B+3*K+2)/4*h1 -
      (18*B^2+3*B*K+12*B+3*K+2)/4*h2 -
      3*(3*B+K+1)/2*h3
  rcases mul_eq_zero.mp hc with hk | hk
  · have hk : K = -1 := by linear_combination hk
    have hb : B*(B-1)*(B+1)=0 := by
      rw [hk] at h1
      dsimp [ogrF] at h1
      linear_combination h1/9
    exact ogr_boundary_roots B K hb (Or.inl hk)
  · have hk : K = -2*B-1 := by linear_combination hk
    have hb : B*(B-1)*(B+1)=0 := by
      rw [hk] at h1
      dsimp [ogrF] at h1
      linear_combination h1
    exact ogr_boundary_roots B K hb (Or.inr hk)

set_option maxHeartbeats 4000000 in
lemma hollow_even_chart_classification (A B K : ℂ)
    (h0 : (A+1)*ogrG A B K = 0) (h1 : ogrF A B K = 0)
    (h2 : ogrF B A (-K) = 0) (h3 : (B+1)*ogrG B A (-K) = 0) :
    ogrEvenRoots A B K := by
  by_cases ha : A+1 = 0
  · have ha : A = -1 := by linear_combination ha
    subst A
    exact ogr_boundary_case B K h1 h2 h3
  by_cases hb : B+1 = 0
  · have hb : B = -1 := by linear_combination hb
    subst B
    have hr := ogr_boundary_case A (-K) h2 (by simpa using h1) (by simpa using h0)
    simpa using ogr_even_roots_swap (-1) A (-K) hr
  have hg0 : ogrG A B K = 0 := (mul_eq_zero.mp h0).resolve_left ha
  have hg3 : ogrG B A (-K) = 0 := (mul_eq_zero.mp h3).resolve_left hb
  have hc : (A-B)*(3*A-3*B-K-1)*(3*A-3*B-K+1) = 0 := by
    dsimp [ogrG,ogrF] at hg0 h1 h2 hg3
    linear_combination -(B+1)^2*hg0+(B+1)*h1-(A+1)*h2+(A+1)^2*hg3
  rcases mul_eq_zero.mp hc with hc | hc
  · rcases mul_eq_zero.mp hc with hab | hk
    · have hab : B = A := by linear_combination -hab
      subst B
      exact ogr_equal_case A K hg0 h1 hg3
    · have hk : K = 3*(A-B)-1 := by linear_combination -hk
      exact ogr_minus_case A B K hb hk hg0 h1 h2 hg3
  · have hk : -K = 3*(B-A)-1 := by linear_combination hc
    have hr := ogr_minus_case B A (-K) ha hk hg3 h2
      (by simpa using h1) (by simpa using hg0)
    simpa using ogr_even_roots_swap B A (-K) hr

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

def wittQ (u : Fin 5 → ℂ) : ℂ := u 0*u 2+u 1*u 3-3*(u 4)^2

def wittPolar (u v : Fin 5 → ℂ) : ℂ :=
  u 0*v 2+u 2*v 0+u 1*v 3+u 3*v 1-6*u 4*v 4

def wittMinor (u v : Fin 5 → ℂ) (i j : Fin 5) : ℂ := u i*v j-u j*v i

def wittTriangleMinor (u v : Fin 5 → ℂ) : Fin 4 → ℂ :=
  ![wittMinor u v 0 1,
    (u 0-u 3)*(-v 0-v 1-v 2-2*v 3-6*v 4)-
      (v 0-v 3)*(-u 0-u 1-u 2-2*u 3-6*u 4),
    (u 1-u 2)*(-v 0-v 1-2*v 2-v 3-6*v 4)-
      (v 1-v 2)*(-u 0-u 1-2*u 2-u 3-6*u 4),
    -wittMinor u v 2 3]

set_option maxHeartbeats 4000000 in
lemma hollow_triangle_minors_zero (u v : Fin 5 → ℂ)
    (hqu : wittQ u = 0) (hqv : wittQ v = 0) (hb : wittPolar u v = 0)
    (ht : ∀ k : Fin 4, wittTriangleMinor u v k = 0) :
    ∀ i j : Fin 5, wittMinor u v i j = 0 := by
  have h01 : wittMinor u v 0 1 = 0 := by simpa [wittTriangleMinor] using ht 0
  have h23 : wittMinor u v 2 3 = 0 := by simpa [wittTriangleMinor] using ht 3
  have h04s : (wittMinor u v 0 4)^2 = 0 := by
    dsimp [wittQ,wittPolar,wittMinor] at hqu hqv hb h01 ⊢
    linear_combination -(v 0)^2/3*hqu-(u 0)^2/3*hqv+u 0*v 0/3*hb+
      (u 0*v 3-u 3*v 0)/3*h01
  have h14s : (wittMinor u v 1 4)^2 = 0 := by
    dsimp [wittQ,wittPolar,wittMinor] at hqu hqv hb h01 ⊢
    linear_combination -(v 1)^2/3*hqu-(u 1)^2/3*hqv+u 1*v 1/3*hb-
      (u 1*v 2-u 2*v 1)/3*h01
  have h24s : (wittMinor u v 2 4)^2 = 0 := by
    dsimp [wittQ,wittPolar,wittMinor] at hqu hqv hb h23 ⊢
    linear_combination -(v 2)^2/3*hqu-(u 2)^2/3*hqv+u 2*v 2/3*hb-
      (u 1*v 2-u 2*v 1)/3*h23
  have h34s : (wittMinor u v 3 4)^2 = 0 := by
    dsimp [wittQ,wittPolar,wittMinor] at hqu hqv hb h23 ⊢
    linear_combination -(v 3)^2/3*hqu-(u 3)^2/3*hqv+u 3*v 3/3*hb+
      (u 0*v 3-u 3*v 0)/3*h23
  have h04 : wittMinor u v 0 4 = 0 := eq_zero_of_pow_eq_zero h04s
  have h14 : wittMinor u v 1 4 = 0 := eq_zero_of_pow_eq_zero h14s
  have h24 : wittMinor u v 2 4 = 0 := eq_zero_of_pow_eq_zero h24s
  have h34 : wittMinor u v 3 4 = 0 := eq_zero_of_pow_eq_zero h34s
  have hsum2 : (wittMinor u v 0 2+wittMinor u v 1 3)^2 = 0 := by
    dsimp [wittQ,wittPolar,wittMinor] at hqu hqv hb h01 ⊢
    linear_combination -4*(v 0*v 2+v 1*v 3)*hqu-12*(u 4)^2*hqv+
      (u 0*v 2+u 2*v 0+u 1*v 3+u 3*v 1+6*u 4*v 4)*hb+
      4*(u 2*v 3-u 3*v 2)*h01
  have hsum : wittMinor u v 0 2+wittMinor u v 1 3 = 0 :=
    eq_zero_of_pow_eq_zero hsum2
  have h03 : wittMinor u v 0 3 = 0 := by
    have hh := ht 1
    simp [wittTriangleMinor] at hh
    dsimp [wittMinor] at h01 hsum h04 h23 h34 ⊢
    linear_combination -hh/3-h01/3-hsum/3-2*h04-h23/3+2*h34
  have h12 : wittMinor u v 1 2 = 0 := by
    have hh := ht 2
    simp [wittTriangleMinor] at hh
    dsimp [wittMinor] at h01 hsum h14 h23 h24 ⊢
    linear_combination -hh/3+h01/3-hsum/3-2*h14+h23/3+2*h24
  have h02s : (wittMinor u v 0 2)^2 = 0 := by
    dsimp [wittMinor] at hsum h01 h03 ⊢
    linear_combination (u 0*v 2-u 2*v 0)*hsum-
      (u 2*v 3-u 3*v 2)*h01-(u 1*v 2-u 2*v 1)*h03
  have h02 : wittMinor u v 0 2 = 0 := eq_zero_of_pow_eq_zero h02s
  have h13 : wittMinor u v 1 3 = 0 := by linear_combination hsum-h02
  intro i j
  fin_cases i <;> fin_cases j <;>
    dsimp [wittMinor] at h01 h02 h03 h04 h12 h13 h14 h23 h24 h34 ⊢ <;>
    solve
    | ring
    | linear_combination h01
    | linear_combination -h01
    | linear_combination h02
    | linear_combination -h02
    | linear_combination h03
    | linear_combination -h03
    | linear_combination h04
    | linear_combination -h04
    | linear_combination h12
    | linear_combination -h12
    | linear_combination h13
    | linear_combination -h13
    | linear_combination h14
    | linear_combination -h14
    | linear_combination h23
    | linear_combination -h23
    | linear_combination h24
    | linear_combination -h24
    | linear_combination h34
    | linear_combination -h34

lemma hollow_triangle_covers_nonzero_minor (u v : Fin 5 → ℂ)
    (hqu : wittQ u = 0) (hqv : wittQ v = 0) (hb : wittPolar u v = 0)
    (hi : ∃ i j : Fin 5, wittMinor u v i j ≠ 0) :
    ∃ k : Fin 4, wittTriangleMinor u v k ≠ 0 := by
  by_contra hh
  push Not at hh
  obtain ⟨i,j,hij⟩ := hi
  exact hij (hollow_triangle_minors_zero u v hqu hqv hb hh i j)

lemma witt_pair_independent_has_minor (u v : Fin 5 → ℂ)
    (hi : LinearIndependent ℂ ![u,v]) : ∃ i j : Fin 5, wittMinor u v i j ≠ 0 := by
  by_contra hh
  push Not at hh
  have hlin := linearIndependent_fin2.mp hi
  change v ≠ 0 ∧ ∀ a : ℂ, a • v ≠ u at hlin
  obtain ⟨i,hvi⟩ : ∃ i : Fin 5, v i ≠ 0 := by
    by_contra hv
    push Not at hv
    apply hlin.1
    funext i
    exact hv i
  apply hlin.2 (u i / v i)
  funext j
  change u i / v i * v j = u j
  have h := hh i j
  dsimp [wittMinor] at h
  field_simp [hvi]
  linear_combination h

lemma hollow_triangle_covers_independent_pair (u v : Fin 5 → ℂ)
    (hqu : wittQ u = 0) (hqv : wittQ v = 0) (hb : wittPolar u v = 0)
    (hi : LinearIndependent ℂ ![u,v]) :
    ∃ k : Fin 4, wittTriangleMinor u v k ≠ 0 := by
  exact hollow_triangle_covers_nonzero_minor u v hqu hqv hb
    (witt_pair_independent_has_minor u v hi)

lemma normalize_two_linear_coordinates
    (W : Submodule ℂ (Fin 5 → ℂ))
    (F G : (Fin 5 → ℂ) →ₗ[ℂ] ℂ)
    (u v : Fin 5 → ℂ) (hu : u ∈ W) (hv : v ∈ W)
    (hd : F u*G v-F v*G u ≠ 0) :
    ∃ a ∈ W, ∃ b ∈ W, F a=1 ∧ G a=0 ∧ F b=0 ∧ G b=1 := by
  have hd' : G v*F u-F v*G u ≠ 0 := by simpa [mul_comm] using hd
  let d := F u*G v-F v*G u
  let a := (G v/d) • u-(G u/d) • v
  let b := (F u/d) • v-(F v/d) • u
  refine ⟨a,W.sub_mem (W.smul_mem _ hu) (W.smul_mem _ hv),
    b,W.sub_mem (W.smul_mem _ hv) (W.smul_mem _ hu),?_,?_,?_,?_⟩
  all_goals
    dsimp [a,b,d]
    simp only [map_sub,map_smul,smul_eq_mul]
    field_simp [hd,hd'] <;> ring

lemma isotropic_even_chart_normal_form (u v : Fin 5 → ℂ)
    (hu0 : u 0=1) (hu1 : u 1=0) (hv0 : v 0=0) (hv1 : v 1=1)
    (hqu : wittQ u=0) (hqv : wittQ v=0) (hb : wittPolar u v=0) :
    ∃ A B K : ℂ,
      u = ![1,0,3*A^2,3*A*B-K,A] ∧
      v = ![0,1,3*A*B+K,3*B^2,B] := by
  have hu2 : u 2=3*(u 4)^2 := by
    dsimp [wittQ] at hqu
    rw [hu0,hu1] at hqu
    linear_combination hqu
  have hv3 : v 3=3*(v 4)^2 := by
    dsimp [wittQ] at hqv
    rw [hv0,hv1] at hqv
    linear_combination hqv
  have hu3 : u 3=6*u 4*v 4-v 2 := by
    dsimp [wittPolar] at hb
    rw [hu0,hu1,hv0,hv1] at hb
    linear_combination hb
  refine ⟨u 4,v 4,v 2-3*u 4*v 4,?_,?_⟩
  · funext i
    fin_cases i <;> simp [hu0,hu1,hu2,hu3] <;> ring
  · funext i
    fin_cases i <;> simp [hv0,hv1,hv3]

lemma finrank_le_two_of_zero_coordinate_kernel
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (p q : Fin 4 × Fin 4)
    (hk : ∀ V ∈ L, V p=0 → V q=0 → V=0) : Module.finrank ℂ L ≤ 2 := by
  let F : L →ₗ[ℂ] (Fin 2 → ℂ) :=
    { toFun := fun V => ![V.val p,V.val q]
      map_add' := by intros; ext i; fin_cases i <;> simp
      map_smul' := by intros; ext i; fin_cases i <;> simp }
  have hker : ∀ V : L, F V=0 → V=0 := by
    intro V hV
    apply Subtype.ext
    have hp : V.val p=0 := by simpa [F] using congrFun hV 0
    have hq : V.val q=0 := by simpa [F] using congrFun hV 1
    exact hk V.val V.property hp hq
  have hF : Function.Injective F := by
    intro V W h
    apply sub_eq_zero.mp
    apply hker (V-W)
    rw [map_sub,h,sub_self]
  have hd := Submodule.finrank_le (LinearMap.range F)
  rw [LinearMap.finrank_range_of_inj hF] at hd
  simpa using hd

lemma containing_nonstar1_plane_finrank_le_two
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hc : ∀ a b : ℂ, nonstarPlane1 a b ∈ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) : Module.finrank ℂ L ≤ 2 := by
  apply finrank_le_two_of_zero_coordinate_kernel L (0,1) (1,3)
  intro V hV h01 h13
  apply nonstar1_normalized_zero V (hs V hV) h01 h13
  intro a b z
  have h := hp _ (L.add_mem (hc a b) (L.smul_mem z hV))
  simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_assoc] using h

lemma containing_nonstar2_plane_finrank_le_two
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hc : ∀ a b : ℂ, nonstarPlane2 a b ∈ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) : Module.finrank ℂ L ≤ 2 := by
  apply finrank_le_two_of_zero_coordinate_kernel L (0,1) (0,2)
  intro V hV h01 h02
  apply nonstar2_normalized_zero V (hs V hV) h01 h02
  intro a b z
  have h := hp _ (L.add_mem (hc a b) (L.smul_mem z hV))
  simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_assoc] using h

def canonicalHollowPlane (k : Fin 3) (a b : ℂ) : Fin 4 × Fin 4 → ℂ :=
  ![starMatrix a b,nonstarPlane1 a b,nonstarPlane2 a b] k

lemma containing_canonical_hollow_plane_finrank_le_two
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (k : Fin 3)
    (hc : ∀ a b : ℂ, canonicalHollowPlane k a b ∈ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) : Module.finrank ℂ L ≤ 2 := by
  fin_cases k
  · apply containing_star_plane_finrank_le_two L ?_ hs hp
    rintro V ⟨v,rfl⟩
    simpa [canonicalHollowPlane,starMap] using hc (v 0) (v 1)
  · apply containing_nonstar1_plane_finrank_le_two L ?_ hs hp
    intro a b
    simpa [canonicalHollowPlane] using hc a b
  · apply containing_nonstar2_plane_finrank_le_two L ?_ hs hp
    intro a b
    simpa [canonicalHollowPlane] using hc a b

lemma hollow_coefficient_cubic_zero (a b c d e f : ℂ)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+z*hollowMatrix a b c d e f i j)=24) : hollowCubic a b c d e f=0 := by
  obtain ⟨hs,_⟩ := hollow_coefficient_constraints a b c d e f hp
  have h₁ := hp 1
  have h₂ := hp (-1)
  rw [permanent_hollow_scaled] at h₁ h₂
  linear_combination h₁/2-h₂/2-12*hs

lemma hollow_member_cubic_zero (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hz : ∀ V ∈ L, ∀ i : Fin 4, V (i,i)=0)
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24)
    (V : Fin 4 × Fin 4 → ℂ) (hV : V ∈ L) :
    hollowCubic (V (0,1)) (V (0,2)) (V (0,3)) (V (1,2)) (V (1,3)) (V (2,3))=0 := by
  apply hollow_coefficient_cubic_zero
  intro z
  have h := hp (z • V) (L.smul_mem z hV)
  convert h using 1
  congr 1
  funext i j
  change 1+z*hollowMatrix _ _ _ _ _ _ i j=1+z*V (i,j)
  rw [hollow_reconstruction V (hs V hV) (hz V hV) i j]

def entryPermute (σ : Equiv.Perm (Fin 4)) :
    (Fin 4 × Fin 4 → ℂ) ≃ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun V p := V (σ p.1,σ p.2)
  invFun V p := V (σ.symm p.1,σ.symm p.2)
  left_inv V := by
    funext p
    simp
  right_inv V := by
    funext p
    simp
  map_add' V W := rfl
  map_smul' c V := rfl

lemma entryPermute_apply (σ : Equiv.Perm (Fin 4))
    (V : Fin 4 × Fin 4 → ℂ) (i j : Fin 4) :
    entryPermute σ V (i,j)=V (σ i,σ j) := rfl

lemma entryPermute_symmetric (σ : Equiv.Perm (Fin 4))
    (V : Fin 4 × Fin 4 → ℂ)
    (h : ∀ i j : Fin 4, V (i,j)=V (j,i)) :
    ∀ i j : Fin 4, entryPermute σ V (i,j)=entryPermute σ V (j,i) := by
  intro i j
  exact h (σ i) (σ j)

lemma entryPermute_hollow (σ : Equiv.Perm (Fin 4))
    (V : Fin 4 × Fin 4 → ℂ) (h : ∀ i : Fin 4, V (i,i)=0) :
    ∀ i : Fin 4, entryPermute σ V (i,i)=0 := by
  intro i
  exact h (σ i)

lemma entryPermute_permanent (σ : Equiv.Perm (Fin 4))
    (V : Fin 4 × Fin 4 → ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+entryPermute σ V (i,j)) =
      Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j)) := by
  change Matrix.permanent
    (((Matrix.of fun (i j : Fin 4) => 1+V (i,j)).submatrix σ id).submatrix id σ) = _
  rw [Matrix.permanent_permute_rows,Matrix.permanent_permute_cols]

def entryPermuteSubmodule (σ : Equiv.Perm (Fin 4))
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) : Submodule ℂ (Fin 4 × Fin 4 → ℂ) :=
  L.map (entryPermute σ).toLinearMap

lemma entryPermuteSubmodule_finrank (σ : Equiv.Perm (Fin 4))
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) :
    Module.finrank ℂ (entryPermuteSubmodule σ L)=Module.finrank ℂ L := by
  exact LinearEquiv.finrank_map_eq (entryPermute σ) L

lemma entryPermute_mem_iff (σ : Equiv.Perm (Fin 4))
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (V : Fin 4 × Fin 4 → ℂ) :
    entryPermute σ V ∈ entryPermuteSubmodule σ L ↔ V ∈ L := by
  constructor
  · rintro ⟨W,hW,he⟩
    have hWV : W=V := (entryPermute σ).injective he
    simpa [hWV] using hW
  · intro hV
    exact ⟨V,hV,rfl⟩

lemma entryPermuteSubmodule_symmetric (σ : Equiv.Perm (Fin 4))
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (h : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i)) :
    ∀ V ∈ entryPermuteSubmodule σ L, ∀ i j : Fin 4, V (i,j)=V (j,i) := by
  rintro V ⟨W,hW,rfl⟩ i j
  exact h W hW (σ i) (σ j)

lemma entryPermuteSubmodule_hollow (σ : Equiv.Perm (Fin 4))
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (h : ∀ V ∈ L, ∀ i : Fin 4, V (i,i)=0) :
    ∀ V ∈ entryPermuteSubmodule σ L, ∀ i : Fin 4, V (i,i)=0 := by
  rintro V ⟨W,hW,rfl⟩ i
  exact h W hW (σ i)

lemma entryPermuteSubmodule_permanent (σ : Equiv.Perm (Fin 4))
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (h : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    ∀ V ∈ entryPermuteSubmodule σ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24 := by
  rintro V ⟨W,hW,rfl⟩
  change Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
    1+entryPermute σ W (i,j))=24
  exact (entryPermute_permanent σ W).trans (h W hW)

def hollowWittMatrix (u : Fin 5 → ℂ) : Fin 4 × Fin 4 → ℂ :=
  fun p => hollowMatrix (u 0+u 4) (u 1+u 4)
    (-u 0-u 1-u 2-u 3-5*u 4) (u 4) (u 3+u 4) (u 2+u 4) p.1 p.2

def triangleCoordinatePerm (k : Fin 4) : Equiv.Perm (Fin 4) :=
  ![1,Equiv.swap 2 3,
    Equiv.swap 1 2 * Equiv.swap 2 3,
    Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3] k

def leadingTriangleMinor (U V : Fin 4 × Fin 4 → ℂ) : ℂ :=
  (U (0,1)-U (1,2))*(V (0,2)-V (1,2))-
    (V (0,1)-V (1,2))*(U (0,2)-U (1,2))

lemma leadingTriangleMinor_permute_witt (u v : Fin 5 → ℂ) (k : Fin 4) :
    leadingTriangleMinor (entryPermute (triangleCoordinatePerm k) (hollowWittMatrix u))
      (entryPermute (triangleCoordinatePerm k) (hollowWittMatrix v)) =
      ![u 0*v 1-u 1*v 0,
        (u 0-u 3)*(-v 0-v 1-v 2-2*v 3-6*v 4)-
          (v 0-v 3)*(-u 0-u 1-u 2-2*u 3-6*u 4),
        (u 1-u 2)*(-v 0-v 1-2*v 2-v 3-6*v 4)-
          (v 1-v 2)*(-u 0-u 1-2*u 2-u 3-6*u 4),
        -(u 2*v 3-u 3*v 2)] k := by
  fin_cases k <;>
    simp [leadingTriangleMinor,entryPermute,triangleCoordinatePerm,hollowWittMatrix,
      hollowMatrix,Equiv.Perm.mul_apply,Equiv.swap_apply_def] <;>
    ring

def hollowWittCoordinates : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ) where
  toFun V := ![V (0,1)-V (1,2),V (0,2)-V (1,2),
    V (2,3)-V (1,2),V (1,3)-V (1,2),V (1,2)]
  map_add' := by intros; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intros; ext i; fin_cases i <;> simp <;> ring

def wittMatrix : (Fin 5 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun u := fun p => hollowMatrix (u 0+u 4) (u 1+u 4)
    (-u 0-u 1-u 2-u 3-5*u 4) (u 4) (u 3+u 4) (u 2+u 4) p.1 p.2
  map_add' := by
    intros
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [hollowMatrix] <;> ring
  map_smul' := by
    intros
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [hollowMatrix] <;> ring

def wittCubic (u : Fin 5 → ℂ) : ℂ :=
  hollowCubic (u 0+u 4) (u 1+u 4) (-u 0-u 1-u 2-u 3-5*u 4)
    (u 4) (u 3+u 4) (u 2+u 4)

lemma hollowWittCoordinates_wittMatrix (u : Fin 5 → ℂ) :
    hollowWittCoordinates (wittMatrix u)=u := by
  funext i
  fin_cases i <;> simp [hollowWittCoordinates,wittMatrix,hollowMatrix]

lemma wittMatrix_hollowWittCoordinates (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j)=V (j,i)) (hz : ∀ i : Fin 4, V (i,i)=0)
    (hS : V (0,1)+V (0,2)+V (0,3)+V (1,2)+V (1,3)+V (2,3)=0) :
    wittMatrix (hollowWittCoordinates V)=V := by
  funext p
  rcases p with ⟨i,j⟩
  change hollowMatrix _ _ _ _ _ _ i j=V (i,j)
  rw [hollow_reconstruction V hs hz i j]
  fin_cases i <;> fin_cases j <;>
    simp [hollowWittCoordinates,hollowMatrix] <;>
    solve
    | ring
    | linear_combination hS
    | linear_combination -hS

lemma wittQ_hollowWittCoordinates (V : Fin 4 × Fin 4 → ℂ)
    (hS : V (0,1)+V (0,2)+V (0,3)+V (1,2)+V (1,3)+V (2,3)=0) :
    wittQ (hollowWittCoordinates V)=V (0,1)*V (2,3)+V (0,2)*V (1,3)+V (0,3)*V (1,2) := by
  dsimp [wittQ,hollowWittCoordinates]
  linear_combination -V (1,2)*hS

lemma wittCubic_eq_matrix_cubic (u : Fin 5 → ℂ) :
    wittCubic u=hollowCubic ((wittMatrix u) (0,1)) ((wittMatrix u) (0,2))
      ((wittMatrix u) (0,3)) ((wittMatrix u) (1,2)) ((wittMatrix u) (1,3))
      ((wittMatrix u) (2,3)) := by simp [wittCubic,wittMatrix,hollowMatrix]

lemma hollow_witt_image_finrank
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hz : ∀ V ∈ L, ∀ i : Fin 4, V (i,i)=0)
    (hS : ∀ V ∈ L, V (0,1)+V (0,2)+V (0,3)+V (1,2)+V (1,3)+V (2,3)=0) :
    Module.finrank ℂ (L.map hollowWittCoordinates)=Module.finrank ℂ L := by
  let F := hollowWittCoordinates.domRestrict L
  have hF : Function.Injective F := by
    intro V W h
    apply Subtype.ext
    change hollowWittCoordinates V.val=hollowWittCoordinates W.val at h
    have hV := wittMatrix_hollowWittCoordinates V.val (hs _ V.property)
      (hz _ V.property) (hS _ V.property)
    have hW := wittMatrix_hollowWittCoordinates W.val (hs _ W.property)
      (hz _ W.property) (hS _ W.property)
    rw [← hV,← hW,h]
  have hd := LinearMap.finrank_range_of_inj hF
  change Module.finrank ℂ (LinearMap.range (hollowWittCoordinates.domRestrict L))=
    Module.finrank ℂ L at hd
  rw [LinearMap.range_domRestrict] at hd
  exact hd

lemma hollow_witt_image_constraints
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hz : ∀ V ∈ L, ∀ i : Fin 4, V (i,i)=0)
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    (∀ u ∈ L.map hollowWittCoordinates, wittQ u=0) ∧
    (∀ u ∈ L.map hollowWittCoordinates, wittCubic u=0) := by
  constructor
  · rintro u ⟨V,hV,rfl⟩
    obtain ⟨hS,hq⟩ := hollow_member_constraints L hs hz hp V hV
    rw [wittQ_hollowWittCoordinates V hS]
    exact hq
  · rintro u ⟨V,hV,rfl⟩
    have hS := (hollow_member_constraints L hs hz hp V hV).1
    rw [wittCubic_eq_matrix_cubic,
      wittMatrix_hollowWittCoordinates V (hs _ hV) (hz _ hV) hS]
    exact hollow_member_cubic_zero L hs hz hp V hV

lemma witt_polar_zero_of_submodule (W : Submodule ℂ (Fin 5 → ℂ))
    (hq : ∀ u ∈ W, wittQ u=0) (u v : Fin 5 → ℂ) (hu : u ∈ W) (hv : v ∈ W) :
    wittPolar u v=0 := by
  have h₁ := hq u hu
  have h₂ := hq v hv
  have h₃ := hq (u+v) (W.add_mem hu hv)
  dsimp [wittQ,wittPolar] at h₁ h₂ h₃ ⊢
  linear_combination h₃-h₁-h₂

lemma witt_submodule_has_triangle_chart (W : Submodule ℂ (Fin 5 → ℂ))
    (hq : ∀ u ∈ W, wittQ u=0) (hd : 2 ≤ Module.finrank ℂ W) :
    ∃ u ∈ W, ∃ v ∈ W, ∃ k : Fin 4, wittTriangleMinor u v k ≠ 0 := by
  obtain ⟨f,hf⟩ := exists_linearIndependent_of_le_finrank hd
  have hi := hf.map_injOn W.subtype (fun _ _ _ _ h => Subtype.ext h)
  have heq : W.subtype ∘ f=![((f 0).val),((f 1).val)] := by
    funext i
    fin_cases i <;> rfl
  rw [heq] at hi
  refine ⟨(f 0).val,(f 0).property,(f 1).val,(f 1).property,?_⟩
  apply hollow_triangle_covers_independent_pair _ _ (hq _ (f 0).property)
    (hq _ (f 1).property) ?_ hi
  exact witt_polar_zero_of_submodule W hq _ _ (f 0).property (f 1).property

def evenChartVector (A B K s t : ℂ) : Fin 5 → ℂ :=
  ![s,t,3*A*(A*s+B*t)+K*t,3*B*(A*s+B*t)-K*s,A*s+B*t]

lemma evenChartVector_linear_combination (A B K s t : ℂ) :
    evenChartVector A B K s t =
      s • ![1,0,3*A^2,3*A*B-K,A]+t • ![0,1,3*A*B+K,3*B^2,B] := by
  funext i
  fin_cases i <;> simp [evenChartVector] <;> ring

set_option maxHeartbeats 4000000 in
lemma wittCubic_evenChartVector (A B K s t : ℂ) :
    wittCubic (evenChartVector A B K s t) =
      -2*((A+1)*ogrG A B K*s^3+ogrF A B K*s^2*t+
        ogrF B A (-K)*s*t^2+(B+1)*ogrG B A (-K)*t^3) := by
  simp [wittCubic,evenChartVector,hollowCubic,ogrG,ogrF]
  ring

lemma even_chart_cubic_classification (A B K : ℂ)
    (hc : ∀ s t : ℂ, wittCubic (evenChartVector A B K s t)=0) :
    ogrEvenRoots A B K := by
  have h10 := hc 1 0
  have h01 := hc 0 1
  have h11 := hc 1 1
  have h1m := hc 1 (-1)
  rw [wittCubic_evenChartVector] at h10 h01 h11 h1m
  apply hollow_even_chart_classification A B K
  · linear_combination -h10/2
  · linear_combination (h1m-h11)/4+h01/2
  · linear_combination -(h11+h1m)/4+h10/2
  · linear_combination -h01/2

lemma isotropic_normalized_pair_classified (W : Submodule ℂ (Fin 5 → ℂ))
    (hq : ∀ u ∈ W, wittQ u=0) (hc : ∀ u ∈ W, wittCubic u=0)
    (u v : Fin 5 → ℂ) (hu : u ∈ W) (hv : v ∈ W)
    (hu0 : u 0=1) (hu1 : u 1=0) (hv0 : v 0=0) (hv1 : v 1=1) :
    ∃ A B K : ℂ, ogrEvenRoots A B K ∧
      u=![1,0,3*A^2,3*A*B-K,A] ∧ v=![0,1,3*A*B+K,3*B^2,B] := by
  obtain ⟨A,B,K,hU,hV⟩ := isotropic_even_chart_normal_form u v hu0 hu1 hv0 hv1
    (hq u hu) (hq v hv) (witt_polar_zero_of_submodule W hq u v hu hv)
  refine ⟨A,B,K,?_,hU,hV⟩
  apply even_chart_cubic_classification A B K
  intro s t
  apply hc
  rw [evenChartVector_linear_combination,← hU,← hV]
  exact W.add_mem (W.smul_mem s hu) (W.smul_mem t hv)

set_option maxHeartbeats 4000000 in
lemma even_chart_contains_permuted_canonical
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (A B K : ℂ)
    (hr : ogrEvenRoots A B K)
    (hc : ∀ s t : ℂ, wittMatrix (evenChartVector A B K s t) ∈ L) :
    ∃ k : Fin 3, ∃ σ : Equiv.Perm (Fin 4),
      ∀ a b : ℂ, canonicalHollowPlane k a b ∈ entryPermuteSubmodule σ L := by
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨rfl,rfl,rfl⟩
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![2,0,3,1] (by decide)
    refine ⟨2,σ,?_⟩
    intro a b
    refine ⟨wittMatrix (evenChartVector (-1) (-1) (-1) (-a) (2*a + b)),hc _ _,?_⟩
    change entryPermute σ _=canonicalHollowPlane _ a b
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,σ,canonicalHollowPlane,wittMatrix,evenChartVector,
        hollowMatrix,starMatrix,nonstarPlane1,nonstarPlane2] <;> ring
  · rcases h with ⟨rfl,rfl,rfl⟩
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![1,0,3,2] (by decide)
    refine ⟨2,σ,?_⟩
    intro a b
    refine ⟨wittMatrix (evenChartVector (-1) (-1) (1) (2*a + b) (-a)),hc _ _,?_⟩
    change entryPermute σ _=canonicalHollowPlane _ a b
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,σ,canonicalHollowPlane,wittMatrix,evenChartVector,
        hollowMatrix,starMatrix,nonstarPlane1,nonstarPlane2] <;> ring
  · rcases h with ⟨rfl,rfl,rfl⟩
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![2,0,1,3] (by decide)
    refine ⟨0,σ,?_⟩
    intro a b
    refine ⟨wittMatrix (evenChartVector (-1) (0) (-1) (-b) (a - b)),hc _ _,?_⟩
    change entryPermute σ _=canonicalHollowPlane _ a b
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,σ,canonicalHollowPlane,wittMatrix,evenChartVector,
        hollowMatrix,starMatrix,nonstarPlane1,nonstarPlane2] <;> ring
  · rcases h with ⟨rfl,rfl,rfl⟩
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![0,1,3,2] (by decide)
    refine ⟨2,σ,?_⟩
    intro a b
    refine ⟨wittMatrix (evenChartVector (-1) (1) (-3) (3*a + b) (a)),hc _ _,?_⟩
    change entryPermute σ _=canonicalHollowPlane _ a b
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,σ,canonicalHollowPlane,wittMatrix,evenChartVector,
        hollowMatrix,starMatrix,nonstarPlane1,nonstarPlane2] <;> ring
  · rcases h with ⟨rfl,rfl,rfl⟩
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![2,0,1,3] (by decide)
    refine ⟨2,σ,?_⟩
    intro a b
    refine ⟨wittMatrix (evenChartVector (-1) (1) (-1) (a - 2*b) (a - b)),hc _ _,?_⟩
    change entryPermute σ _=canonicalHollowPlane _ a b
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,σ,canonicalHollowPlane,wittMatrix,evenChartVector,
        hollowMatrix,starMatrix,nonstarPlane1,nonstarPlane2] <;> ring
  · rcases h with ⟨rfl,rfl,rfl⟩
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![0,1,3,2] (by decide)
    refine ⟨1,σ,?_⟩
    intro a b
    refine ⟨wittMatrix (evenChartVector (-2/3) (-1/3) (0) (a - b) (-2*a - b)),hc _ _,?_⟩
    change entryPermute σ _=canonicalHollowPlane _ a b
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,σ,canonicalHollowPlane,wittMatrix,evenChartVector,
        hollowMatrix,starMatrix,nonstarPlane1,nonstarPlane2] <;> ring
  · rcases h with ⟨rfl,rfl,rfl⟩
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![1,0,3,2] (by decide)
    refine ⟨1,σ,?_⟩
    intro a b
    refine ⟨wittMatrix (evenChartVector (-2/3) (0) (-1) (3*a) (2*a + b)),hc _ _,?_⟩
    change entryPermute σ _=canonicalHollowPlane _ a b
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,σ,canonicalHollowPlane,wittMatrix,evenChartVector,
        hollowMatrix,starMatrix,nonstarPlane1,nonstarPlane2] <;> ring
  · rcases h with ⟨rfl,rfl,rfl⟩
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![0,2,3,1] (by decide)
    refine ⟨1,σ,?_⟩
    intro a b
    refine ⟨wittMatrix (evenChartVector (-1/3) (-2/3) (0) (-2*a - b) (a - b)),hc _ _,?_⟩
    change entryPermute σ _=canonicalHollowPlane _ a b
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,σ,canonicalHollowPlane,wittMatrix,evenChartVector,
        hollowMatrix,starMatrix,nonstarPlane1,nonstarPlane2] <;> ring
  · rcases h with ⟨rfl,rfl,rfl⟩
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![3,0,2,1] (by decide)
    refine ⟨2,σ,?_⟩
    intro a b
    refine ⟨wittMatrix (evenChartVector (-1/3) (-1/3) (-1/3) (-3*a - 3*b) (-3*b)),hc _ _,?_⟩
    change entryPermute σ _=canonicalHollowPlane _ a b
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,σ,canonicalHollowPlane,wittMatrix,evenChartVector,
        hollowMatrix,starMatrix,nonstarPlane1,nonstarPlane2] <;> ring
  · rcases h with ⟨rfl,rfl,rfl⟩
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![3,0,1,2] (by decide)
    refine ⟨2,σ,?_⟩
    intro a b
    refine ⟨wittMatrix (evenChartVector (-1/3) (-1/3) (1/3) (-3*b) (-3*a - 3*b)),hc _ _,?_⟩
    change entryPermute σ _=canonicalHollowPlane _ a b
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,σ,canonicalHollowPlane,wittMatrix,evenChartVector,
        hollowMatrix,starMatrix,nonstarPlane1,nonstarPlane2] <;> ring
  · rcases h with ⟨rfl,rfl,rfl⟩
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![1,2,3,0] (by decide)
    refine ⟨1,σ,?_⟩
    intro a b
    refine ⟨wittMatrix (evenChartVector (-1/3) (0) (0) (-3*a) (-a + b)),hc _ _,?_⟩
    change entryPermute σ _=canonicalHollowPlane _ a b
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,σ,canonicalHollowPlane,wittMatrix,evenChartVector,
        hollowMatrix,starMatrix,nonstarPlane1,nonstarPlane2] <;> ring
  · rcases h with ⟨rfl,rfl,rfl⟩
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![1,0,2,3] (by decide)
    refine ⟨0,σ,?_⟩
    intro a b
    refine ⟨wittMatrix (evenChartVector (0) (-1) (1) (a - b) (-b)),hc _ _,?_⟩
    change entryPermute σ _=canonicalHollowPlane _ a b
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,σ,canonicalHollowPlane,wittMatrix,evenChartVector,
        hollowMatrix,starMatrix,nonstarPlane1,nonstarPlane2] <;> ring
  · rcases h with ⟨rfl,rfl,rfl⟩
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![2,0,3,1] (by decide)
    refine ⟨1,σ,?_⟩
    intro a b
    refine ⟨wittMatrix (evenChartVector (0) (-2/3) (1) (2*a + b) (3*a)),hc _ _,?_⟩
    change entryPermute σ _=canonicalHollowPlane _ a b
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,σ,canonicalHollowPlane,wittMatrix,evenChartVector,
        hollowMatrix,starMatrix,nonstarPlane1,nonstarPlane2] <;> ring
  · rcases h with ⟨rfl,rfl,rfl⟩
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![2,1,3,0] (by decide)
    refine ⟨1,σ,?_⟩
    intro a b
    refine ⟨wittMatrix (evenChartVector (0) (-1/3) (0) (-a + b) (-3*a)),hc _ _,?_⟩
    change entryPermute σ _=canonicalHollowPlane _ a b
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,σ,canonicalHollowPlane,wittMatrix,evenChartVector,
        hollowMatrix,starMatrix,nonstarPlane1,nonstarPlane2] <;> ring
  · rcases h with ⟨rfl,rfl,rfl⟩
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![0,1,2,3] (by decide)
    refine ⟨0,σ,?_⟩
    intro a b
    refine ⟨wittMatrix (evenChartVector (0) (0) (0) (a) (b)),hc _ _,?_⟩
    change entryPermute σ _=canonicalHollowPlane _ a b
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,σ,canonicalHollowPlane,wittMatrix,evenChartVector,
        hollowMatrix,starMatrix,nonstarPlane1,nonstarPlane2] <;> ring
  · rcases h with ⟨rfl,rfl,rfl⟩
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![1,0,2,3] (by decide)
    refine ⟨2,σ,?_⟩
    intro a b
    refine ⟨wittMatrix (evenChartVector (1) (-1) (1) (a - b) (a - 2*b)),hc _ _,?_⟩
    change entryPermute σ _=canonicalHollowPlane _ a b
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,σ,canonicalHollowPlane,wittMatrix,evenChartVector,
        hollowMatrix,starMatrix,nonstarPlane1,nonstarPlane2] <;> ring
  · rcases h with ⟨rfl,rfl,rfl⟩
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![0,1,2,3] (by decide)
    refine ⟨2,σ,?_⟩
    intro a b
    refine ⟨wittMatrix (evenChartVector (1) (-1) (3) (b) (-a + 2*b)),hc _ _,?_⟩
    change entryPermute σ _=canonicalHollowPlane _ a b
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,σ,canonicalHollowPlane,wittMatrix,evenChartVector,
        hollowMatrix,starMatrix,nonstarPlane1,nonstarPlane2] <;> ring

lemma containing_even_chart_finrank_le_two
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (A B K : ℂ)
    (hr : ogrEvenRoots A B K)
    (hc : ∀ s t : ℂ, wittMatrix (evenChartVector A B K s t) ∈ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    Module.finrank ℂ L ≤ 2 := by
  obtain ⟨k,σ,hk⟩ := even_chart_contains_permuted_canonical L A B K hr hc
  have hd := containing_canonical_hollow_plane_finrank_le_two (entryPermuteSubmodule σ L) k hk
    (entryPermuteSubmodule_symmetric σ L hs) (entryPermuteSubmodule_permanent σ L hp)
  simpa only [entryPermuteSubmodule_finrank] using hd

lemma hollow_witt_image_reconstructs
    (H : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hs : ∀ V ∈ H, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hz : ∀ V ∈ H, ∀ i : Fin 4, V (i,i)=0)
    (hS : ∀ V ∈ H, V (0,1)+V (0,2)+V (0,3)+V (1,2)+V (1,3)+V (2,3)=0) :
    ∀ u ∈ H.map hollowWittCoordinates, wittMatrix u ∈ H := by
  rintro u ⟨V,hV,rfl⟩
  rw [wittMatrix_hollowWittCoordinates V (hs _ hV) (hz _ hV) (hS _ hV)]
  exact hV

lemma valid_flat_containing_hollow_two_plane
    (L H : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (hHL : H ≤ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24)
    (hz : ∀ V ∈ H, ∀ i : Fin 4, V (i,i)=0) (hd : 2 ≤ Module.finrank ℂ H) :
    Module.finrank ℂ L ≤ 2 := by
  have hsH : ∀ V ∈ H, ∀ i j : Fin 4, V (i,j)=V (j,i) := fun V hV => hs V (hHL hV)
  have hpH : ∀ V ∈ H, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24 := fun V hV => hp V (hHL hV)
  have hS : ∀ V ∈ H, V (0,1)+V (0,2)+V (0,3)+V (1,2)+V (1,3)+V (2,3)=0 :=
    fun V hV => (hollow_member_constraints H hsH hz hpH V hV).1
  let W := H.map hollowWittCoordinates
  obtain ⟨hqW,hcW⟩ := hollow_witt_image_constraints H hsH hz hpH
  have hdW : 2 ≤ Module.finrank ℂ W := by
    dsimp [W]
    rw [hollow_witt_image_finrank H hsH hz hS]
    exact hd
  obtain ⟨u,hu,v,hv,k,hk⟩ := witt_submodule_has_triangle_chart W hqW hdW
  let σ := triangleCoordinatePerm k
  let L' := entryPermuteSubmodule σ L
  let H' := entryPermuteSubmodule σ H
  have hHL' : H' ≤ L' := Submodule.map_mono hHL
  have hsH' := entryPermuteSubmodule_symmetric σ H hsH
  have hzH' := entryPermuteSubmodule_hollow σ H hz
  have hpH' := entryPermuteSubmodule_permanent σ H hpH
  have hS' : ∀ V ∈ H', V (0,1)+V (0,2)+V (0,3)+V (1,2)+V (1,3)+V (2,3)=0 :=
    fun V hV => (hollow_member_constraints H' hsH' hzH' hpH' V hV).1
  let W' := H'.map hollowWittCoordinates
  let U := entryPermute σ (wittMatrix u)
  let V := entryPermute σ (wittMatrix v)
  let u' := hollowWittCoordinates U
  let v' := hollowWittCoordinates V
  have hU : U ∈ H' := (entryPermute_mem_iff σ H _).mpr
    (hollow_witt_image_reconstructs H hsH hz hS u hu)
  have hV : V ∈ H' := (entryPermute_mem_iff σ H _).mpr
    (hollow_witt_image_reconstructs H hsH hz hS v hv)
  have hu' : u' ∈ W' := ⟨U,hU,rfl⟩
  have hv' : v' ∈ W' := ⟨V,hV,rfl⟩
  let F : (Fin 5 → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => x 0
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let G : (Fin 5 → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => x 1
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hdet : F u'*G v'-F v'*G u' ≠ 0 := by
    change leadingTriangleMinor (entryPermute σ (wittMatrix u))
      (entryPermute σ (wittMatrix v)) ≠ 0
    have heq := leadingTriangleMinor_permute_witt u v k
    change leadingTriangleMinor (entryPermute σ (wittMatrix u))
      (entryPermute σ (wittMatrix v))=wittTriangleMinor u v k at heq
    rw [heq]
    exact hk
  obtain ⟨a,ha,b,hb,ha0,ha1,hb0,hb1⟩ :=
    normalize_two_linear_coordinates W' F G u' v' hu' hv' hdet
  change a 0=1 at ha0
  change a 1=0 at ha1
  change b 0=0 at hb0
  change b 1=1 at hb1
  obtain ⟨hqW',hcW'⟩ := hollow_witt_image_constraints H' hsH' hzH' hpH'
  obtain ⟨A,B,K,hr,hA,hB⟩ := isotropic_normalized_pair_classified W' hqW' hcW'
    a b ha hb ha0 ha1 hb0 hb1
  have hchart : ∀ s t : ℂ, wittMatrix (evenChartVector A B K s t) ∈ L' := by
    intro s t
    apply hHL'
    apply hollow_witt_image_reconstructs H' hsH' hzH' hS'
    rw [evenChartVector_linear_combination,← hA,← hB]
    exact W'.add_mem (W'.smul_mem s ha) (W'.smul_mem t hb)
  have hdim := containing_even_chart_finrank_le_two L' A B K hr hchart
    (entryPermuteSubmodule_symmetric σ L hs) (entryPermuteSubmodule_permanent σ L hp)
  simpa only [L',entryPermuteSubmodule_finrank] using hdim

def matrixDiagonalCoordinates : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun V i := V (i,i)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

lemma valid_flat_diagonal_rank_le_one
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24)
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates) ≤ 1) :
    Module.finrank ℂ L ≤ 2 := by
  let F := matrixDiagonalCoordinates.domRestrict L
  let H := (LinearMap.ker F).map L.subtype
  have hHL : H ≤ L := by
    rintro V ⟨v,hv,rfl⟩
    exact v.property
  have hz : ∀ V ∈ H, ∀ i : Fin 4, V (i,i)=0 := by
    rintro V ⟨v,hv,rfl⟩ i
    have he : F v=0 := hv
    exact congrFun he i
  by_cases hdim : 2 ≤ Module.finrank ℂ H
  · exact valid_flat_containing_hollow_two_plane L H hHL hs hp hz hdim
  · have hk : Module.finrank ℂ (LinearMap.ker F) ≤ 1 := by
      dsimp [H] at hdim
      rw [Submodule.finrank_map_subtype_eq] at hdim
      omega
    have hr : Module.finrank ℂ (LinearMap.range F) ≤ 1 := by
      change Module.finrank ℂ (LinearMap.range (matrixDiagonalCoordinates.domRestrict L)) ≤ 1
      rw [LinearMap.range_domRestrict]
      exact hd
    have htotal := F.finrank_range_add_finrank_ker
    omega

def duplicateRowPolynomial (a b c d e f : ℂ) : ℂ :=
  2*a^2*(d*f+e^2)+8*a*b*c*e+4*a*(b^2*f+c^2*d)+4*b^2*c^2

def duplicateRowMatrix (a b c d e f : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![a,a,b,c; a,a,b,c; b,b,d,e; c,c,e,f]

def duplicateRowMap : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun v p := duplicateRowMatrix (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) p.1 p.2
  map_add' v w := by
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> rfl
  map_smul' z v := by
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> rfl

lemma duplicateRowMap_injective : Function.Injective duplicateRowMap := by
  intro v w h
  have h00 := congrArg (fun V => V (0,0)) h
  have h02 := congrArg (fun V => V (0,2)) h
  have h03 := congrArg (fun V => V (0,3)) h
  have h22 := congrArg (fun V => V (2,2)) h
  have h23 := congrArg (fun V => V (2,3)) h
  have h33 := congrArg (fun V => V (3,3)) h
  funext i
  fin_cases i
  · exact h00
  · exact h02
  · exact h03
  · exact h22
  · exact h23
  · exact h33

lemma permanent_duplicateRow (a b c d e f : ℂ) :
    Matrix.permanent (duplicateRowMatrix a b c d e f) =
      duplicateRowPolynomial a b c d e f := by
  rw [permanent_four]
  simp [duplicateRowMatrix, duplicateRowPolynomial]
  ring

lemma permanent_duplicateRowMap (v : Fin 6 → ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (1 : ℂ) + duplicateRowMap v (i,j)) =
      duplicateRowPolynomial (1+v 0) (1+v 1) (1+v 2)
        (1+v 3) (1+v 4) (1+v 5) := by
  rw [permanent_four]
  simp [duplicateRowMap, duplicateRowMatrix, duplicateRowPolynomial]
  ring

lemma quartic_all_coefficients (a b c d : ℂ)
    (h : ∀ z : ℂ, a*z+b*z^2+c*z^3+d*z^4 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  obtain ⟨ha,hb⟩ := quartic_first_coefficients a b c d h
  have h1 := h 1
  have hn := h (-1)
  refine ⟨ha,hb,?_,?_⟩
  · linear_combination (1/2:ℂ)*h1-(1/2:ℂ)*hn-ha
  · linear_combination (1/2:ℂ)*h1+(1/2:ℂ)*hn-hb

set_option maxHeartbeats 1600000 in
lemma duplicate_normalized_pair_impossible (B C D E F r : ℂ) (hr : r^2 = 2)
    (hp : ∀ z h : ℂ, duplicateRowPolynomial (1+z) (1+B*z) (1+C*z)
      (1+D*z+(r-1)*h) (1+E*z+h) (1+F*z+(-r-1)*h) = 24) : False := by
  let q1 := 6*(4*B+4*C+D+2*E+F+4)
  let q2 := 2*(4*B^2+12*B*C+4*B*E+4*B*F+8*B+4*C^2+4*C*D+
    4*C*E+8*C+D*F+4*D+E^2+8*E+4*F+2)
  let q3 := 2*(4*B^2*C+2*B^2*F+2*B^2+4*B*C^2+4*B*C*E+4*B*C+
    4*B*E+4*B*F+2*C^2*D+2*C^2+4*C*D+4*C*E+2*D*F+D+2*E^2+2*E+F)
  have hz : ∀ z : ℂ, q1*z+q2*z^2+q3*z^3+
      duplicateRowPolynomial 1 B C D E F*z^4 = 0 := by
    intro z
    have h := hp z 0
    dsimp [q1,q2,q3,duplicateRowPolynomial] at *
    linear_combination h
  obtain ⟨h1,h2,h3,_⟩ := quartic_all_coefficients _ _ _ _ hz
  let l1 := -2*(4*B*r-4*C*r+D*r+D-2*E-F*r+F)
  let l2 := -4*(B^2*r+B^2-2*B*C+2*B*r-C^2*r+C^2-2*C*r+
    D*r+D-2*E-F*r+F)
  let l3 := -2*(2*B^2*r+2*B^2-4*B*C-2*C^2*r+2*C^2+D*r+D-2*E-F*r+F)
  have hl : ∀ z : ℂ, l1*z+l2*z^2+l3*z^3+0*z^4 = 0 := by
    intro z
    have hp1 := hp z 1
    have hpn := hp z (-1)
    dsimp [l1,l2,l3,duplicateRowPolynomial] at *
    linear_combination (1/2:ℂ)*hp1-(1/2:ℂ)*hpn
  obtain ⟨hl1,hl2,_⟩ := quartic_all_coefficients _ _ _ _ hl
  dsimp [q1,q2,q3] at h1 h2 h3
  dsimp [l1,l2] at hl1 hl2
  have hd : D = r-2+(r-4)*B+r*C+(r-1)*E := by
    linear_combination (2-r)/24*h1-r/8*hl1-(4*B-4*C+D-F)/4*hr
  have hf : F = -2-r-r*B-(4+r)*C-(r+1)*E := by
    linear_combination (2+r)/24*h1+r/8*hl1+(4*B-4*C+D-F)/4*hr
  subst D
  subst F
  have hsplit : (B-C)*((r+1)*B+(r-1)*C-2*r) = 0 := by
    linear_combination -(1/4:ℂ)*hl2-2*(B+C+E+1)*hr
  rcases mul_eq_zero.mp hsplit with heq | hother
  · have hCB : C = B := by linear_combination -heq
    subst C
    have hQ : B^2+6*B+3 = 0 := by
      linear_combination -(1/8:ℂ)*h2-(1/4:ℂ)*(2*B+E+1)^2*hr
    have hC : B*(B+1)^2 = 0 := by
      linear_combination -(1/16:ℂ)*h3-(1/4:ℂ)*(2*B+E+1)^2*hr
    have hbad : (6:ℂ) = 0 := by
      linear_combination (11*B^2+16*B+2)*hQ-(11*B+60)*hC
    norm_num at hbad
  · have hCB : C = 4+2*r-(3+2*r)*B := by
      linear_combination (r+1)*hother-(B+C-2)*hr
    subst C
    let Q := 5*B^2+(-18+8*r)*B-17+12*r
    let T := (B-r)*(5*B^2+(-14+4*r)*B-3+4*r)
    let X := 4*B^2*r^2+8*B^2*r-4*B^2-4*B*E*r-4*B*E-8*B*r^2-
      28*B*r+60*B+E^2+4*E*r+10*E+4*r^2+20*r+113
    let Y := 8*B^3*r^2+32*B^3*r+64*B^3-4*B^2*E*r-8*B^2*E-
      20*B^2*r^2-100*B^2*r-184*B^2+4*B*E*r+12*B*E+16*B*r^2+
      172*B*r-44*B+E^2+2*E-4*r^2+56*r-3
    have hQraw : (16*r+24)*Q = 0 := by
      dsimp [Q,X]
      linear_combination h2+2*X*hr
    have hTraw : (-80*r-112)*T = 0 := by
      dsimp [T,Y]
      linear_combination h3+4*Y*hr
    have hQ : Q = 0 := by
      linear_combination (3-2*r)/8*hQraw+4*Q*hr
    have hT : T = 0 := by
      linear_combination -(5*r-7)/16*hTraw-25*T*hr
    have hbad : (318:ℂ) = 0 := by
      dsimp [Q,T] at hQ hT
      linear_combination
        ((3485+2460*r)*B^2-(6032+4250*r)*B+1848+1324*r)*hQ-
        ((3485+2460*r)*B+36+55*r)*hT-
        (22140*B^3+9840*B^2*r-34765*B^2+10060*B*r-34694*B+220*r+15867)*hr
    norm_num at hbad

set_option maxHeartbeats 800000 in
lemma duplicate_normalized_first_kernel_zero (v w : Fin 6 → ℂ)
    (hv0 : v 0 = 1) (hw0 : w 0 = 0)
    (hp : ∀ z h : ℂ, duplicateRowPolynomial
      (1+z*v 0+h*w 0) (1+z*v 1+h*w 1) (1+z*v 2+h*w 2)
      (1+z*v 3+h*w 3) (1+z*v 4+h*w 4) (1+z*v 5+h*w 5) = 24) :
    w = 0 := by
  have hw1 : w 1 = 0 := by
    by_contra hne
    have h := hp (-1) ((v 1-1)/w 1)
    have hzero : 1+(-1)*v 1+((v 1-1)/w 1)*w 1 = 0 := by
      field_simp
      ring
    rw [hzero] at h
    norm_num [hv0,hw0,duplicateRowPolynomial] at h
  have hw2 : w 2 = 0 := by
    by_contra hne
    have h := hp (-1) ((v 2-1)/w 2)
    have hzero : 1+(-1)*v 2+((v 2-1)/w 2)*w 2 = 0 := by
      field_simp
      ring
    rw [hzero] at h
    norm_num [hv0,hw0,duplicateRowPolynomial] at h
  have h1 := hp 0 1
  have hn := hp 0 (-1)
  simp only [zero_mul,add_zero,hw0,hw1,hw2,mul_zero] at h1 hn
  dsimp [duplicateRowPolynomial] at h1 hn
  have hlin : w 3+2*w 4+w 5 = 0 := by
    linear_combination h1/12-hn/12
  have hquad : w 3*w 5+(w 4)^2 = 0 := by
    linear_combination h1/4+hn/4
  by_cases hw4 : w 4 = 0
  · have hsq : (w 3)^2 = 0 := by
      linear_combination w 3*hlin-hquad+(w 4-2*w 3)*hw4
    have hw3 : w 3 = 0 := eq_zero_of_pow_eq_zero hsq
    have hw5 : w 5 = 0 := by linear_combination hlin-hw3-2*hw4
    funext i
    fin_cases i <;> simp [hw0,hw1,hw2,hw3,hw4,hw5]
  · let r := w 3/w 4+1
    have hr : r^2 = 2 := by
      dsimp [r]
      field_simp
      linear_combination w 3*hlin-hquad
    have hratio : w 5/w 4 = -r-1 := by
      dsimp [r]
      field_simp
      linear_combination hlin
    exfalso
    apply duplicate_normalized_pair_impossible (v 1) (v 2) (v 3) (v 4) (v 5) r hr
    intro z h
    have hh := hp z (h/w 4)
    simp only [hv0,hw0,hw1,hw2,mul_one,mul_zero,add_zero] at hh
    have hd : h/w 4*w 3 = (r-1)*h := by dsimp [r]; ring
    have he : h/w 4*w 4 = h := by field_simp
    have hf : h/w 4*w 5 = (-r-1)*h := by
      rw [← hratio]
      ring
    rw [hd,he,hf] at hh
    simpa only [mul_comm] using hh

lemma coordinate_product_zero_split (W : Submodule ℂ (Fin 6 → ℂ)) (i j : Fin 6)
    (h : ∀ v ∈ W, v i * v j = 0) :
    (∀ v ∈ W, v i = 0) ∨ (∀ v ∈ W, v j = 0) := by
  classical
  by_cases hi : ∀ v ∈ W, v i = 0
  · exact Or.inl hi
  · push Not at hi
    obtain ⟨u, hu, hui⟩ := hi
    have huj := (mul_eq_zero.mp (h u hu)).resolve_left hui
    right
    intro v hv
    by_cases hvi : v i = 0
    · have huv := h (u + v) (W.add_mem hu hv)
      simp only [Pi.add_apply, hvi, huj, add_zero, zero_add] at huv
      exact (mul_eq_zero.mp huv).resolve_left hui
    · exact (mul_eq_zero.mp (h v hv)).resolve_left hvi

lemma finrank_le_one_of_coordinate_kernel (W : Submodule ℂ (Fin 6 → ℂ)) (i : Fin 6)
    (hk : ∀ v ∈ W, v i = 0 → v = 0) : Module.finrank ℂ W ≤ 1 := by
  let F : W →ₗ[ℂ] ℂ :=
    { toFun := fun v => v.val i
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hker : ∀ v : W, F v = 0 → v = 0 := by
    intro v hv
    apply Subtype.ext
    exact hk v.val v.property hv
  have hF : Function.Injective F := by
    intro v w h
    apply sub_eq_zero.mp
    apply hker (v - w)
    rw [map_sub, h, sub_self]
  have hd := Submodule.finrank_le (LinearMap.range F)
  rw [LinearMap.finrank_range_of_inj hF] at hd
  simpa using hd

lemma duplicate_constant_quartic (b c d e f : ℂ)
    (hp : ∀ z : ℂ, duplicateRowPolynomial 1 (1+z*b) (1+z*c)
      (1+z*d) (1+z*e) (1+z*f) = 24) : b*c = 0 := by
  have h1 := hp 1
  have hm1 := hp (-1)
  have h2 := hp 2
  have hm2 := hp (-2)
  dsimp [duplicateRowPolynomial] at h1 hm1 h2 hm2
  have hsq : (b*c)^2 = 0 := by
    linear_combination h2/96 + hm2/96 - h1/24 - hm1/24
  by_contra hne
  exact (mul_ne_zero hne hne) (by simpa only [pow_two] using hsq)

lemma duplicate_constant_left_cubic (c d e f : ℂ)
    (hp : ∀ z : ℂ, duplicateRowPolynomial 1 1 (1+z*c)
      (1+z*d) (1+z*e) (1+z*f) = 24) : c*d = 0 := by
  have h1 := hp 1
  have hm1 := hp (-1)
  have h2 := hp 2
  have hm2 := hp (-2)
  dsimp [duplicateRowPolynomial] at h1 hm1 h2 hm2
  have hcube : c^2*d = 0 := by
    linear_combination h2/48 - hm2/48 - h1/24 + hm1/24
  rcases mul_eq_zero.mp hcube with hc | hd
  · have hc0 : c = 0 := by
      by_contra hne
      exact (mul_ne_zero hne hne) (by simpa only [pow_two] using hc)
    simp [hc0]
  · simp [hd]

lemma duplicate_constant_right_cubic (b d e f : ℂ)
    (hp : ∀ z : ℂ, duplicateRowPolynomial 1 (1+z*b) 1
      (1+z*d) (1+z*e) (1+z*f) = 24) : b*f = 0 := by
  apply duplicate_constant_left_cubic b f e d
  intro z
  have hz := hp z
  dsimp [duplicateRowPolynomial] at hz ⊢
  linear_combination hz

lemma duplicate_constant_block_finrank_le_one
    (W : Submodule ℂ (Fin 6 → ℂ))
    (hp : ∀ v ∈ W, duplicateRowPolynomial (1+v 0) (1+v 1) (1+v 2)
      (1+v 3) (1+v 4) (1+v 5) = 24)
    (ha : ∀ v ∈ W, v 0 = 0) : Module.finrank ℂ W ≤ 1 := by
  have hs (v : Fin 6 → ℂ) (hv : v ∈ W) (z : ℂ) :
      duplicateRowPolynomial 1 (1+z*v 1) (1+z*v 2)
        (1+z*v 3) (1+z*v 4) (1+z*v 5) = 24 := by
    have hz := hp (z • v) (W.smul_mem z hv)
    simpa only [Pi.smul_apply, smul_eq_mul, ha v hv, mul_zero, add_zero] using hz
  have hbc : (∀ v ∈ W, v 1 = 0) ∨ (∀ v ∈ W, v 2 = 0) := by
    apply coordinate_product_zero_split W 1 2
    intro v hv
    exact duplicate_constant_quartic _ _ _ _ _ (hs v hv)
  have hboth (hb : ∀ v ∈ W, v 1 = 0) (hc : ∀ v ∈ W, v 2 = 0) :
      Module.finrank ℂ W ≤ 1 := by
    apply finrank_le_one_of_coordinate_kernel W 4
    intro v hv he
    have h1 := hs v hv 1
    have hm1 := hs v hv (-1)
    simp only [hb v hv, hc v hv, he, mul_zero, add_zero] at h1 hm1
    dsimp [duplicateRowPolynomial] at h1 hm1
    have hlin : v 3 + v 5 = 0 := by linear_combination h1/12 - hm1/12
    have hquad : v 3 * v 5 = 0 := by linear_combination h1/4 + hm1/4
    have hd : v 3 = 0 := by
      have hsq : (v 3)^2 = 0 := by linear_combination v 3*hlin - hquad
      by_contra hne
      exact (mul_ne_zero hne hne) (by simpa only [pow_two] using hsq)
    have hf : v 5 = 0 := by linear_combination hlin - hd
    funext i
    fin_cases i <;> simp [ha v hv, hb v hv, hc v hv, hd, he, hf]
  have hleft (hb : ∀ v ∈ W, v 1 = 0) (hd : ∀ v ∈ W, v 3 = 0) :
      Module.finrank ℂ W ≤ 1 := by
    apply finrank_le_one_of_coordinate_kernel W 2
    intro v hv hc
    have h1 := hs v hv 1
    have hm1 := hs v hv (-1)
    simp only [hb v hv, hd v hv, hc, mul_zero, add_zero] at h1 hm1
    dsimp [duplicateRowPolynomial] at h1 hm1
    have he : v 4 = 0 := by
      have hsq : (v 4)^2 = 0 := by linear_combination h1/4 + hm1/4
      by_contra hne
      exact (mul_ne_zero hne hne) (by simpa only [pow_two] using hsq)
    have hf : v 5 = 0 := by linear_combination h1/12 - hm1/12 - 2*he
    funext i
    fin_cases i <;> simp [ha v hv, hb v hv, hc, hd v hv, he, hf]
  have hright (hc : ∀ v ∈ W, v 2 = 0) (hf : ∀ v ∈ W, v 5 = 0) :
      Module.finrank ℂ W ≤ 1 := by
    apply finrank_le_one_of_coordinate_kernel W 1
    intro v hv hb
    have h1 := hs v hv 1
    have hm1 := hs v hv (-1)
    simp only [hc v hv, hf v hv, hb, mul_zero, add_zero] at h1 hm1
    dsimp [duplicateRowPolynomial] at h1 hm1
    have he : v 4 = 0 := by
      have hsq : (v 4)^2 = 0 := by linear_combination h1/4 + hm1/4
      by_contra hne
      exact (mul_ne_zero hne hne) (by simpa only [pow_two] using hsq)
    have hd : v 3 = 0 := by linear_combination h1/12 - hm1/12 - 2*he
    funext i
    fin_cases i <;> simp [ha v hv, hb, hc v hv, hd, he, hf v hv]
  rcases hbc with hb | hc
  · have hcd : (∀ v ∈ W, v 2 = 0) ∨ (∀ v ∈ W, v 3 = 0) := by
      apply coordinate_product_zero_split W 2 3
      intro v hv
      apply duplicate_constant_left_cubic (v 2) (v 3) (v 4) (v 5)
      intro z
      simpa only [hb v hv, mul_zero, add_zero] using hs v hv z
    exact hcd.elim (hboth hb) (hleft hb)
  · have hbf : (∀ v ∈ W, v 1 = 0) ∨ (∀ v ∈ W, v 5 = 0) := by
      apply coordinate_product_zero_split W 1 5
      intro v hv
      apply duplicate_constant_right_cubic (v 1) (v 3) (v 4) (v 5)
      intro z
      simpa only [hc v hv, mul_zero, add_zero] using hs v hv z
    exact hbf.elim (fun hb => hboth hb hc) (hright hc)

lemma duplicate_row_flat_finrank_le_one
    (W : Submodule ℂ (Fin 6 → ℂ))
    (hp : ∀ v ∈ W, duplicateRowPolynomial (1+v 0) (1+v 1) (1+v 2)
      (1+v 3) (1+v 4) (1+v 5) = 24) : Module.finrank ℂ W ≤ 1 := by
  classical
  by_cases ha : ∀ v ∈ W, v 0 = 0
  · exact duplicate_constant_block_finrank_le_one W hp ha
  · push Not at ha
    obtain ⟨v,hv,hv0⟩ := ha
    let v' := (v 0)⁻¹ • v
    have hv' : v' ∈ W := W.smul_mem _ hv
    have hv'0 : v' 0 = 1 := by simp [v',hv0]
    apply finrank_le_one_of_coordinate_kernel W 0
    intro w hw hw0
    apply duplicate_normalized_first_kernel_zero v' w hv'0 hw0
    intro z h
    have hm := W.add_mem (W.smul_mem z hv') (W.smul_mem h hw)
    have hz := hp (z • v' + h • w) hm
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_assoc] using hz

lemma basic_star_row_relations (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ a z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + starMatrix a (-a) (i,j) +
        z * V (i,j)) = 24) :
    V (1,1) = V (2,2) ∧ V (1,1) = V (1,2) ∧ V (1,3) = V (2,3) := by
  have hp' : ∀ a z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + starMatrix a ((-1)*a) (i,j) +
        z * V (i,j)) = 24 := by simpa using hp
  rcases star_line_constraints (-1) V hs hp' with ⟨h1,h2,hq⟩
  have hsq : (V (1,3) - V (2,3))^2 = 0 := by
    unfold starLineQuad at hq
    linear_combination hq - V (3,3) * h2
  have h13 : V (1,3) = V (2,3) := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsq)
  have h11 : V (1,1) = V (2,2) := by linear_combination h1 - h13
  have h12 : V (1,1) = V (1,2) := by linear_combination (h2 + h11) / 2
  exact ⟨h11,h12,h13⟩

noncomputable def basicStarCoordinates : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) where
  toFun V := ![V (1,1),(V (0,1)+V (0,2))/2,V (1,3),V (0,0),V (0,3),V (3,3)]
  map_add' := by intros; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intros; ext i; fin_cases i <;> simp <;> ring

noncomputable def basicStarPermutation : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective ![1,2,0,3] (by decide)

lemma basic_star_projection_reconstruction (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (h11 : V (1,1)=V (2,2)) (h12 : V (1,1)=V (1,2))
    (h13 : V (1,3)=V (2,3)) :
    duplicateRowMap (basicStarCoordinates V) = entryPermute basicStarPermutation
      (V - ((V (0,1)-V (0,2))/2) • starMatrix 1 (-1)) := by
  have h10 := hs 1 0
  have h20 := hs 2 0
  have h30 := hs 3 0
  have h21 := hs 2 1
  have h31 := hs 3 1
  have h32 := hs 3 2
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [duplicateRowMap,duplicateRowMatrix,basicStarCoordinates,entryPermute,
      basicStarPermutation,starMatrix,h10,h20,h30,h21,h31,h32,
      ← h11,← h12,← h13] <;> ring

lemma basic_star_coordinates_kernel (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (h11 : V (1,1)=V (2,2)) (h12 : V (1,1)=V (1,2))
    (h13 : V (1,3)=V (2,3))
    (hF : basicStarCoordinates V=0) (h01 : V (0,1)=0) : V=0 := by
  have h₀ : V (1,1)=0 := by simpa [basicStarCoordinates] using congrFun hF 0
  have h₁ : (V (0,1)+V (0,2))/2=0 := by
    simpa [basicStarCoordinates] using congrFun hF 1
  have h₂ : V (1,3)=0 := by simpa [basicStarCoordinates] using congrFun hF 2
  have h₃ : V (0,0)=0 := by simpa [basicStarCoordinates] using congrFun hF 3
  have h₄ : V (0,3)=0 := by simpa [basicStarCoordinates] using congrFun hF 4
  have h₅ : V (3,3)=0 := by simpa [basicStarCoordinates] using congrFun hF 5
  have h02 : V (0,2)=0 := by linear_combination 2*h₁-h01
  have h10 := hs 1 0
  have h20 := hs 2 0
  have h30 := hs 3 0
  have h21 := hs 2 1
  have h31 := hs 3 1
  have h32 := hs 3 2
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [h10,h20,h30,h21,h31,h32,← h11,← h12,← h13,
      h₀,h₂,h₃,h₄,h₅,h01,h02]

lemma containing_basic_star_line_finrank_le_two
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (hA : starMatrix 1 (-1) ∈ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    Module.finrank ℂ L ≤ 2 := by
  have hrows (V : Fin 4 × Fin 4 → ℂ) (hV : V ∈ L) :
      V (1,1)=V (2,2) ∧ V (1,1)=V (1,2) ∧ V (1,3)=V (2,3) := by
    apply basic_star_row_relations V (hs V hV)
    intro a z
    simpa using star_line_closed_family L (-1) hA hp V hV a z
  have himage : ∀ v ∈ L.map basicStarCoordinates,
      duplicateRowPolynomial (1+v 0) (1+v 1) (1+v 2)
        (1+v 3) (1+v 4) (1+v 5)=24 := by
    rintro v ⟨V,hV,rfl⟩
    obtain ⟨h11,h12,h13⟩ := hrows V hV
    rw [← permanent_duplicateRowMap,
      basic_star_projection_reconstruction V (hs V hV) h11 h12 h13]
    apply (entryPermute_permanent basicStarPermutation _).trans
    exact hp _ (L.sub_mem hV (L.smul_mem _ hA))
  let F := basicStarCoordinates.domRestrict L
  have hrange : Module.finrank ℂ (LinearMap.range F) ≤ 1 := by
    change Module.finrank ℂ (LinearMap.range (basicStarCoordinates.domRestrict L)) ≤ 1
    rw [LinearMap.range_domRestrict]
    exact duplicate_row_flat_finrank_le_one _ himage
  let G : LinearMap.ker F →ₗ[ℂ] ℂ :=
    { toFun := fun V => V.val.val (0,1)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hGker : ∀ V : LinearMap.ker F, G V=0 → V=0 := by
    intro V hV
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨h11,h12,h13⟩ := hrows V.val.val V.val.property
    exact basic_star_coordinates_kernel V.val.val (hs _ V.val.property)
      h11 h12 h13 V.property hV
  have hG : Function.Injective G := by
    intro V W h
    apply sub_eq_zero.mp
    apply hGker (V-W)
    change G V-G W=0
    exact sub_eq_zero.mpr h
  have hkernel : Module.finrank ℂ (LinearMap.ker F) ≤ 1 := by
    have hd := Submodule.finrank_le (LinearMap.range G)
    rw [LinearMap.finrank_range_of_inj hG] at hd
    simpa using hd
  have htotal := F.finrank_range_add_finrank_ker
  omega

lemma starMatrix_smul (z a b : ℂ) :
    z • starMatrix a b = starMatrix (z*a) (z*b) := by
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> simp [starMatrix] <;> ring

lemma entryPermute_star_swap12 (a b : ℂ) :
    entryPermute (Equiv.swap (1 : Fin 4) 2) (starMatrix a b) =
      starMatrix b a := by
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [entryPermute,Equiv.swap_apply_def,starMatrix] <;> ring

lemma entryPermute_star_swap23 (a b : ℂ) :
    entryPermute (Equiv.swap (2 : Fin 4) 3) (starMatrix a b) =
      starMatrix a (-a-b) := by
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [entryPermute,Equiv.swap_apply_def,starMatrix] <;> ring

lemma containing_normalized_star_line_finrank_le_two
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (t : ℂ)
    (hA : starMatrix 1 t ∈ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    Module.finrank ℂ L ≤ 2 := by
  let σ := Equiv.swap (2 : Fin 4) 3
  have hA' : starMatrix 1 (-1-t) ∈ entryPermuteSubmodule σ L := by
    have hm := (entryPermute_mem_iff σ L (starMatrix 1 t)).mpr hA
    simpa only [σ,entryPermute_star_swap23] using hm
  have hs' := entryPermuteSubmodule_symmetric σ L hs
  have hp' := entryPermuteSubmodule_permanent σ L hp
  by_cases ht0 : t = 0
  · subst t
    have hbound := containing_basic_star_line_finrank_le_two
      (entryPermuteSubmodule σ L) (by simpa using hA') hs' hp'
    simpa only [entryPermuteSubmodule_finrank] using hbound
  by_cases ht1 : t = -1
  · subst t
    exact containing_basic_star_line_finrank_le_two L hA hs hp
  by_cases ht2 : t = -2
  · subst t
    have hbound := containing_generic_star_line_finrank_le_two
      (entryPermuteSubmodule σ L) 1 (by norm_num) (by norm_num) (by norm_num)
      (by convert hA' using 1 <;> norm_num) hs' hp'
    simpa only [entryPermuteSubmodule_finrank] using hbound
  · apply containing_generic_star_line_finrank_le_two L t ht0 _ _ hA hs hp
    · intro h
      exact ht1 (by linear_combination h)
    · intro h
      exact ht2 (by linear_combination h)

lemma containing_nonzero_star_line_finrank_le_two
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (a b : ℂ)
    (hab : a ≠ 0 ∨ b ≠ 0) (hA : starMatrix a b ∈ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    Module.finrank ℂ L ≤ 2 := by
  by_cases ha : a = 0
  · subst a
    have hb : b ≠ 0 := hab.resolve_left (by simp)
    let σ := Equiv.swap (1 : Fin 4) 2
    have hm : starMatrix b 0 ∈ entryPermuteSubmodule σ L := by
      have hm := (entryPermute_mem_iff σ L (starMatrix 0 b)).mpr hA
      simpa only [σ,entryPermute_star_swap12] using hm
    have hnorm : starMatrix 1 0 ∈ entryPermuteSubmodule σ L := by
      have hm' := (entryPermuteSubmodule σ L).smul_mem b⁻¹ hm
      simpa [starMatrix_smul,hb] using hm'
    have hbound := containing_normalized_star_line_finrank_le_two
      (entryPermuteSubmodule σ L) 0 hnorm
      (entryPermuteSubmodule_symmetric σ L hs)
      (entryPermuteSubmodule_permanent σ L hp)
    simpa only [entryPermuteSubmodule_finrank] using hbound
  · have hnorm : starMatrix 1 (a⁻¹*b) ∈ L := by
      have hm := L.smul_mem a⁻¹ hA
      simpa [starMatrix_smul,ha] using hm
    exact containing_normalized_star_line_finrank_le_two L _ hnorm hs hp

lemma containing_nonzero_starMatrix_finrank_le_two
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (a b : ℂ)
    (hne : starMatrix a b ≠ 0) (hA : starMatrix a b ∈ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    Module.finrank ℂ L ≤ 2 := by
  apply containing_nonzero_star_line_finrank_le_two L a b _ hA hs hp
  by_contra h
  push Not at h
  apply hne
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> simp [starMatrix,h.1,h.2]

lemma incident_star_support (b c d e : ℂ)
    (hbd : b*d=0) (hce : c*e=0) (hR : b*e+c*d=0) :
    (d=0 ∧ e=0) ∨ (b=0 ∧ c=0) := by
  by_cases hb : b=0
  · by_cases hc : c=0
    · exact Or.inr ⟨hb,hc⟩
    · have he : e=0 := (mul_eq_zero.mp hce).resolve_left hc
      have hd : d=0 := (mul_eq_zero.mp (by simpa [hb] using hR)).resolve_left hc
      exact Or.inl ⟨hd,he⟩
  · have hd : d=0 := (mul_eq_zero.mp hbd).resolve_left hb
    have he : e=0 := (mul_eq_zero.mp (by simpa [hd] using hR)).resolve_left hb
    exact Or.inl ⟨hd,he⟩

lemma incident_hollow_is_permuted_star (b c d e f : ℂ)
    (hf : f=0) (hbd : b*d=0) (hce : c*e=0) (hR : b*e+c*d=0)
    (hS : 1+b+c+d+e+f=0) :
    ∃ (σ : Equiv.Perm (Fin 4)) (a t : ℂ), starMatrix a t ≠ 0 ∧
      entryPermute σ (fun p => hollowMatrix 1 b c d e f p.1 p.2)=starMatrix a t := by
  rcases incident_star_support b c d e hbd hce hR with ⟨hd,he⟩ | ⟨hb,hc⟩
  · have hc : c = -1-b := by linear_combination hS-hd-he-hf
    refine ⟨Equiv.refl _,1,b,?_,?_⟩
    · intro h
      have hh := congrFun h (0,1)
      norm_num [starMatrix] at hh
    · funext p
      rcases p with ⟨i,j⟩
      fin_cases i <;> fin_cases j <;>
        simp [entryPermute,hollowMatrix,starMatrix,hc,hd,he,hf]
  · have he : e = -1-d := by linear_combination hS-hb-hc-hf
    refine ⟨Equiv.swap 0 1,1,d,?_,?_⟩
    · intro h
      have hh := congrFun h (0,1)
      norm_num [starMatrix] at hh
    · funext p
      rcases p with ⟨i,j⟩
      fin_cases i <;> fin_cases j <;>
        simp [entryPermute,Equiv.swap_apply_def,hollowMatrix,starMatrix,hb,hc,he,hf]

set_option maxHeartbeats 800000 in
lemma diagonal_edge_normalizing_permutation (i j k : Fin 4) (hjk : j ≠ k) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0=i ∧
      ((σ 0=j ∧ σ 1=k) ∨ (σ 0=k ∧ σ 1=j) ∨
       (σ 1=j ∧ σ 2=k) ∨ (σ 1=k ∧ σ 2=j)) := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first | exact False.elim (hjk rfl) | decide

lemma normalize_hollow_tracezero_pair
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (H V : Fin 4 × Fin 4 → ℂ)
    (hH : H ∈ L) (hV : V ∈ L) (hHne : H ≠ 0)
    (hHz : ∀ i : Fin 4, H (i,i)=0)
    (hHs : ∀ i j : Fin 4, H (i,j)=H (j,i))
    (hVdiag : ∃ i : Fin 4, V (i,i) ≠ 0)
    (hVtrace : (∑ i : Fin 4, V (i,i))=0) :
    ∃ σ : Equiv.Perm (Fin 4),
      ∃ A ∈ entryPermuteSubmodule σ L, ∃ B ∈ entryPermuteSubmodule σ L,
      A ≠ 0 ∧ (∀ i : Fin 4, A (i,i)=0) ∧
      (∑ i : Fin 4, B (i,i))=0 ∧ B (0,0)=1 ∧
      ((A (0,1)=1 ∧ B (0,1)=0) ∨ (A (1,2)=1 ∧ B (1,2)=0)) := by
  obtain ⟨i,hi⟩ := hVdiag
  have hex : ∃ j k : Fin 4, H (j,k) ≠ 0 := by
    by_contra he
    push Not at he
    apply hHne
    funext p
    exact he p.1 p.2
  obtain ⟨j,k,hjk⟩ := hex
  have hjkne : j ≠ k := by
    rintro rfl
    exact hjk (hHz j)
  obtain ⟨σ,hσ,hcases⟩ := diagonal_edge_normalizing_permutation i j k hjkne
  let H' := entryPermute σ H
  let V' := entryPermute σ V
  let L' := entryPermuteSubmodule σ L
  have hH' : H' ∈ L' := (entryPermute_mem_iff σ L H).mpr hH
  have hV' : V' ∈ L' := (entryPermute_mem_iff σ L V).mpr hV
  have hHz' : ∀ i : Fin 4, H' (i,i)=0 := entryPermute_hollow σ H hHz
  have hV00 : V' (0,0) ≠ 0 := by simpa [V',entryPermute_apply,hσ] using hi
  have hVtr : (∑ i : Fin 4, V' (i,i))=0 := by
    change (∑ i : Fin 4, V (σ i,σ i))=0
    exact (Equiv.sum_comp σ (fun i => V (i,i))).trans hVtrace
  have hpivot : H' (0,1) ≠ 0 ∨ H' (1,2) ≠ 0 := by
    rcases hcases with ⟨h0,h1⟩ | ⟨h0,h1⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩
    · left
      simpa [H',entryPermute_apply,h0,h1] using hjk
    · left
      simpa [H',entryPermute_apply,h0,h1,hHs k j] using hjk
    · right
      simpa [H',entryPermute_apply,h1,h2] using hjk
    · right
      simpa [H',entryPermute_apply,h1,h2,hHs k j] using hjk
  have make (p : Fin 4 × Fin 4) (hp : H' p ≠ 0) :
      ∃ A ∈ L', ∃ B ∈ L', A ≠ 0 ∧ (∀ i : Fin 4, A (i,i)=0) ∧
        (∑ i : Fin 4, B (i,i))=0 ∧ B (0,0)=1 ∧ A p=1 ∧ B p=0 := by
    let A := (H' p)⁻¹ • H'
    let B := (V' (0,0))⁻¹ • V' - ((V' (0,0))⁻¹*V' p) • A
    have hA : A ∈ L' := L'.smul_mem _ hH'
    have hB : B ∈ L' := L'.sub_mem (L'.smul_mem _ hV') (L'.smul_mem _ hA)
    have hAz : ∀ i : Fin 4, A (i,i)=0 := by intro i; simp [A,hHz']
    have hAp : A p=1 := by simp [A,hp]
    have hAne : A ≠ 0 := by
      intro he
      have hh := congrFun he p
      rw [hAp] at hh
      norm_num at hh
    have hBtr : (∑ i : Fin 4, B (i,i))=0 := by
      simp [B,hAz,← Finset.mul_sum,hVtr]
    have hB00 : B (0,0)=1 := by simp [B,hAz,hV00]
    have hBp : B p=0 := by simp [B,hAp]
    exact ⟨A,hA,B,hB,hAne,hAz,hBtr,hB00,hAp,hBp⟩
  rcases hpivot with h01 | h12
  · obtain ⟨A,hA,B,hB,hAne,hAz,hBtr,hB00,hAp,hBp⟩ := make (0,1) h01
    exact ⟨σ,A,hA,B,hB,hAne,hAz,hBtr,hB00,Or.inl ⟨hAp,hBp⟩⟩
  · obtain ⟨A,hA,B,hB,hAne,hAz,hBtr,hB00,hAp,hBp⟩ := make (1,2) h12
    exact ⟨σ,A,hA,B,hB,hAne,hAz,hBtr,hB00,Or.inr ⟨hAp,hBp⟩⟩

lemma diagonal_rank_two_has_tracezero_pair
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : Module.finrank ℂ L = 3)
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates) = 2) :
    ∃ H ∈ L, ∃ V ∈ L, H ≠ 0 ∧
      (∀ i : Fin 4, H (i,i)=0) ∧
      (∃ i : Fin 4, V (i,i) ≠ 0) ∧
      (∑ i : Fin 4, V (i,i))=0 := by
  let F := matrixDiagonalCoordinates.domRestrict L
  have hrF : Module.finrank ℂ (LinearMap.range F) = 2 := by
    change Module.finrank ℂ
      (LinearMap.range (matrixDiagonalCoordinates.domRestrict L)) = 2
    rw [LinearMap.range_domRestrict]
    exact hd
  have hkF : 0 < Module.finrank ℂ (LinearMap.ker F) := by
    have hn := F.finrank_range_add_finrank_ker
    omega
  letI : Nontrivial (LinearMap.ker F) := Module.nontrivial_of_finrank_pos hkF
  obtain ⟨h, hh⟩ := exists_ne (0 : LinearMap.ker F)
  have hHne : h.val.val ≠ 0 := by
    intro he
    apply hh
    apply Subtype.ext
    apply Subtype.ext
    exact he
  have hHz : ∀ i : Fin 4, h.val.val (i,i)=0 := by
    intro i
    have he : F h.val=0 := h.property
    exact congrFun he i
  let D := L.map matrixDiagonalCoordinates
  let G : D →ₗ[ℂ] ℂ :=
    { toFun := fun d => ∑ i : Fin 4, d.val i
      map_add' := by intros; simp [Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.mul_sum] }
  have hrG : Module.finrank ℂ (LinearMap.range G) ≤ 1 := by
    have hb := Submodule.finrank_le (LinearMap.range G)
    simpa using hb
  have hkG : 0 < Module.finrank ℂ (LinearMap.ker G) := by
    have hn := G.finrank_range_add_finrank_ker
    change Module.finrank ℂ D=2 at hd
    omega
  letI : Nontrivial (LinearMap.ker G) := Module.nontrivial_of_finrank_pos hkG
  obtain ⟨d, hdne⟩ := exists_ne (0 : LinearMap.ker G)
  have hdval : d.val.val ≠ 0 := by
    intro he
    apply hdne
    apply Subtype.ext
    apply Subtype.ext
    exact he
  obtain ⟨V,hV,hVD⟩ := d.val.property
  have hVdiag : ∃ i : Fin 4, V (i,i) ≠ 0 := by
    by_contra he
    push Not at he
    apply hdval
    rw [← hVD]
    funext i
    exact he i
  have hVtrace : (∑ i : Fin 4, V (i,i))=0 := by
    have he : G d.val=0 := d.property
    change (∑ i : Fin 4, d.val.val i)=0 at he
    rw [← hVD] at he
    exact he
  exact ⟨h.val.val,h.val.property,V,hV,hHne,hHz,hVdiag,hVtrace⟩

lemma no_diagonal_rank_two_three_flat_of_tracezero_star_classification
    (hclass : ∀ H V : Fin 4 × Fin 4 → ℂ,
      H ≠ 0 → (∀ i : Fin 4, H (i,i)=0) →
      (∃ i : Fin 4, V (i,i) ≠ 0) → (∑ i : Fin 4, V (i,i))=0 →
      (∀ i j : Fin 4, H (i,j)=H (j,i)) →
      (∀ i j : Fin 4, V (i,j)=V (j,i)) →
      (∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
        1+a*H (i,j)+z*V (i,j))=24) →
      ∃ (σ : Equiv.Perm (Fin 4)) (a b : ℂ),
        starMatrix a b ≠ 0 ∧ entryPermute σ H=starMatrix a b)
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : Module.finrank ℂ L = 3)
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates) = 2)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) : False := by
  obtain ⟨H,hH,V,hV,hHne,hHz,hVdiag,hVtrace⟩ :=
    diagonal_rank_two_has_tracezero_pair L hL hd
  have hpair : ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*H (i,j)+z*V (i,j))=24 := by
    intro a z
    have he := hp _ (L.add_mem (L.smul_mem a hH) (L.smul_mem z hV))
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_assoc] using he
  obtain ⟨σ,a,b,hne,heq⟩ := hclass H V hHne hHz hVdiag hVtrace (hs H hH) (hs V hV) hpair
  have hm : starMatrix a b ∈ entryPermuteSubmodule σ L := by
    rw [← heq]
    exact (entryPermute_mem_iff σ L H).mpr hH
  have hb := containing_nonzero_starMatrix_finrank_le_two
    (entryPermuteSubmodule σ L) a b hne hm
    (entryPermuteSubmodule_symmetric σ L hs)
    (entryPermuteSubmodule_permanent σ L hp)
  rw [entryPermuteSubmodule_finrank] at hb
  omega

def NormalizedIncidentOppositeEdge : Prop :=
  ∀ H V : Fin 4 × Fin 4 → ℂ,
    (∀ i j : Fin 4, H (i,j)=H (j,i)) →
    (∀ i j : Fin 4, V (i,j)=V (j,i)) →
    (∀ i : Fin 4, H (i,i)=0) →
    (∑ i : Fin 4, V (i,i))=0 →
    V (0,0)=1 → H (0,1)=1 → V (0,1)=0 →
    (∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*H (i,j)+z*V (i,j))=24) → H (2,3)=0

lemma incident_edge_product_zero
    (hincident : NormalizedIncidentOppositeEdge)
    (H V : Fin 4 × Fin 4 → ℂ)
    (hHs : ∀ i j : Fin 4, H (i,j)=H (j,i))
    (hVs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hHz : ∀ i : Fin 4, H (i,i)=0)
    (hVtrace : (∑ i : Fin 4, V (i,i))=0) (hV00 : V (0,0) ≠ 0)
    (hp : ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*H (i,j)+z*V (i,j))=24) : H (0,1)*H (2,3)=0 := by
  by_cases hH01 : H (0,1)=0
  · simp [hH01]
  let A := (H (0,1))⁻¹ • H
  let B := (V (0,0))⁻¹ • V - ((V (0,0))⁻¹*V (0,1)) • A
  have hAs : ∀ i j : Fin 4, A (i,j)=A (j,i) := by
    intro i j
    change (H (0,1))⁻¹*H (i,j)=(H (0,1))⁻¹*H (j,i)
    rw [hHs i j]
  have hBs : ∀ i j : Fin 4, B (i,j)=B (j,i) := by
    intro i j
    change (V (0,0))⁻¹*V (i,j)-((V (0,0))⁻¹*V (0,1))*A (i,j)=
      (V (0,0))⁻¹*V (j,i)-((V (0,0))⁻¹*V (0,1))*A (j,i)
    rw [hVs i j,hAs i j]
  have hAz : ∀ i : Fin 4, A (i,i)=0 := by intro i; simp [A,hHz]
  have hA01 : A (0,1)=1 := by simp [A,hH01]
  have hB00 : B (0,0)=1 := by simp [B,hAz,hV00]
  have hB01 : B (0,1)=0 := by simp [B,hA01]
  have hBtrace : (∑ i : Fin 4, B (i,i))=0 := by
    simp [B,hAz,← Finset.mul_sum,hVtrace]
  have hpair : ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*A (i,j)+z*B (i,j))=24 := by
    intro a z
    have heq : (Matrix.of fun (i j : Fin 4) => 1+a*A (i,j)+z*B (i,j))=
        Matrix.of fun (i j : Fin 4) =>
          1+((a-z*((V (0,0))⁻¹*V (0,1)))*(H (0,1))⁻¹)*H (i,j)+
            (z*(V (0,0))⁻¹)*V (i,j) := by
      ext i j
      simp [A,B]
      ring
    rw [heq]
    exact hp _ _
  have hA23 := hincident A B hAs hBs hAz hBtrace hB00 hA01 hB01 hpair
  have hH23 : H (2,3)=0 := by
    change (H (0,1))⁻¹*H (2,3)=0 at hA23
    exact (mul_eq_zero.mp hA23).resolve_left (inv_ne_zero hH01)
  simp [hH23]

lemma level_pair_permutation
    (σ : Equiv.Perm (Fin 4)) (H V : Fin 4 × Fin 4 → ℂ)
    (hp : ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*H (i,j)+z*V (i,j))=24) :
    ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*entryPermute σ H (i,j)+z*entryPermute σ V (i,j))=24 := by
  intro a z
  have he := entryPermute_permanent σ (fun p => a*H p+z*V p)
  have hb : Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+(a*H (i,j)+z*V (i,j)))=24 := by simpa only [add_assoc] using hp a z
  simpa only [entryPermute_apply,add_assoc] using he.trans hb

lemma incident_opposite_products_zero
    (hincident : NormalizedIncidentOppositeEdge)
    (H V : Fin 4 × Fin 4 → ℂ)
    (hHs : ∀ i j : Fin 4, H (i,j)=H (j,i))
    (hVs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hHz : ∀ i : Fin 4, H (i,i)=0)
    (hVtrace : (∑ i : Fin 4, V (i,i))=0) (hV00 : V (0,0) ≠ 0)
    (hp : ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*H (i,j)+z*V (i,j))=24) :
    H (0,1)*H (2,3)=0 ∧ H (0,2)*H (1,3)=0 ∧ H (0,3)*H (1,2)=0 := by
  have hperm (σ : Equiv.Perm (Fin 4)) (hσ0 : σ 0=0) :
      H (σ 0,σ 1)*H (σ 2,σ 3)=0 := by
    have hV00' : entryPermute σ V (0,0) ≠ 0 := by
      simpa only [entryPermute_apply,hσ0] using hV00
    have htrace : (∑ i : Fin 4, entryPermute σ V (i,i))=0 := by
      change (∑ i : Fin 4, V (σ i,σ i))=0
      exact (Equiv.sum_comp σ (fun i => V (i,i))).trans hVtrace
    exact incident_edge_product_zero hincident (entryPermute σ H) (entryPermute σ V)
      (entryPermute_symmetric σ H hHs) (entryPermute_symmetric σ V hVs)
      (entryPermute_hollow σ H hHz) htrace hV00' (level_pair_permutation σ H V hp)
  refine ⟨incident_edge_product_zero hincident H V hHs hVs hHz hVtrace hV00 hp,?_,?_⟩
  · have h := hperm (Equiv.swap (1 : Fin 4) 2) (by decide)
    simpa [Equiv.swap_apply_def] using h
  · have h := hperm (Equiv.swap (1 : Fin 4) 3) (by decide)
    simpa [Equiv.swap_apply_def,hHs 2 1] using h

lemma hollow_star_support_of_opposite_products (a b c d e f : ℂ)
    (haf : a*f=0) (hbe : b*e=0) (hcd : c*d=0)
    (hT : a*b*d+a*c*e+b*c*f+d*e*f=0) :
    (d=0 ∧ e=0 ∧ f=0) ∨ (b=0 ∧ c=0 ∧ f=0) ∨
    (a=0 ∧ c=0 ∧ e=0) ∨ (a=0 ∧ b=0 ∧ d=0) := by
  by_cases ha : a=0
  · by_cases hb : b=0
    · by_cases hc : c=0
      · have hdef : d*e*f=0 := by simpa [ha,hb,hc] using hT
        rcases mul_eq_zero.mp hdef with hde | hf
        · rcases mul_eq_zero.mp hde with hd | he
          · exact Or.inr (Or.inr (Or.inr ⟨ha,hb,hd⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨ha,hc,he⟩))
        · exact Or.inr (Or.inl ⟨hb,hc,hf⟩)
      · have hd : d=0 := (mul_eq_zero.mp hcd).resolve_left hc
        exact Or.inr (Or.inr (Or.inr ⟨ha,hb,hd⟩))
    · have he : e=0 := (mul_eq_zero.mp hbe).resolve_left hb
      by_cases hc : c=0
      · exact Or.inr (Or.inr (Or.inl ⟨ha,hc,he⟩))
      · have hd : d=0 := (mul_eq_zero.mp hcd).resolve_left hc
        have hbcf : b*c*f=0 := by simpa [ha,he] using hT
        have hf : f=0 := (mul_eq_zero.mp hbcf).resolve_left (mul_ne_zero hb hc)
        exact Or.inl ⟨hd,he,hf⟩
  · have hf : f=0 := (mul_eq_zero.mp haf).resolve_left ha
    have hsum : b*d+c*e=0 := by
      have hh : a*(b*d+c*e)=0 := by linear_combination hT-(b*c+d*e)*hf
      exact (mul_eq_zero.mp hh).resolve_left ha
    have hbd : b*d=0 := by
      have hh : (b*d)^2=0 := by linear_combination b*d*hsum-c*d*hbe
      exact eq_zero_of_pow_eq_zero hh
    have hce : c*e=0 := by linear_combination hsum-hbd
    by_cases hb : b=0
    · by_cases hc : c=0
      · exact Or.inr (Or.inl ⟨hb,hc,hf⟩)
      · have hd : d=0 := (mul_eq_zero.mp hcd).resolve_left hc
        have he : e=0 := (mul_eq_zero.mp hce).resolve_left hc
        exact Or.inl ⟨hd,he,hf⟩
    · have hd : d=0 := (mul_eq_zero.mp hbd).resolve_left hb
      have he : e=0 := (mul_eq_zero.mp hbe).resolve_left hb
      exact Or.inl ⟨hd,he,hf⟩

lemma hollow_opposite_scalar_permuted_star (a b c d e f : ℂ)
    (hS : a+b+c+d+e+f=0)
    (haf : a*f=0) (hbe : b*e=0) (hcd : c*d=0)
    (hT : a*b*d+a*c*e+b*c*f+d*e*f=0) :
    ∃ (σ : Equiv.Perm (Fin 4)) (u v : ℂ),
      entryPermute σ (fun p => hollowMatrix a b c d e f p.1 p.2)=starMatrix u v := by
  rcases hollow_star_support_of_opposite_products a b c d e f haf hbe hcd hT with
    ⟨hd,he,hf⟩ | ⟨hb,hc,hf⟩ | ⟨ha,hc,he⟩ | ⟨ha,hb,hd⟩
  · have hc : c = -a-b := by linear_combination hS-hd-he-hf
    refine ⟨Equiv.refl _,a,b,?_⟩
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,hollowMatrix,starMatrix,hc,hd,he,hf]
  · have he : e = -a-d := by linear_combination hS-hb-hc-hf
    refine ⟨Equiv.swap 0 1,a,d,?_⟩
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,Equiv.swap_apply_def,hollowMatrix,starMatrix,hb,hc,he,hf]
  · have hf : f = -d-b := by linear_combination hS-ha-hc-he
    refine ⟨Equiv.swap 0 2,d,b,?_⟩
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,Equiv.swap_apply_def,hollowMatrix,starMatrix,ha,hc,he,hf]
  · have hc : c = -e-f := by linear_combination hS-ha-hb-hd
    refine ⟨Equiv.swap 0 3,e,f,?_⟩
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,Equiv.swap_apply_def,hollowMatrix,starMatrix,ha,hb,hc,hd]

lemma hollow_opposite_products_permuted_star (H : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, H (i,j)=H (j,i))
    (hz : ∀ i : Fin 4, H (i,i)=0) (hne : H ≠ 0)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+z*H (i,j))=24)
    (haf : H (0,1)*H (2,3)=0) (hbe : H (0,2)*H (1,3)=0) (hcd : H (0,3)*H (1,2)=0) :
    ∃ (σ : Equiv.Perm (Fin 4)) (a b : ℂ),
      starMatrix a b ≠ 0 ∧ entryPermute σ H=starMatrix a b := by
  have hrec : H=(fun p => hollowMatrix (H (0,1)) (H (0,2)) (H (0,3))
      (H (1,2)) (H (1,3)) (H (2,3)) p.1 p.2) := by
    funext p
    exact hollow_reconstruction H hs hz p.1 p.2
  have hp' : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+z*hollowMatrix (H (0,1)) (H (0,2)) (H (0,3))
        (H (1,2)) (H (1,3)) (H (2,3)) i j)=24 := by
    intro z
    convert hp z using 1
    congr 1
    funext i j
    change 1+z*hollowMatrix (H (0,1)) (H (0,2)) (H (0,3))
      (H (1,2)) (H (1,3)) (H (2,3)) i j=1+z*H (i,j)
    rw [hollow_reconstruction H hs hz i j]
  have hS := (hollow_coefficient_constraints _ _ _ _ _ _ hp').1
  have hC := hollow_coefficient_cubic_zero _ _ _ _ _ _ hp'
  have hT : H (0,1)*H (0,2)*H (1,2)+H (0,1)*H (0,3)*H (1,3)+
      H (0,2)*H (0,3)*H (2,3)+H (1,2)*H (1,3)*H (2,3)=0 := by
    dsimp [hollowCubic] at hC
    linear_combination hC/2-
      (H (0,1)+H (0,2)+H (0,3)+H (1,2)+H (1,3)+H (2,3))*(haf+hbe+hcd)
  obtain ⟨σ,a,b,heq⟩ := hollow_opposite_scalar_permuted_star _ _ _ _ _ _ hS haf hbe hcd hT
  have he : entryPermute σ H=starMatrix a b := by rw [hrec]; exact heq
  refine ⟨σ,a,b,?_,he⟩
  intro hzero
  apply hne
  apply (entryPermute σ).injective
  rw [he,hzero,map_zero]

lemma tracezero_pair_star_of_normalized_incident
    (hincident : NormalizedIncidentOppositeEdge)
    (H V : Fin 4 × Fin 4 → ℂ)
    (hHne : H ≠ 0) (hHz : ∀ i : Fin 4, H (i,i)=0)
    (hVdiag : ∃ i : Fin 4, V (i,i) ≠ 0)
    (hVtrace : (∑ i : Fin 4, V (i,i))=0)
    (hHs : ∀ i j : Fin 4, H (i,j)=H (j,i))
    (hVs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*H (i,j)+z*V (i,j))=24) :
    ∃ (σ : Equiv.Perm (Fin 4)) (a b : ℂ),
      starMatrix a b ≠ 0 ∧ entryPermute σ H=starMatrix a b := by
  obtain ⟨i,hi⟩ := hVdiag
  let σ := Equiv.swap (0 : Fin 4) i
  have hσ : σ 0=i := by simp [σ]
  let H' := entryPermute σ H
  let V' := entryPermute σ V
  have hHne' : H' ≠ 0 := by
    intro he
    apply hHne
    apply (entryPermute σ).injective
    simpa only [map_zero] using he
  have hHsym := entryPermute_symmetric σ H hHs
  have hVsym := entryPermute_symmetric σ V hVs
  have hHz' := entryPermute_hollow σ H hHz
  have hV00 : V' (0,0) ≠ 0 := by simpa only [V',entryPermute_apply,hσ] using hi
  have hVtr : (∑ i : Fin 4, V' (i,i))=0 := by
    change (∑ i : Fin 4, V (σ i,σ i))=0
    exact (Equiv.sum_comp σ (fun i => V (i,i))).trans hVtrace
  have hpair := level_pair_permutation σ H V hp
  obtain ⟨haf,hbe,hcd⟩ := incident_opposite_products_zero hincident H' V'
    hHsym hVsym hHz' hVtr hV00 hpair
  have hline : ∀ z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+z*H' (i,j))=24 := by
    intro z
    simpa only [zero_mul,add_zero] using hpair z 0
  obtain ⟨τ,a,b,hne,heq⟩ := hollow_opposite_products_permuted_star H'
    hHsym hHz' hHne' hline haf hbe hcd
  refine ⟨σ*τ,a,b,hne,?_⟩
  calc
    entryPermute (σ*τ) H=entryPermute τ (entryPermute σ H) := by
      funext p
      rcases p with ⟨j,k⟩
      simp [entryPermute_apply,Equiv.Perm.mul_apply]
    _=starMatrix a b := heq

lemma no_rank_two_diagonal_three_flat_of_normalized_incident
    (hincident : NormalizedIncidentOppositeEdge)
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : Module.finrank ℂ L=3)
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates)=2)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) : False := by
  exact no_diagonal_rank_two_three_flat_of_tracezero_star_classification
    (tracezero_pair_star_of_normalized_incident hincident) L hL hd hs hp

def hadamardSigns : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,1,1; 1,1,-1,-1; 1,-1,1,-1; 1,-1,-1,1]

noncomputable def hadamardTransform :
    (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun V p := (∑ i : Fin 4, ∑ j : Fin 4,
    hadamardSigns p.1 i * V (i,j) * hadamardSigns p.2 j) / 4
  map_add' V W := by
    funext p
    simp [Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib,add_div]
  map_smul' z V := by
    funext p
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp [hadamardSigns,Fin.sum_univ_succ]
    ring

set_option maxHeartbeats 1600000 in
lemma hadamardTransform_involution (V : Fin 4 × Fin 4 → ℂ) :
    hadamardTransform (hadamardTransform V)=V := by
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [hadamardTransform,hadamardSigns,Fin.sum_univ_succ] <;> ring

lemma hadamardTransform_symmetric (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j)=V (j,i)) :
    ∀ i j : Fin 4, hadamardTransform V (i,j)=hadamardTransform V (j,i) := by
  intro i j
  change (∑ a : Fin 4, ∑ b : Fin 4,
    hadamardSigns i a * V (a,b) * hadamardSigns j b) / 4 =
    (∑ a : Fin 4, ∑ b : Fin 4,
      hadamardSigns j a * V (a,b) * hadamardSigns i b) / 4
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [hs b a]
  ring

lemma hadamardTransform_zero_zero (V : Fin 4 × Fin 4 → ℂ) :
    hadamardTransform V (0,0)=(∑ i : Fin 4, ∑ j : Fin 4, V (i,j))/4 := by
  simp [hadamardTransform,hadamardSigns,Fin.sum_univ_succ]

lemma hadamardTransform_trace (V : Fin 4 × Fin 4 → ℂ) :
    (∑ i : Fin 4, hadamardTransform V (i,i))=∑ i : Fin 4, V (i,i) := by
  simp [hadamardTransform,hadamardSigns,Fin.sum_univ_succ]
  ring

noncomputable def hadamardB : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun V := ![hadamardTransform V (1,1),hadamardTransform V (2,2),hadamardTransform V (3,3)]
  map_add' := by intros; ext i; fin_cases i <;> simp
  map_smul' := by intros; ext i; fin_cases i <;> simp

noncomputable def hadamardP : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun V := ![3*hadamardTransform V (0,1)+hadamardTransform V (2,3),
    3*hadamardTransform V (0,2)+hadamardTransform V (1,3),
    3*hadamardTransform V (0,3)+hadamardTransform V (1,2)]
  map_add' := by intros; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intros; ext i; fin_cases i <;> simp <;> ring

noncomputable def hadamardD : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun V := ![hadamardTransform V (0,1)+hadamardTransform V (2,3),
    hadamardTransform V (0,2)+hadamardTransform V (1,3),
    hadamardTransform V (0,3)+hadamardTransform V (1,2)]
  map_add' := by intros; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intros; ext i; fin_cases i <;> simp <;> ring

noncomputable def hadamardCoordinateMatrix (B P D : Fin 3 → ℂ) : Fin 4 × Fin 4 → ℂ :=
  fun p => (!![0,(P 0-D 0)/2,(P 1-D 1)/2,(P 2-D 2)/2;
    (P 0-D 0)/2,B 0,(3*D 2-P 2)/2,(3*D 1-P 1)/2;
    (P 1-D 1)/2,(3*D 2-P 2)/2,B 1,(3*D 0-P 0)/2;
    (P 2-D 2)/2,(3*D 1-P 1)/2,(3*D 0-P 0)/2,B 2] : Matrix (Fin 4) (Fin 4) ℂ) p.1 p.2

noncomputable def hadamardReconstruct (B P D : Fin 3 → ℂ) : Fin 4 × Fin 4 → ℂ :=
  hadamardTransform (hadamardCoordinateMatrix B P D)

lemma hadamardCoordinateMatrix_coordinates (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (ht : (∑ i : Fin 4, ∑ j : Fin 4, V (i,j))=0) :
    hadamardCoordinateMatrix (hadamardB V) (hadamardP V) (hadamardD V)=hadamardTransform V := by
  have hsym := hadamardTransform_symmetric V hs
  have h00 : hadamardTransform V (0,0)=0 := by rw [hadamardTransform_zero_zero,ht]; norm_num
  have h10 := hsym 1 0
  have h20 := hsym 2 0
  have h30 := hsym 3 0
  have h21 := hsym 2 1
  have h31 := hsym 3 1
  have h32 := hsym 3 2
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [hadamardCoordinateMatrix,hadamardB,hadamardP,hadamardD,
      h00,h10,h20,h30,h21,h31,h32] <;> ring

lemma hadamard_reconstruction (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (ht : (∑ i : Fin 4, ∑ j : Fin 4, V (i,j))=0) :
    hadamardReconstruct (hadamardB V) (hadamardP V) (hadamardD V)=V := by
  unfold hadamardReconstruct
  rw [hadamardCoordinateMatrix_coordinates V hs ht,hadamardTransform_involution]

lemma hadamard_trace_coordinates (V : Fin 4 × Fin 4 → ℂ)
    (ht : (∑ i : Fin 4, ∑ j : Fin 4, V (i,j))=0) :
    (∑ i : Fin 3, hadamardB V i)=∑ i : Fin 4, V (i,i) := by
  have h00 : hadamardTransform V (0,0)=0 := by rw [hadamardTransform_zero_zero,ht]; norm_num
  have hh := hadamardTransform_trace V
  simpa [hadamardB,Fin.sum_univ_succ,h00] using hh

lemma hadamard_reconstruct_diagonal (B P D : Fin 3 → ℂ) :
    (fun i : Fin 4 => hadamardReconstruct B P D (i,i)) =
      ![(B 0+B 1+B 2)/4+(D 0+D 1+D 2)/2,
        (B 0+B 1+B 2)/4+(D 0-D 1-D 2)/2,
        (B 0+B 1+B 2)/4+(-D 0+D 1-D 2)/2,
        (B 0+B 1+B 2)/4+(-D 0-D 1+D 2)/2] := by
  funext i
  fin_cases i <;>
    simp [hadamardReconstruct,hadamardTransform,hadamardCoordinateMatrix,
      hadamardSigns,Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 1600000 in
lemma permanent_level_entry_sum_zero (V : Fin 4 × Fin 4 → ℂ)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+z*V (i,j))=24) :
    (∑ i : Fin 4, ∑ j : Fin 4, V (i,j))=0 := by
  have h1 := hp 1
  have hn1 := hp (-1)
  have h2 := hp 2
  have hn2 := hp (-2)
  rw [permanent_four] at h1 hn1 h2 hn2
  simp only [Matrix.of_apply] at h1 hn1 h2 hn2
  simp [Fin.sum_univ_succ]
  linear_combination h1/9-hn1/9-h2/72+hn2/72

lemma level_flat_entry_sum_zero
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24)
    (V : Fin 4 × Fin 4 → ℂ) (hV : V ∈ L) :
    (∑ i : Fin 4, ∑ j : Fin 4, V (i,j))=0 := by
  apply permanent_level_entry_sum_zero V
  intro z
  simpa only [Pi.smul_apply,smul_eq_mul] using hp _ (L.smul_mem z hV)

lemma hadamardD_zero_constant_diagonal (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (ht : (∑ i : Fin 4, ∑ j : Fin 4, V (i,j))=0)
    (hD : hadamardD V=0) :
    ∀ i : Fin 4, V (i,i)=(hadamardB V 0+hadamardB V 1+hadamardB V 2)/4 := by
  have hd := hadamard_reconstruct_diagonal (hadamardB V) (hadamardP V) (hadamardD V)
  rw [hadamard_reconstruction V hs ht] at hd
  intro i
  have hi := congrFun hd i
  fin_cases i <;> simpa [hD] using hi

lemma hadamardD_injective_on_full_diagonal_rank
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates)=Module.finrank ℂ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    Function.Injective (hadamardD.domRestrict L) := by
  let F := matrixDiagonalCoordinates.domRestrict L
  have hr : Module.finrank ℂ (LinearMap.range F)=Module.finrank ℂ L := by
    change Module.finrank ℂ (LinearMap.range (matrixDiagonalCoordinates.domRestrict L)) = _
    rw [LinearMap.range_domRestrict]
    exact hd
  have hk : Module.finrank ℂ (LinearMap.ker F)=0 := by
    have hn := F.finrank_range_add_finrank_ker
    omega
  have hF : Function.Injective F :=
    LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)
  have hzero (V : L) (hD : hadamardD V.val=0) : V=0 := by
    have hc := hadamardD_zero_constant_diagonal V.val (hs V.val V.property)
      (level_flat_entry_sum_zero L hp V.val V.property) hD
    have hr0 := level_flat_constant_diagonal_zero L hs hp V.val V.property
      ((hadamardB V.val 0+hadamardB V.val 1+hadamardB V.val 2)/4) hc
    apply hF
    change matrixDiagonalCoordinates V.val=matrixDiagonalCoordinates 0
    funext i
    change V.val (i,i)=0
    rw [hc i,hr0]
  intro V W he
  apply sub_eq_zero.mp
  apply hzero (V-W)
  change (hadamardD.domRestrict L) (V-W)=0
  rw [map_sub,he,sub_self]

lemma hadamardD_bijective_on_rank_three_flat
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : Module.finrank ℂ L=3)
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates)=3)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    Function.Bijective (hadamardD.domRestrict L) := by
  have hinj := hadamardD_injective_on_full_diagonal_rank L (hd.trans hL.symm) hs hp
  refine ⟨hinj,?_⟩
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [LinearMap.finrank_range_of_inj hinj,hL]
  simp

noncomputable def hadamardTrace : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] ℂ where
  toFun V := ∑ i : Fin 4, V (i,i)
  map_add' := by intros; simp [Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum]

lemma hadamardTrace_permute (σ : Equiv.Perm (Fin 4)) (V : Fin 4 × Fin 4 → ℂ) :
    hadamardTrace (entryPermute σ V)=hadamardTrace V := by
  exact Equiv.sum_comp σ (fun i => V (i,i))

lemma hadamardD_swap13 (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j)=V (j,i)) :
    hadamardD (entryPermute (Equiv.swap (1 : Fin 4) 3) V)=
      ![hadamardD V 2,hadamardD V 1,hadamardD V 0] := by
  have h10 := hs 1 0
  have h20 := hs 2 0
  have h30 := hs 3 0
  have h21 := hs 2 1
  have h31 := hs 3 1
  have h32 := hs 3 2
  funext i
  fin_cases i <;>
    simp [hadamardD,hadamardTransform,hadamardSigns,entryPermute,
      Equiv.swap_apply_def,Fin.sum_univ_succ,h10,h20,h30,h21,h31,h32] <;> ring

lemma hadamardD_swap23 (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j)=V (j,i)) :
    hadamardD (entryPermute (Equiv.swap (2 : Fin 4) 3) V)=
      ![hadamardD V 0,hadamardD V 2,hadamardD V 1] := by
  have h10 := hs 1 0
  have h20 := hs 2 0
  have h30 := hs 3 0
  have h21 := hs 2 1
  have h31 := hs 3 1
  have h32 := hs 3 2
  funext i
  fin_cases i <;>
    simp [hadamardD,hadamardTransform,hadamardSigns,entryPermute,
      Equiv.swap_apply_def,Fin.sum_univ_succ,h10,h20,h30,h21,h31,h32] <;> ring

lemma rank_three_flat_has_trace_pivot_basis
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : Module.finrank ℂ L=3)
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates)=3)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    ∃ σ : Equiv.Perm (Fin 4),
      ∃ U ∈ entryPermuteSubmodule σ L, ∃ V ∈ entryPermuteSubmodule σ L,
      ∃ W ∈ entryPermuteSubmodule σ L,
      hadamardD U=![1,0,0] ∧ hadamardD V=![0,1,0] ∧ hadamardD W=![0,0,1] ∧
      (hadamardTrace W ≠ 0 ∨ (hadamardTrace U=0 ∧ hadamardTrace V=0)) := by
  have hsurj := (hadamardD_bijective_on_rank_three_flat L hL hd hs hp).2
  obtain ⟨X,hX⟩ := hsurj ![1,0,0]
  obtain ⟨Y,hY⟩ := hsurj ![0,1,0]
  obtain ⟨Z,hZ⟩ := hsurj ![0,0,1]
  change hadamardD X.val=![1,0,0] at hX
  change hadamardD Y.val=![0,1,0] at hY
  change hadamardD Z.val=![0,0,1] at hZ
  have hid (htrace : hadamardTrace Z.val ≠ 0 ∨
      (hadamardTrace X.val=0 ∧ hadamardTrace Y.val=0)) :
      ∃ σ : Equiv.Perm (Fin 4),
        ∃ U ∈ entryPermuteSubmodule σ L, ∃ V ∈ entryPermuteSubmodule σ L,
        ∃ W ∈ entryPermuteSubmodule σ L,
        hadamardD U=![1,0,0] ∧ hadamardD V=![0,1,0] ∧ hadamardD W=![0,0,1] ∧
        (hadamardTrace W ≠ 0 ∨ (hadamardTrace U=0 ∧ hadamardTrace V=0)) := by
    refine ⟨Equiv.refl _,X.val,?_,Y.val,?_,Z.val,?_,hX,hY,hZ,htrace⟩
    · exact ⟨X.val,X.property,rfl⟩
    · exact ⟨Y.val,Y.property,rfl⟩
    · exact ⟨Z.val,Z.property,rfl⟩
  by_cases htz : hadamardTrace Z.val=0
  · by_cases hty : hadamardTrace Y.val=0
    · by_cases htx : hadamardTrace X.val=0
      · exact hid (Or.inr ⟨htx,hty⟩)
      · let σ := Equiv.swap (1 : Fin 4) 3
        refine ⟨σ,entryPermute σ Z.val,?_,entryPermute σ Y.val,?_,
          entryPermute σ X.val,?_,?_,?_,?_,Or.inl ?_⟩
        · exact (entryPermute_mem_iff σ L Z.val).mpr Z.property
        · exact (entryPermute_mem_iff σ L Y.val).mpr Y.property
        · exact (entryPermute_mem_iff σ L X.val).mpr X.property
        · simpa [σ,hZ] using hadamardD_swap13 Z.val (hs Z.val Z.property)
        · simpa [σ,hY] using hadamardD_swap13 Y.val (hs Y.val Y.property)
        · simpa [σ,hX] using hadamardD_swap13 X.val (hs X.val X.property)
        · simpa only [hadamardTrace_permute] using htx
    · let σ := Equiv.swap (2 : Fin 4) 3
      refine ⟨σ,entryPermute σ X.val,?_,entryPermute σ Z.val,?_,
        entryPermute σ Y.val,?_,?_,?_,?_,Or.inl ?_⟩
      · exact (entryPermute_mem_iff σ L X.val).mpr X.property
      · exact (entryPermute_mem_iff σ L Z.val).mpr Z.property
      · exact (entryPermute_mem_iff σ L Y.val).mpr Y.property
      · simpa [σ,hX] using hadamardD_swap23 X.val (hs X.val X.property)
      · simpa [σ,hZ] using hadamardD_swap23 Z.val (hs Z.val Z.property)
      · simpa [σ,hY] using hadamardD_swap23 Y.val (hs Y.val Y.property)
      · simpa only [hadamardTrace_permute] using hty
  · exact hid (Or.inl htz)

lemma rank_three_flat_has_hadamard_incidence_basis
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : Module.finrank ℂ L=3)
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates)=3)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    ∃ σ : Equiv.Perm (Fin 4), ∃ k l : ℂ,
      ∃ A ∈ entryPermuteSubmodule σ L, ∃ B ∈ entryPermuteSubmodule σ L,
      ∃ W ∈ entryPermuteSubmodule σ L,
      hadamardD A=![1,0,k] ∧ hadamardD B=![0,1,l] ∧ hadamardD W=![0,0,1] ∧
      hadamardTrace A=0 ∧ hadamardTrace B=0 := by
  obtain ⟨σ,U,hU,V,hV,W,hW,hDU,hDV,hDW,htr⟩ :=
    rank_three_flat_has_trace_pivot_basis L hL hd hs hp
  rcases htr with hw | ⟨hu,hv⟩
  · let k := -hadamardTrace U/hadamardTrace W
    let l := -hadamardTrace V/hadamardTrace W
    let A := U+k • W
    let B := V+l • W
    refine ⟨σ,k,l,A,?_,B,?_,W,hW,?_,?_,hDW,?_,?_⟩
    · exact (entryPermuteSubmodule σ L).add_mem hU ((entryPermuteSubmodule σ L).smul_mem k hW)
    · exact (entryPermuteSubmodule σ L).add_mem hV ((entryPermuteSubmodule σ L).smul_mem l hW)
    · simp [A,map_add,map_smul,hDU,hDW]
    · simp [B,map_add,map_smul,hDV,hDW]
    · simp [A,k,map_add,map_smul,hw]
    · simp [B,l,map_add,map_smul,hw]
  · exact ⟨σ,0,0,U,hU,V,hV,W,hW,hDU,hDV,hDW,hu,hv⟩

lemma rank_three_flat_hadamard_incidence_family
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : Module.finrank ℂ L=3)
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates)=3)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    ∃ (σ : Equiv.Perm (Fin 4)) (k l : ℂ) (BA BB BW PA PB PW : Fin 3 → ℂ),
      (∑ i : Fin 3, BA i)=0 ∧ (∑ i : Fin 3, BB i)=0 ∧
      ∀ s t u : ℂ,
        hadamardReconstruct (s • BA+t • BB+u • BW) (s • PA+t • PB+u • PW)
          ![s,t,k*s+l*t+u] ∈ entryPermuteSubmodule σ L ∧
        Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
          1+hadamardReconstruct (s • BA+t • BB+u • BW) (s • PA+t • PB+u • PW)
            ![s,t,k*s+l*t+u] (i,j))=24 := by
  obtain ⟨σ,k,l,A,hA,B,hB,W,hW,hDA,hDB,hDW,htrA,htrB⟩ :=
    rank_three_flat_has_hadamard_incidence_basis L hL hd hs hp
  let L' := entryPermuteSubmodule σ L
  have hs' := entryPermuteSubmodule_symmetric σ L hs
  have hp' := entryPermuteSubmodule_permanent σ L hp
  refine ⟨σ,k,l,hadamardB A,hadamardB B,hadamardB W,
    hadamardP A,hadamardP B,hadamardP W,?_,?_,?_⟩
  · exact (hadamard_trace_coordinates A (level_flat_entry_sum_zero L' hp' A hA)).trans htrA
  · exact (hadamard_trace_coordinates B (level_flat_entry_sum_zero L' hp' B hB)).trans htrB
  · intro s t u
    let T := s • A+t • B+u • W
    have hT : T ∈ L' := L'.add_mem (L'.add_mem (L'.smul_mem s hA) (L'.smul_mem t hB))
      (L'.smul_mem u hW)
    have hD : hadamardD T=![s,t,k*s+l*t+u] := by
      simp only [T,map_add,map_smul,hDA,hDB,hDW]
      funext i
      fin_cases i <;> simp <;> ring
    have hrec := hadamard_reconstruction T (hs' T hT) (level_flat_entry_sum_zero L' hp' T hT)
    rw [hD] at hrec
    simp only [T,map_add,map_smul] at hrec
    constructor
    · rw [hrec]
      exact hT
    · rw [hrec]
      exact hp' T hT

def incidentGenerator1 (_x0 _x1 _x2 x3 _x4 x5 _x6 x7 _x8 x9 : ℂ) : ℂ :=
  4*x3*x9 - 4*x3 + 4*x5*x7 - 4*x5 - 4*x7 - 4*x9 - 4

def incidentGenerator2 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℂ) : ℂ :=
  -4*x0*x3 - 8*x0*x7 - 4*x0*x9 - 8*x0 - 4*x1*x3 + 4*x1*x5 - 4*x1*x7 + 4*x1*x9 + 4*x2*x9 - 4*x2 +
    4*x3*x8 - 8*x3 + 4*x4*x7 - 4*x4 + 4*x5*x6 - 4*x5 - 4*x6 - 4*x7 - 4*x8 - 8

def incidentGenerator3 (x0 x1 x2 _x3 x4 _x5 x6 _x7 x8 _x9 : ℂ) : ℂ :=
  -2*x0^2 - 2*x0*x1 - 4*x0*x2 - 8*x0*x6 - 4*x0*x8 - 2*x0 - 2*x1^2 - 4*x1*x2 + 4*x1*x4 - 4*x1*x6 +
    4*x1*x8 - 2*x1 + 4*x2*x8 - 8*x2 + 4*x4*x6 - 4*x4 - 4*x6 - 2

def incidentGenerator4 (_x0 _x1 _x2 x3 _x4 x5 _x6 x7 _x8 x9 : ℂ) : ℂ :=
  -2*x3^2*x5 - 2*x3*x5^2 - 2*x3*x5*x7 - 2*x3*x5*x9 - 2*x3*x5 - 2*x3*x7*x9 + 2*x3*x7 - 2*x5*x7*x9 +
    2*x5*x9 - 2*x7^2*x9 - 2*x7*x9^2 - 2*x7*x9

def incidentGenerator5 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℂ) : ℂ :=
  -x0*x3^2 - 2*x0*x3*x7 - 2*x0*x3 + 2*x0*x7*x9 + x0*x9^2 + 2*x0*x9 - x1*x3^2 - 2*x1*x3*x7 - 2*x1*x3
    + x1*x5^2 + 2*x1*x5*x9 + 2*x1*x5 - x1*x7^2 - 2*x1*x7 + x1*x9^2 + 2*x1*x9 - 4*x2*x3*x5 -
    2*x2*x5^2 - 2*x2*x5*x7 - 2*x2*x5*x9 - 2*x2*x5 - 2*x2*x7*x9 + 2*x2*x7 - 2*x3^2*x4 - 4*x3*x4*x5 -
    2*x3*x4*x7 - 2*x3*x4*x9 - 2*x3*x4 - 2*x3*x5*x6 - 2*x3*x5*x8 + 2*x3*x5 - 2*x3*x6*x9 + 2*x3*x6 -
    2*x3*x7*x8 - 2*x3*x7 - 2*x4*x7*x9 + 2*x4*x9 + x5^2 - 2*x5*x6*x9 - 2*x5*x7*x8 + 2*x5*x8 + 2*x5 -
    4*x6*x7*x9 - 2*x6*x9^2 - 2*x6*x9 - 2*x7^2*x8 - x7^2 - 4*x7*x8*x9 - 2*x7*x8 - 2*x7

def incidentGenerator6 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℂ) : ℂ :=
  -2*x0^2*x3 - 2*x0*x1*x3 + 2*x0*x1*x5 - 2*x0*x1 - 2*x0*x2*x3 - 2*x0*x2*x7 - 2*x0*x2 - 2*x0*x3*x6 -
    4*x0*x3 - 2*x0*x5 + 2*x0*x6*x9 + 2*x0*x7*x8 - 4*x0*x7 + 2*x0*x8*x9 + 2*x0*x8 - 2*x0*x9 - 2*x0 -
    2*x1^2 - 2*x1*x2*x3 - 2*x1*x2*x7 - 2*x1*x2 - 2*x1*x3*x6 + 2*x1*x4*x5 + 2*x1*x4*x9 + 2*x1*x4 +
    2*x1*x5*x8 - 2*x1*x6*x7 - 2*x1*x6 - 2*x1*x7 + 2*x1*x8*x9 + 2*x1*x8 + 2*x1*x9 - 2*x1 - 2*x2^2*x5
    - 4*x2*x3*x4 - 4*x2*x4*x5 - 2*x2*x4*x7 - 2*x2*x4*x9 - 2*x2*x4 - 2*x2*x5*x6 - 2*x2*x5*x8 +
    2*x2*x5 - 2*x2*x6*x9 + 2*x2*x6 - 2*x2*x7*x8 - 2*x2*x7 - 2*x3*x4^2 - 2*x3*x4*x6 - 2*x3*x4*x8 +
    2*x3*x4 - 2*x3*x6*x8 - 2*x3*x6 + 2*x4*x5 - 2*x4*x6*x9 - 2*x4*x7*x8 + 2*x4*x8 + 2*x4 - 2*x5*x6*x8
    - 2*x6^2*x9 - 4*x6*x7*x8 - 2*x6*x7 - 4*x6*x8*x9 - 2*x6*x8 - 2*x6 - 2*x7*x8^2 - 2*x7

def incidentGenerator7 (x0 x1 x2 _x3 x4 _x5 x6 _x7 x8 _x9 : ℂ) : ℂ :=
  -x0^2*x1 - 2*x0^2*x2 - x0^2 - x0*x1^2 - 2*x0*x1*x2 + 2*x0*x1*x4 - 2*x0*x1 - x0*x2^2 - 2*x0*x2*x6 -
    4*x0*x2 - 2*x0*x4 + 2*x0*x6*x8 - 4*x0*x6 + x0*x8^2 - 2*x0*x8 - x0 - x1^2 - x1*x2^2 - 2*x1*x2*x6
    + x1*x4^2 + 2*x1*x4*x8 - x1*x6^2 - 2*x1*x6 + x1*x8^2 + 2*x1*x8 - x1 - 2*x2^2*x4 - 2*x2*x4^2 -
    2*x2*x4*x6 - 2*x2*x4*x8 + 2*x2*x4 - 2*x2*x6*x8 - 2*x2*x6 + x4^2 - 2*x4*x6*x8 - 2*x6^2*x8 - x6^2
    - 2*x6*x8^2 - 2*x6

def incidentGenerator8 (_x0 _x1 _x2 x3 _x4 x5 _x6 x7 _x8 x9 : ℂ) : ℂ :=
  x3^2*x9^2 - 2*x3^2*x9 + x3^2 + 2*x3*x5*x7*x9 - 2*x3*x5*x7 - 2*x3*x5*x9 + 2*x3*x5 - 2*x3*x7*x9 +
    2*x3*x7 - 2*x3*x9^2 + 2*x3 + x5^2*x7^2 - 2*x5^2*x7 + x5^2 - 2*x5*x7^2 - 2*x5*x7*x9 + 2*x5*x9 +
    2*x5 + x7^2 + 2*x7*x9 + 2*x7 + x9^2 + 2*x9 + 1

def incidentGenerator9 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℂ) : ℂ :=
  -2*x0*x3^2*x5 - 2*x0*x3*x5^2 - 2*x0*x3*x5*x7 - 2*x0*x3*x5*x9 - 2*x0*x3*x5 - 2*x0*x3*x7 -
    2*x1*x3*x7 + 2*x1*x5*x9 + 2*x2*x3*x9^2 - 4*x2*x3*x9 + 2*x2*x3 + 2*x2*x5*x7*x9 - 2*x2*x5*x7 -
    2*x2*x5*x9 + 2*x2*x5 - 2*x2*x7*x9 + 2*x2*x7 - 2*x2*x9^2 + 2*x2 + 2*x3^2*x8*x9 - 2*x3^2*x8 +
    2*x3*x4*x7*x9 - 2*x3*x4*x7 - 2*x3*x4*x9 + 2*x3*x4 + 2*x3*x5*x6*x9 - 2*x3*x5*x6 + 2*x3*x5*x7*x8 -
    2*x3*x5*x8 - 2*x3*x6*x9 + 2*x3*x6 - 2*x3*x7*x8 - 2*x3*x7*x9 - 2*x3*x7 - 4*x3*x8*x9 +
    2*x4*x5*x7^2 - 4*x4*x5*x7 + 2*x4*x5 - 2*x4*x7^2 - 2*x4*x7*x9 + 2*x4*x9 + 2*x4 + 2*x5^2*x6*x7 -
    2*x5^2*x6 - 4*x5*x6*x7 - 2*x5*x6*x9 - 2*x5*x7*x8 - 2*x5*x7*x9 + 2*x5*x8 + 2*x6*x7 + 2*x6*x9 +
    2*x6 - 2*x7^2*x9 + 2*x7*x8 - 2*x7*x9^2 - 2*x7*x9 + 2*x8*x9 + 2*x8

def incidentGenerator10 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℂ) : ℂ :=
  -x0^2*x3^2 - x0*x1*x3^2 + x0*x1*x5^2 - x0*x1 - 4*x0*x2*x3*x5 - 2*x0*x2*x5^2 - 2*x0*x2*x5*x7 -
    2*x0*x2*x5*x9 - 2*x0*x2*x5 - 2*x0*x2*x7 - 2*x0*x3^2*x4 - 4*x0*x3*x4*x5 - 2*x0*x3*x4*x7 -
    2*x0*x3*x4*x9 - 2*x0*x3*x4 - 2*x0*x3*x5*x6 - 2*x0*x3*x5*x8 + 2*x0*x3*x5 - 2*x0*x3*x6 +
    2*x0*x3*x7 + 2*x0*x3*x9 + 2*x0*x3 + x0*x5^2 + 2*x0*x5*x7 + 2*x0*x5*x9 + 2*x0*x5 + 2*x0*x7*x9 +
    2*x0*x7 + x0*x9^2 + 2*x0*x9 + x0 - x1^2 - 2*x1*x2*x7 - 2*x1*x3*x6 + 2*x1*x4*x9 + 2*x1*x5*x8 -
    x1*x7^2 + x1*x9^2 - x1 + x2^2*x9^2 - 2*x2^2*x9 + x2^2 + 4*x2*x3*x8*x9 - 4*x2*x3*x8 +
    2*x2*x4*x7*x9 - 2*x2*x4*x7 - 2*x2*x4*x9 + 2*x2*x4 + 2*x2*x5*x6*x9 - 2*x2*x5*x6 + 2*x2*x5*x7*x8 -
    2*x2*x5*x8 - 2*x2*x6*x9 + 2*x2*x6 - 2*x2*x7*x8 - 2*x2*x7*x9 - 2*x2*x7 - 4*x2*x8*x9 + x3^2*x8^2 +
    2*x3*x4*x6*x9 - 2*x3*x4*x6 + 2*x3*x4*x7*x8 - 2*x3*x4*x8 + 2*x3*x5*x6*x8 - 2*x3*x6*x8 -
    2*x3*x6*x9 - 2*x3*x6 - 2*x3*x7*x8 - 2*x3*x8^2 + x4^2*x7^2 - 2*x4^2*x7 + x4^2 + 4*x4*x5*x6*x7 -
    4*x4*x5*x6 - 4*x4*x6*x7 - 2*x4*x6*x9 - 2*x4*x7*x8 - 2*x4*x7*x9 + 2*x4*x8 + x5^2*x6^2 - 2*x5*x6^2
    - 2*x5*x6*x8 - 2*x5*x6*x9 - 2*x5*x7*x8 + x6^2 - 4*x6*x7*x9 + 2*x6*x8 - 2*x6*x9^2 - 2*x6*x9 -
    2*x7^2*x8 - x7^2 - 4*x7*x8*x9 - 2*x7*x8 + x8^2

def incidentGenerator11 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℂ) : ℂ :=
  -2*x0^2*x2*x3 - 2*x0*x1*x2*x3 + 2*x0*x1*x4*x5 - 2*x0*x2^2*x5 - 4*x0*x2*x3*x4 - 4*x0*x2*x4*x5 -
    2*x0*x2*x4*x7 - 2*x0*x2*x4*x9 - 2*x0*x2*x4 - 2*x0*x2*x5*x6 - 2*x0*x2*x5*x8 + 2*x0*x2*x5 -
    2*x0*x2*x6 + 2*x0*x2*x7 + 2*x0*x2*x9 + 2*x0*x2 - 2*x0*x3*x4^2 - 2*x0*x3*x4*x6 - 2*x0*x3*x4*x8 +
    2*x0*x3*x4 + 2*x0*x3*x6 + 2*x0*x3*x8 + 2*x0*x4*x5 + 2*x0*x4*x7 + 2*x0*x4*x9 + 2*x0*x4 +
    2*x0*x5*x6 + 2*x0*x5*x8 + 2*x0*x6*x9 + 2*x0*x6 + 2*x0*x7*x8 + 2*x0*x8*x9 + 2*x0*x8 - 2*x1*x2*x6
    + 2*x1*x4*x8 - 2*x1*x6*x7 + 2*x1*x8*x9 + 2*x2^2*x8*x9 - 2*x2^2*x8 + 2*x2*x3*x8^2 + 2*x2*x4*x6*x9
    - 2*x2*x4*x6 + 2*x2*x4*x7*x8 - 2*x2*x4*x8 + 2*x2*x5*x6*x8 - 2*x2*x6*x8 - 2*x2*x6*x9 - 2*x2*x6 -
    2*x2*x7*x8 - 2*x2*x8^2 + 2*x3*x4*x6*x8 - 2*x3*x6*x8 + 2*x4^2*x6*x7 - 2*x4^2*x6 + 2*x4*x5*x6^2 -
    2*x4*x6^2 - 2*x4*x6*x8 - 2*x4*x6*x9 - 2*x4*x7*x8 - 2*x5*x6*x8 - 2*x6^2*x9 - 4*x6*x7*x8 - 2*x6*x7
    - 4*x6*x8*x9 - 2*x6*x8 - 2*x7*x8^2

def incidentGenerator12 (x0 x1 x2 _x3 x4 _x5 x6 _x7 x8 _x9 : ℂ) : ℂ :=
  -x0^2*x1 - x0^2*x2^2 - x0*x1^2 - x0*x1*x2^2 + x0*x1*x4^2 - x0*x1 - 2*x0*x2^2*x4 - 2*x0*x2*x4^2 -
    2*x0*x2*x4*x6 - 2*x0*x2*x4*x8 + 2*x0*x2*x4 + 2*x0*x2*x6 + 2*x0*x2*x8 + x0*x4^2 + 2*x0*x4*x6 +
    2*x0*x4*x8 + 2*x0*x6*x8 + x0*x8^2 - x1*x6^2 + x1*x8^2 + x2^2*x8^2 + 2*x2*x4*x6*x8 - 2*x2*x6*x8 +
    x4^2*x6^2 - 2*x4*x6*x8 - 2*x6^2*x8 - x6^2 - 2*x6*x8^2

def incidentH (x3 x5 x7 x9 : ℂ) : Fin 4 × Fin 4 → ℂ :=
  fun p => (!![0,1,x3,x5; 1,0,x7,x9; x3,x7,0,-1-x3-x5-x7-x9;
    x5,x9,-1-x3-x5-x7-x9,0] : Matrix (Fin 4) (Fin 4) ℂ) p.1 p.2

def incidentV (x0 x1 x2 x4 x6 x8 : ℂ) : Fin 4 × Fin 4 → ℂ :=
  fun p => (!![1,0,x2,x4; 0,x0,x6,x8; x2,x6,x1,-x2-x4-x6-x8;
    x4,x8,-x2-x4-x6-x8,-1-x0-x1] : Matrix (Fin 4) (Fin 4) ℂ) p.1 p.2

set_option maxHeartbeats 8000000 in
lemma permanent_incident_chart (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 a z : ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*incidentH x3 x5 x7 x9 (i,j)+z*incidentV x0 x1 x2 x4 x6 x8 (i,j)) =
    24 + incidentGenerator1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * a^2 +
      incidentGenerator2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * a * z +
      incidentGenerator3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * z^2 +
      incidentGenerator4 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * a^3 +
      incidentGenerator5 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * a^2 * z +
      incidentGenerator6 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * a * z^2 +
      incidentGenerator7 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * z^3 +
      incidentGenerator8 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * a^4 +
      incidentGenerator9 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * a^3 * z +
      incidentGenerator10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * a^2 * z^2 +
      incidentGenerator11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * a * z^3 +
      incidentGenerator12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * z^4 := by
  rw [permanent_four]
  simp [incidentH,incidentV]
  dsimp [incidentGenerator1,incidentGenerator2,incidentGenerator3,incidentGenerator4,incidentGenerator5,incidentGenerator6,incidentGenerator7,incidentGenerator8,incidentGenerator9,incidentGenerator10,incidentGenerator11,incidentGenerator12]
  ring

lemma incident_bivariate_coefficients (g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 : ℂ)
    (hp : ∀ a z : ℂ,
      g1*a^2+g2*a*z+g3*z^2+g4*a^3+g5*a^2*z+g6*a*z^2+g7*z^3+
        g8*a^4+g9*a^3*z+g10*a^2*z^2+g11*a*z^3+g12*z^4=0) :
    g1=0 ∧ g2=0 ∧ g3=0 ∧ g4=0 ∧ g5=0 ∧ g6=0 ∧ g7=0 ∧
      g8=0 ∧ g9=0 ∧ g10=0 ∧ g11=0 ∧ g12=0 := by
  have hd (z : ℂ) : g1+g2*z+g3*z^2=0 ∧
      g4+g5*z+g6*z^2+g7*z^3=0 ∧
      g8+g9*z+g10*z^2+g11*z^3+g12*z^4=0 := by
    have h := quartic_all_coefficients 0 (g1+g2*z+g3*z^2)
      (g4+g5*z+g6*z^2+g7*z^3) (g8+g9*z+g10*z^2+g11*z^3+g12*z^4) (by
        intro t
        have ht := hp t (t*z)
        linear_combination ht)
    exact h.2
  have h1 : g1=0 := by simpa using (hd 0).1
  have h4 : g4=0 := by simpa using (hd 0).2.1
  have h8 : g8=0 := by simpa using (hd 0).2.2
  obtain ⟨h2,h3,_,_⟩ := quartic_all_coefficients g2 g3 0 0 (by
    intro z
    linear_combination (hd z).1-h1)
  obtain ⟨h5,h6,h7,_⟩ := quartic_all_coefficients g5 g6 g7 0 (by
    intro z
    linear_combination (hd z).2.1-h4)
  obtain ⟨h9,h10,h11,h12⟩ := quartic_all_coefficients g9 g10 g11 g12 (by
    intro z
    linear_combination (hd z).2.2-h8)
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩

set_option maxHeartbeats 4000000 in
lemma incident_level_tangent (T : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, T (i,j)=T (j,i))
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+z*T (i,j))=24) :
    T (0,0)+2*T (0,1)+2*T (0,2)+2*T (0,3)+T (1,1)+
      2*T (1,2)+2*T (1,3)+T (2,2)+2*T (2,3)+T (3,3)=0 := by
  have h1 := hp 1
  have h2 := hp (-1)
  have h3 := hp 2
  have h4 := hp (-2)
  rw [permanent_four] at h1 h2 h3 h4
  simp only [Matrix.of_apply,hs 1 0,hs 2 0,hs 3 0,hs 2 1,hs 3 1,hs 3 2] at h1 h2 h3 h4
  linear_combination (1/9:ℂ)*h1-(1/9:ℂ)*h2-(1/72:ℂ)*h3+(1/72:ℂ)*h4

lemma normalized_incident_reconstruction (H V : Fin 4 × Fin 4 → ℂ)
    (hHs : ∀ i j : Fin 4, H (i,j)=H (j,i))
    (hVs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hHz : ∀ i : Fin 4, H (i,i)=0)
    (hVtrace : (∑ i : Fin 4, V (i,i))=0)
    (hV00 : V (0,0)=1) (hH01 : H (0,1)=1) (hV01 : V (0,1)=0)
    (hp : ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*H (i,j)+z*V (i,j))=24) :
    H (2,3)=-1-H (0,2)-H (0,3)-H (1,2)-H (1,3) ∧
    V (2,3)=-V (0,2)-V (0,3)-V (1,2)-V (1,3) ∧
    V (3,3)=-1-V (1,1)-V (2,2) := by
  have hHt := incident_level_tangent H hHs (by intro z; simpa using hp z 0)
  have hVt := incident_level_tangent V hVs (by intro z; simpa using hp 0 z)
  have htr : V (0,0)+V (1,1)+V (2,2)+V (3,3)=0 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hVtrace
  simp only [hHz,hH01] at hHt
  rw [hV01] at hVt
  refine ⟨?_,?_,?_⟩
  · linear_combination hHt/2
  · linear_combination hVt/2-htr/2
  · rw [hV00] at htr
    linear_combination htr

set_option maxHeartbeats 2000000 in
lemma normalized_incident_generators_zero (H V : Fin 4 × Fin 4 → ℂ)
    (hHs : ∀ i j : Fin 4, H (i,j)=H (j,i))
    (hVs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hHz : ∀ i : Fin 4, H (i,i)=0)
    (hVtrace : (∑ i : Fin 4, V (i,i))=0)
    (hV00 : V (0,0)=1) (hH01 : H (0,1)=1) (hV01 : V (0,1)=0)
    (hp : ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*H (i,j)+z*V (i,j))=24) :
    incidentGenerator1 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator2 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator3 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator4 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator5 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator6 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator7 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator8 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator9 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator10 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator11 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator12 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 := by
  obtain ⟨hH23,hV23,hV33⟩ := normalized_incident_reconstruction
    H V hHs hVs hHz hVtrace hV00 hH01 hV01 hp
  have hH : H=incidentH (H (0,2)) (H (0,3)) (H (1,2)) (H (1,3)) := by
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [incidentH,hHz,hH01,hH23,hHs 1 0,hHs 2 0,hHs 3 0,hHs 2 1,hHs 3 1,hHs 3 2]
  have hV : V=incidentV (V (1,1)) (V (2,2)) (V (0,2)) (V (0,3))
      (V (1,2)) (V (1,3)) := by
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [incidentV,hV00,hV01,hV23,hV33,hVs 1 0,hVs 2 0,hVs 3 0,hVs 2 1,hVs 3 1,hVs 3 2]
  apply incident_bivariate_coefficients
  intro a z
  have h := hp a z
  rw [hH,hV,permanent_incident_chart] at h
  linear_combination h

end PEqualNP.Outside.L_gct_231
