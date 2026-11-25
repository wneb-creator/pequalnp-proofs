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

end PEqualNP.Outside.L_gct_231
