import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

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

end PEqualNP.Outside.L_gct_231
