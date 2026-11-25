import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import PEqualNP.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic.FinCases
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Field.ZMod

namespace PEqualNP.Outside.L_gct_231_aux

lemma sum_perm_succ {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, f σ = ∑ p : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n), f (Equiv.Perm.decomposeFin.symm (p, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma perm4 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix.permanent M =
    M 0 0 * M 1 1 * M 2 2 * M 3 3 + M 0 0 * M 1 1 * M 3 2 * M 2 3 + M 0 0 * M 2 1 * M 1 2 * M 3 3
  + M 0 0 * M 2 1 * M 3 2 * M 1 3 + M 0 0 * M 3 1 * M 1 2 * M 2 3 + M 0 0 * M 3 1 * M 2 2 * M 1 3
  + M 1 0 * M 0 1 * M 2 2 * M 3 3 + M 1 0 * M 0 1 * M 3 2 * M 2 3 + M 1 0 * M 2 1 * M 0 2 * M 3 3
  + M 1 0 * M 2 1 * M 3 2 * M 0 3 + M 1 0 * M 3 1 * M 0 2 * M 2 3 + M 1 0 * M 3 1 * M 2 2 * M 0 3
  + M 2 0 * M 0 1 * M 1 2 * M 3 3 + M 2 0 * M 0 1 * M 3 2 * M 1 3 + M 2 0 * M 1 1 * M 0 2 * M 3 3
  + M 2 0 * M 1 1 * M 3 2 * M 0 3 + M 2 0 * M 3 1 * M 0 2 * M 1 3 + M 2 0 * M 3 1 * M 1 2 * M 0 3
  + M 3 0 * M 0 1 * M 1 2 * M 2 3 + M 3 0 * M 0 1 * M 2 2 * M 1 3 + M 3 0 * M 1 1 * M 0 2 * M 2 3
  + M 3 0 * M 1 1 * M 2 2 * M 0 3 + M 3 0 * M 2 1 * M 0 2 * M 1 3 + M 3 0 * M 2 1 * M 1 2 * M 0 3 := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring


theorem range_witness
    (F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ))
    (hi : Function.Injective F)
    (hs : ∀ v, ∀ i j : Fin 4, F v (i, j) = F v (j, i))
    (hp : ∀ v, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + F v (i, j)) = 24) :
    ∃ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ), Module.finrank ℂ L = 3 ∧
      (∀ t ∈ L, ∀ i j : Fin 4, t (i, j) = t (j, i)) ∧
      ∀ t ∈ L, Matrix.permanent
        (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + t (i, j)) = 24 := by
  refine ⟨LinearMap.range F, ?_, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hi]
    simp
  · rintro t ⟨v, rfl⟩ i j
    exact hs v i j
  · rintro t ⟨v, rfl⟩
    exact hp v

theorem injective_of_coordinates
    (F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ))
    (p : Fin 3 → Fin 4 × Fin 4)
    (h : ∀ v k, F v (p k) = v k) : Function.Injective F := by
  intro v w hvw
  funext k
  have he := congrFun hvw (p k)
  simpa only [h] using he

theorem symmetric_permanent
    (a b c d e f g h i j : ℂ) :
    Matrix.permanent (!![a, e, f, g; e, b, h, i; f, h, c, j; g, i, j, d]) =
      a*b*c*d + a*b*j^2 + a*c*i^2 + a*d*h^2 + b*c*g^2 + b*d*f^2 + c*d*e^2 +
      2*a*h*i*j + 2*b*f*g*j + 2*c*e*g*i + 2*d*e*f*h +
      e^2*j^2 + f^2*i^2 + g^2*h^2 + 2*e*f*i*j + 2*e*g*h*j + 2*f*g*h*i := by
  rw [perm4]
  simp +decide [Matrix.of_apply]
  ring


theorem diagonal_entries_zero (a b c d : ℂ)
    (h : ∀ z : ℂ, Matrix.permanent
      (!![1+z*a, 1, 1, 1; 1, 1+z*b, 1, 1; 1, 1, 1+z*c, 1; 1, 1, 1, 1+z*d]) = 24) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  have hm2 := h (-2)
  rw [symmetric_permanent] at h1 hm1 h2 hm2
  have he1 : a+b+c+d = 0 := by
    linear_combination (1/9 : ℂ)*h1 - (1/9 : ℂ)*hm1 - (1/72 : ℂ)*h2 + (1/72 : ℂ)*hm2
  have he2 : a*b+a*c+a*d+b*c+b*d+c*d = 0 := by
    linear_combination (1/3 : ℂ)*h1 + (1/3 : ℂ)*hm1 - (1/48 : ℂ)*h2 - (1/48 : ℂ)*hm2
  have he3 : a*b*c+a*b*d+a*c*d+b*c*d = 0 := by
    linear_combination -(1/6 : ℂ)*h1 + (1/6 : ℂ)*hm1 + (1/12 : ℂ)*h2 - (1/12 : ℂ)*hm2
  have he4 : a*b*c*d = 0 := by
    linear_combination -(1/6 : ℂ)*h1 - (1/6 : ℂ)*hm1 + (1/24 : ℂ)*h2 + (1/24 : ℂ)*hm2
  have ha : a^4 = 0 := by linear_combination a^3*he1 - a^2*he2 + a*he3 - he4
  have hb : b^4 = 0 := by linear_combination b^3*he1 - b^2*he2 + b*he3 - he4
  have hc : c^4 = 0 := by linear_combination c^3*he1 - c^2*he2 + c*he3 - he4
  have hd : d^4 = 0 := by linear_combination d^3*he1 - d^2*he2 + d*he3 - he4
  exact ⟨by simpa using ha, by simpa using hb, by simpa using hc, by simpa using hd⟩

theorem diagonal_rigid (d : Fin 4 → ℂ)
    (h : ∀ z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + z * if i = j then d i else 0) = 24) :
    d = 0 := by
  have hscalar : ∀ z : ℂ, Matrix.permanent
      (!![1+z*d 0, 1, 1, 1; 1, 1+z*d 1, 1, 1;
          1, 1, 1+z*d 2, 1; 1, 1, 1, 1+z*d 3]) = 24 := by
    intro z
    convert h z using 1
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.of_apply]
  obtain ⟨h0, h1, h2, h3⟩ := diagonal_entries_zero (d 0) (d 1) (d 2) (d 3) hscalar
  funext i
  fin_cases i <;> assumption


theorem off_diagonal_determines (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hp : ∀ t ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + t (i, j)) = 24)
    (t u : Fin 4 × Fin 4 → ℂ) (ht : t ∈ L) (hu : u ∈ L)
    (hoff : ∀ i j : Fin 4, i ≠ j → t (i,j) = u (i,j)) : t = u := by
  have hd : (fun i : Fin 4 => t (i,i) - u (i,i)) = 0 := by
    apply diagonal_rigid
    intro z
    convert hp (z • (t-u)) (L.smul_mem z (L.sub_mem ht hu)) using 1
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.of_apply]
    · simp [Matrix.of_apply, hij, hoff i j hij]
  funext p
  rcases p with ⟨i,j⟩
  by_cases hij : i = j
  · subst j
    exact sub_eq_zero.mp (congrFun hd i)
  · exact hoff i j hij

noncomputable def offDiagonal : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) where
  toFun t := ![t (0,1), t (0,2), t (0,3), t (1,2), t (1,3), t (2,3)]
  map_add' t u := by
    funext k
    fin_cases k <;> rfl
  map_smul' z t := by
    funext k
    fin_cases k <;> rfl

theorem offDiagonal_injective (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hs : ∀ t ∈ L, ∀ i j : Fin 4, t (i,j) = t (j,i))
    (hp : ∀ t ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + t (i, j)) = 24) :
    Function.Injective (fun t : L => offDiagonal t.val) := by
  intro t u h
  have h01 := congrFun h 0
  have h02 := congrFun h 1
  have h03 := congrFun h 2
  have h12 := congrFun h 3
  have h13 := congrFun h 4
  have h23 := congrFun h 5
  simp [offDiagonal] at h01 h02 h03 h12 h13 h23
  apply Subtype.ext
  apply off_diagonal_determines L hp t.val u.val t.property u.property
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try first | exact (hij rfl).elim | assumption
  all_goals rw [hs t.val t.property, hs u.val u.property]
  all_goals assumption


theorem select_three_coordinates
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (F : V →ₗ[ℂ] (Fin 6 → ℂ)) (hF : Function.Injective F)
    (hdim : Module.finrank ℂ V = 3) :
    ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
      Function.Bijective (fun v : V => fun k : Fin 3 => F v (pick k)) := by
  classical
  let φ : Fin 6 → Module.Dual ℂ V := fun i => (LinearMap.proj i).comp F
  have hspan : Submodule.span ℂ (Set.range φ) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro v hv
    have hnonzero : F v ≠ 0 := by
      intro hz
      apply hv
      apply hF
      simpa using hz
    obtain ⟨i, hi⟩ : ∃ i : Fin 6, F v i ≠ 0 := by
      by_contra! h
      exact hnonzero (funext h)
    exact ⟨φ i, ⟨i, rfl⟩, hi⟩
  let S := (linearIndepOn_empty ℂ id).extend (Set.empty_subset (Set.range φ))
  let b0 : Module.Basis S ℂ (Module.Dual ℂ V) := Module.Basis.ofSpan hspan.ge
  let : Finite S := basis_finite_of_finite_spans (Set.finite_range φ) hspan b0
  let : Fintype S := Fintype.ofFinite S
  have hc : Fintype.card S = 3 := by
    rw [← Module.finrank_eq_card_basis b0, Subspace.dual_finrank_eq, hdim]
  let b : Module.Basis (Fin 3) ℂ (Module.Dual ℂ V) :=
    b0.reindex (Fintype.equivFinOfCardEq hc)
  have hb : ∀ k : Fin 3, ∃ j : Fin 6, φ j = b k := by
    intro k
    apply Module.Basis.ofSpan_subset hspan.ge
    exact ⟨(Fintype.equivFinOfCardEq hc).symm k,
      (Module.Basis.reindex_apply b0 (Fintype.equivFinOfCardEq hc) k).symm⟩
  choose pick hpick using hb
  have hpick_inj : Function.Injective pick := by
    intro i j hij
    apply b.linearIndependent.injective
    rw [← hpick i, ← hpick j, hij]
  let G : V →ₗ[ℂ] (Fin 3 → ℂ) := LinearMap.pi fun k => φ (pick k)
  have hG : Function.Injective G := by
    intro v w hvw
    apply (Module.evalEquiv ℂ V).injective
    apply b.ext
    intro k
    change b k v = b k w
    rw [← hpick k]
    exact congrFun hvw k
  refine ⟨pick, hpick_inj, ?_⟩
  change Function.Bijective G
  refine ⟨hG, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simpa using hdim)).mp hG


theorem candidate_three_coordinate_chart
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hdim : Module.finrank ℂ L = 3)
    (hs : ∀ t ∈ L, ∀ i j : Fin 4, t (i,j) = t (j,i))
    (hp : ∀ t ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + t (i, j)) = 24) :
    ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
      Function.Bijective (fun t : L => fun k : Fin 3 => offDiagonal t.val (pick k)) := by
  exact select_three_coordinates (offDiagonal.comp L.subtype)
    (offDiagonal_injective L hs hp) hdim

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem total_entry_sum_zero (t : Fin 4 × Fin 4 → ℂ)
    (h : ∀ z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + z * t (i,j)) = 24) :
    ∑ i : Fin 4, ∑ j : Fin 4, t (i,j) = 0 := by
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  have hm2 := h (-2)
  rw [perm4] at h1 hm1 h2 hm2
  simp only [Matrix.of_apply] at h1 hm1 h2 hm2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, show (2 : Fin 3).succ = (3 : Fin 4) from rfl]
  linear_combination (1/9 : ℂ)*h1 - (1/9 : ℂ)*hm1 - (1/72 : ℂ)*h2 + (1/72 : ℂ)*hm2

theorem submodule_total_entry_sum_zero
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hp : ∀ t ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + t (i,j)) = 24)
    (t : Fin 4 × Fin 4 → ℂ) (ht : t ∈ L) :
    ∑ i : Fin 4, ∑ j : Fin 4, t (i,j) = 0 := by
  apply total_entry_sum_zero
  intro z
  simpa only [Pi.smul_apply, smul_eq_mul] using hp (z • t) (L.smul_mem z ht)


theorem diagonal33_of_total_entry_sum_zero
    (t : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, t (i,j) = t (j,i))
    (hsum : ∑ i : Fin 4, ∑ j : Fin 4, t (i,j) = 0) :
    t (3,3) = -(t (0,0) + t (1,1) + t (2,2) +
      2 * (t (0,1) + t (0,2) + t (0,3) + t (1,2) + t (1,3) + t (2,3))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, show (2 : Fin 3).succ = (3 : Fin 4) from rfl] at hsum
  rw [hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2] at hsum
  linear_combination hsum

def edgeEnds : Fin 6 → Fin 4 × Fin 4 :=
  ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

def canonicalEdges : Fin 3 → Fin 3 → Fin 6 :=
  ![![0,1,2], ![0,1,3], ![0,3,5]]

def SameUnorderedEnds (a b : Fin 4 × Fin 4) : Prop :=
  (a.1 = b.1 ∧ a.2 = b.2) ∨ (a.1 = b.2 ∧ a.2 = b.1)

noncomputable def orbitVertex : Fin 24 → Equiv.Perm (Fin 4) :=
  ![
    Equiv.ofBijective (![0, 1, 2, 3] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![0, 1, 3, 2] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![0, 2, 1, 3] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![0, 2, 3, 1] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![0, 3, 1, 2] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![0, 3, 2, 1] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![1, 0, 2, 3] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![1, 0, 3, 2] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![1, 2, 0, 3] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![1, 2, 3, 0] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![1, 3, 0, 2] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![1, 3, 2, 0] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![2, 0, 1, 3] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![2, 0, 3, 1] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![2, 1, 0, 3] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![2, 1, 3, 0] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![2, 3, 0, 1] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![2, 3, 1, 0] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![3, 0, 1, 2] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![3, 0, 2, 1] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![3, 1, 0, 2] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![3, 1, 2, 0] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![3, 2, 0, 1] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![3, 2, 1, 0] : Fin 4 → Fin 4) (by decide)]

noncomputable def orbitCoordinate : Fin 6 → Equiv.Perm (Fin 3) :=
  ![
    Equiv.ofBijective (![0, 1, 2] : Fin 3 → Fin 3) (by decide),
    Equiv.ofBijective (![0, 2, 1] : Fin 3 → Fin 3) (by decide),
    Equiv.ofBijective (![1, 0, 2] : Fin 3 → Fin 3) (by decide),
    Equiv.ofBijective (![1, 2, 0] : Fin 3 → Fin 3) (by decide),
    Equiv.ofBijective (![2, 0, 1] : Fin 3 → Fin 3) (by decide),
    Equiv.ofBijective (![2, 1, 0] : Fin 3 → Fin 3) (by decide)]

def orbitWitness : Fin 6 → Fin 6 → Fin 6 → Fin 24 × Fin 6 × Fin 3 :=
  ![
    ![![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)], ![(0,0,0), (0,0,0), (0,0,0), (0,0,1), (8,2,2), (6,0,2)], ![(0,0,0), (0,1,0), (0,0,0), (9,2,2), (1,0,1), (7,0,2)], ![(0,0,0), (0,1,1), (9,4,2), (0,0,0), (6,0,0), (0,0,2)], ![(0,0,0), (8,4,2), (1,1,1), (6,1,0), (0,0,0), (1,0,2)], ![(0,0,0), (6,1,2), (7,1,2), (0,1,2), (1,1,2), (0,0,0)]],
    ![![(0,0,0), (0,0,0), (0,2,0), (0,2,1), (8,0,2), (6,2,2)], ![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)], ![(0,4,0), (0,0,0), (0,0,0), (11,2,2), (10,0,2), (4,0,1)], ![(0,4,1), (0,0,0), (11,4,2), (0,0,0), (2,0,2), (8,0,0)], ![(8,1,2), (0,0,0), (10,1,2), (2,1,2), (0,0,0), (4,1,2)], ![(6,4,2), (0,0,0), (4,1,1), (8,1,0), (4,0,2), (0,0,0)]],
    ![![(0,0,0), (0,3,0), (0,0,0), (9,0,2), (1,2,1), (7,2,2)], ![(0,5,0), (0,0,0), (0,0,0), (11,0,2), (10,2,2), (4,2,1)], ![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)], ![(9,1,2), (11,1,2), (0,0,0), (0,0,0), (3,1,2), (5,1,2)], ![(1,4,1), (10,4,2), (0,0,0), (3,0,2), (0,0,0), (9,0,0)], ![(7,4,2), (4,4,1), (0,0,0), (5,0,2), (9,1,0), (0,0,0)]],
    ![![(0,0,0), (0,3,1), (9,5,2), (0,0,0), (6,2,0), (0,2,2)], ![(0,5,1), (0,0,0), (11,5,2), (0,0,0), (2,2,2), (8,2,0)], ![(9,3,2), (11,3,2), (0,0,0), (0,0,0), (3,3,2), (5,3,2)], ![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)], ![(6,4,0), (2,4,2), (3,5,2), (0,0,0), (0,0,0), (18,0,1)], ![(0,4,2), (8,4,0), (5,5,2), (0,0,0), (18,1,1), (0,0,0)]],
    ![![(0,0,0), (8,5,2), (1,3,1), (6,3,0), (0,0,0), (1,2,2)], ![(8,3,2), (0,0,0), (10,3,2), (2,3,2), (0,0,0), (4,3,2)], ![(1,5,1), (10,5,2), (0,0,0), (3,2,2), (0,0,0), (9,2,0)], ![(6,5,0), (2,5,2), (3,4,2), (0,0,0), (0,0,0), (18,2,1)], ![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)], ![(1,4,2), (4,5,2), (9,4,0), (18,4,1), (0,0,0), (0,0,0)]],
    ![![(0,0,0), (6,3,2), (7,3,2), (0,3,2), (1,3,2), (0,0,0)], ![(6,5,2), (0,0,0), (4,3,1), (8,3,0), (4,2,2), (0,0,0)], ![(7,5,2), (4,5,1), (0,0,0), (5,2,2), (9,3,0), (0,0,0)], ![(0,5,2), (8,5,0), (5,4,2), (0,0,0), (18,3,1), (0,0,0)], ![(1,5,2), (4,4,2), (9,5,0), (18,5,1), (0,0,0), (0,0,0)], ![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)]]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem orbitWitness_valid :
    ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c → ∀ k : Fin 3,
      let w := orbitWitness a b c
      let p := orbitVertex w.1
      let q := orbitCoordinate w.2.1
      SameUnorderedEnds
        (p (edgeEnds (![a,b,c] (q k))).1, p (edgeEnds (![a,b,c] (q k))).2)
        (edgeEnds (canonicalEdges w.2.2 k)) := by
  unfold SameUnorderedEnds
  decide

theorem three_edge_orbits :
    ∀ pick : Fin 3 → Fin 6, Function.Injective pick →
      ∃ p : Equiv.Perm (Fin 4), ∃ q : Equiv.Perm (Fin 3), ∃ kind : Fin 3,
        ∀ k : Fin 3, SameUnorderedEnds
          (p (edgeEnds (pick (q k))).1, p (edgeEnds (pick (q k))).2)
          (edgeEnds (canonicalEdges kind k)) := by
  intro pick hi
  let w := orbitWitness (pick 0) (pick 1) (pick 2)
  refine ⟨orbitVertex w.1, orbitCoordinate w.2.1, w.2.2, ?_⟩
  have h01 : pick 0 ≠ pick 1 := fun h => by have := hi h; contradiction
  have h02 : pick 0 ≠ pick 2 := fun h => by have := hi h; contradiction
  have h12 : pick 1 ≠ pick 2 := fun h => by have := hi h; contradiction
  have hv : ![pick 0, pick 1, pick 2] = pick := by
    funext k
    fin_cases k <;> rfl
  intro k
  simpa only [hv] using orbitWitness_valid (pick 0) (pick 1) (pick 2) h01 h02 h12 k


noncomputable def relabel (p : Equiv.Perm (Fin 4)) :
    (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun t ij := t (p.symm ij.1, p.symm ij.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem relabel_symmetric (p : Equiv.Perm (Fin 4))
    (t : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, t (i,j) = t (j,i)) :
    ∀ i j : Fin 4, relabel p t (i,j) = relabel p t (j,i) := by
  intro i j
  exact hs (p.symm i) (p.symm j)

theorem relabel_permanent (p : Equiv.Perm (Fin 4))
    (t : Fin 4 × Fin 4 → ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + relabel p t (i,j)) =
      Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + t (i,j)) := by
  let M : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun i j => (1 : ℂ) + t (i,j)
  change (M.submatrix p.symm p.symm).permanent = M.permanent
  calc
    _ = ((M.submatrix p.symm id).submatrix id p.symm).permanent := rfl
    _ = (M.submatrix p.symm id).permanent := Matrix.permanent_permute_rows p.symm _
    _ = M.permanent := Matrix.permanent_permute_cols p.symm M

theorem relabel_injective (p : Equiv.Perm (Fin 4)) : Function.Injective (relabel p) := by
  intro t u h
  funext ij
  have he := congrFun h (p ij.1, p ij.2)
  simpa [relabel] using he

theorem offDiagonal_apply (t : Fin 4 × Fin 4 → ℂ) (k : Fin 6) :
    offDiagonal t k = t (edgeEnds k) := by
  fin_cases k <;> rfl

theorem relabel_matches_edge (p : Equiv.Perm (Fin 4))
    (t : Fin 4 × Fin 4 → ℂ) (hs : ∀ i j : Fin 4, t (i,j) = t (j,i))
    (a b : Fin 4 × Fin 4)
    (h : SameUnorderedEnds (p a.1, p a.2) b) :
    relabel p t b = t a := by
  change t (p.symm b.1, p.symm b.2) = t a
  rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · rw [← h1, ← h2]
    simp
  · rw [← h2, ← h1]
    simpa using hs a.2 a.1

theorem parameterize_chart_data
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hs : ∀ t ∈ L, ∀ i j : Fin 4, t (i,j) = t (j,i))
    (hp : ∀ t ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + t (i,j)) = 24)
    (pick : Fin 3 → Fin 6)
    (hbij : Function.Bijective (fun t : L => fun k : Fin 3 => offDiagonal t.val (pick k)))
    (p : Equiv.Perm (Fin 4)) (q : Equiv.Perm (Fin 3)) (kind : Fin 3)
    (horbit : ∀ k : Fin 3, SameUnorderedEnds
      (p (edgeEnds (pick (q k))).1, p (edgeEnds (pick (q k))).2)
      (edgeEnds (canonicalEdges kind k))) :
    ∃ F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ),
      Function.Injective F ∧
      (∀ x, ∀ i j : Fin 4, F x (i,j) = F x (j,i)) ∧
      (∀ x, Matrix.permanent
        (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + F x (i,j)) = 24) ∧
      ∀ x k, F x (edgeEnds (canonicalEdges kind k)) = x k := by
  let G : L →ₗ[ℂ] (Fin 3 → ℂ) := LinearMap.pi fun k =>
    (LinearMap.proj (pick (q k))).comp (offDiagonal.comp L.subtype)
  have hG : Function.Bijective G := by
    constructor
    · intro t u h
      apply hbij.1
      funext k
      have he := congrFun h (q.symm k)
      simpa [G] using he
    · intro x
      obtain ⟨t, ht⟩ := hbij.2 (fun k => x (q.symm k))
      refine ⟨t, ?_⟩
      funext k
      have he := congrFun ht (q k)
      simpa [G] using he
  let e : L ≃ₗ[ℂ] (Fin 3 → ℂ) := LinearEquiv.ofBijective G hG
  let F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) :=
    (relabel p).comp (L.subtype.comp e.symm.toLinearMap)
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · exact (relabel_injective p).comp (Subtype.val_injective.comp e.symm.injective)
  · intro x i j
    exact relabel_symmetric p (e.symm x).val (hs _ (e.symm x).property) i j
  · intro x
    exact (relabel_permanent p (e.symm x).val).trans (hp _ (e.symm x).property)
  · intro x k
    change relabel p (e.symm x).val (edgeEnds (canonicalEdges kind k)) = x k
    rw [relabel_matches_edge p _ (hs _ (e.symm x).property) _ _ (horbit k)]
    have he := congrFun (e.apply_symm_apply x) k
    change offDiagonal (e.symm x).val (pick (q k)) = x k at he
    simpa only [offDiagonal_apply] using he


theorem candidate_canonical_parameterization
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hdim : Module.finrank ℂ L = 3)
    (hs : ∀ t ∈ L, ∀ i j : Fin 4, t (i,j) = t (j,i))
    (hp : ∀ t ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + t (i,j)) = 24) :
    ∃ kind : Fin 3, ∃ F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ),
      Function.Injective F ∧
      (∀ x, ∀ i j : Fin 4, F x (i,j) = F x (j,i)) ∧
      (∀ x, Matrix.permanent
        (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + F x (i,j)) = 24) ∧
      ∀ x k, F x (edgeEnds (canonicalEdges kind k)) = x k := by
  obtain ⟨pick, hpick, hbij⟩ := candidate_three_coordinate_chart L hdim hs hp
  obtain ⟨p,q,kind,horbit⟩ := three_edge_orbits pick hpick
  exact ⟨kind, parameterize_chart_data L hs hp pick hbij p q kind horbit⟩


noncomputable def parametricEntry
    (A : Fin 3 → Fin 4 × Fin 4 → ℂ) (i j : Fin 4) :
    MvPolynomial (Fin 3) ℂ :=
  1 + ∑ k : Fin 3, MvPolynomial.C (A k (i,j)) * MvPolynomial.X k

theorem eval_parametricEntry
    (A : Fin 3 → Fin 4 × Fin 4 → ℂ) (v : Fin 3 → ℂ) (i j : Fin 4) :
    MvPolynomial.eval v (parametricEntry A i j) =
      1 + ∑ k : Fin 3, A k (i,j) * v k := by
  simp [parametricEntry]

theorem polynomial_permanent_identity
    (A : Fin 3 → Fin 4 × Fin 4 → ℂ)
    (hp : ∀ v : Fin 3 → ℂ, Matrix.permanent
      (Matrix.of fun i j : Fin 4 => 1 + ∑ k : Fin 3, A k (i,j) * v k) = 24) :
    Matrix.permanent (Matrix.of (parametricEntry A)) =
      (24 : MvPolynomial (Fin 3) ℂ) := by
  apply MvPolynomial.funext
  intro v
  simpa [Matrix.permanent, Matrix.of_apply, parametricEntry] using hp v

theorem linear_map_coordinate_expansion
    (F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ)) (v : Fin 3 → ℂ) :
    F v = ∑ k : Fin 3, v k • F (Pi.single k 1) := by
  have hv : v = ∑ k : Fin 3, v k • Pi.single k 1 := by
    funext j
    simp [Pi.single_apply]
  calc
    F v = F (∑ k : Fin 3, v k • Pi.single k 1) := congrArg F hv
    _ = ∑ k : Fin 3, v k • F (Pi.single k 1) := by simp

theorem linear_map_polynomial_permanent_identity
    (F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ))
    (hp : ∀ v : Fin 3 → ℂ, Matrix.permanent
      (Matrix.of fun i j : Fin 4 => 1 + F v (i,j)) = 24) :
    Matrix.permanent (Matrix.of (parametricEntry (fun k => F (Pi.single k 1)))) =
      (24 : MvPolynomial (Fin 3) ℂ) := by
  apply polynomial_permanent_identity
  intro v
  convert hp v using 1
  congr 1
  ext i j
  rw [linear_map_coordinate_expansion F v]
  simp [Finset.sum_apply, smul_eq_mul, mul_comm]


noncomputable def starAffine (a b c : ℂ) : MvPolynomial (Fin 3) ℂ :=
  1 + MvPolynomial.C a * MvPolynomial.X 0 +
    MvPolynomial.C b * MvPolynomial.X 1 + MvPolynomial.C c * MvPolynomial.X 2

noncomputable def fullStarMatrix (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ) :
    Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 3) ℂ) :=
  !![starAffine d0 d1 d2, starAffine 1 0 0, starAffine 0 1 0, starAffine 0 0 1;
    starAffine 1 0 0, starAffine d3 d4 d5, starAffine o0 o1 o2, starAffine o3 o4 o5;
    starAffine 0 1 0, starAffine o0 o1 o2, starAffine d6 d7 d8, starAffine o6 o7 o8;
    starAffine 0 0 1, starAffine o3 o4 o5, starAffine o6 o7 o8, starAffine (-(d0+d3+d6+2*(1+o0+o3+o6)))
      (-(d1+d4+d7+2*(1+o1+o4+o7)))
      (-(d2+d5+d8+2*(1+o2+o5+o8)))]



theorem linear_entry_expansion
    (F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ)) (v : Fin 3 → ℂ) (i j : Fin 4) :
    F v (i,j) = F (Pi.single 0 1) (i,j) * v 0 +
      F (Pi.single 1 1) (i,j) * v 1 + F (Pi.single 2 1) (i,j) * v 2 := by
  rw [linear_map_coordinate_expansion F v]
  simp [Fin.sum_univ_succ, smul_eq_mul]
  ring

noncomputable def starFromFamily
    (F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ)) :
    Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 3) ℂ) :=
  fullStarMatrix
    (F (Pi.single 0 1) (0,0)) (F (Pi.single 1 1) (0,0)) (F (Pi.single 2 1) (0,0))
    (F (Pi.single 0 1) (1,1)) (F (Pi.single 1 1) (1,1)) (F (Pi.single 2 1) (1,1))
    (F (Pi.single 0 1) (2,2)) (F (Pi.single 1 1) (2,2)) (F (Pi.single 2 1) (2,2))
    (F (Pi.single 0 1) (1,2)) (F (Pi.single 1 1) (1,2)) (F (Pi.single 2 1) (1,2))
    (F (Pi.single 0 1) (1,3)) (F (Pi.single 1 1) (1,3)) (F (Pi.single 2 1) (1,3))
    (F (Pi.single 0 1) (2,3)) (F (Pi.single 1 1) (2,3)) (F (Pi.single 2 1) (2,3))

set_option maxHeartbeats 4000000 in
theorem normalized_star_formal_identity
    (F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ))
    (hs : ∀ v, ∀ i j : Fin 4, F v (i,j) = F v (j,i))
    (hp : ∀ v, Matrix.permanent
      (Matrix.of fun i j : Fin 4 => (1 : ℂ) + F v (i,j)) = 24)
    (h01 : ∀ v, F v (0,1) = v 0)
    (h02 : ∀ v, F v (0,2) = v 1)
    (h03 : ∀ v, F v (0,3) = v 2) :
    Matrix.permanent (starFromFamily F) = (24 : MvPolynomial (Fin 3) ℂ) := by
  apply MvPolynomial.funext
  intro v
  have hsum : ∑ i : Fin 4, ∑ j : Fin 4, F v (i,j) = 0 := by
    apply total_entry_sum_zero
    intro z
    simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using hp (z • v)
  have hd := diagonal33_of_total_entry_sum_zero (F v) (hs v) hsum
  have he : (fun i j : Fin 4 => MvPolynomial.eval v (starFromFamily F i j)) =
      Matrix.of (fun i j : Fin 4 => (1 : ℂ) + F v (i,j)) := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [starFromFamily, fullStarMatrix, starAffine, h01, h02, h03,
      hs v 1 0, hs v 2 0, hs v 3 0, hs v 2 1, hs v 3 1, hs v 3 2, hd]
    all_goals simp only [linear_entry_expansion F v]
    all_goals ring
  have hh := congrArg Matrix.permanent he
  have hx := hh.trans (hp v)
  simpa [Matrix.permanent] using hx



theorem path_minor_strata
    (a b c d e f g h j : ℂ)
    (h0 : b * f - c * e = 0)
    (h1 : j = 0)
    (h2 : a = 0)
    (h3 : d * h - e * g = 0)
    (h4 : -c = 0)
    (h5 : e * j - f * h = 0)
    (h6 : a * e - b * d = 0)
    (h7 : -g = 0) :
    a = 0 ∧ c = 0 ∧ g = 0 ∧ j = 0 ∧
      ((d = 0 ∧ f = 0) ∨ (b = 0 ∧ h = 0)) := by
  have hc : c = 0 := neg_eq_zero.mp h4
  have hg : g = 0 := neg_eq_zero.mp h7
  have hbf : b * f = 0 := by simpa [hc] using h0
  have hdh : d * h = 0 := by simpa [hg] using h3
  have hfh : f * h = 0 := by linear_combination e * h1 - h5
  have hbd : b * d = 0 := by linear_combination e * h2 - h6
  refine ⟨h2, hc, hg, h1, ?_⟩
  by_cases hd : d = 0
  · by_cases hf : f = 0
    · exact Or.inl ⟨hd, hf⟩
    · exact Or.inr ⟨(mul_eq_zero.mp hbf).resolve_right hf,
        (mul_eq_zero.mp hfh).resolve_left hf⟩
  · exact Or.inr ⟨(mul_eq_zero.mp hbd).resolve_right hd,
      (mul_eq_zero.mp hdh).resolve_left hd⟩



theorem block_scalar_rigidity
    (a b p q : ℂ)
    (h1 : a + b = 0)
    (h2 : p + q + a * b = 0)
    (h3 : a * q + b * p = 0)
    (h4 : p * q = 0) :
    a = 0 ∧ b = 0 ∧ p = 0 ∧ q = 0 := by
  have ha3 : a ^ 3 = 0 := by
    rcases mul_eq_zero.mp h4 with hp | hq
    · linear_combination (a - b) * hp + a ^ 2 * h1 - a * h2 + h3
    · linear_combination (p + a ^ 2) * h1 - a * h2 - h3 + 2 * a * hq
  have ha : a = 0 := by
    have hm : a * (a * a) = 0 := by linear_combination ha3
    rcases mul_eq_zero.mp hm with ha | haa
    · exact ha
    · exact (mul_eq_zero.mp haa).elim id id
  have hb : b = 0 := by simpa [ha] using h1
  have hpq : p + q = 0 := by simpa [ha, hb] using h2
  rcases mul_eq_zero.mp h4 with hp | hq
  · exact ⟨ha, hb, hp, by simpa [hp] using hpq⟩
  · exact ⟨ha, hb, by simpa [hq] using hpq, hq⟩





lemma sum_perm_succ_poly {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → (MvPolynomial (Fin 3) ℂ)) :
    ∑ σ, f σ = ∑ p : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n), f (Equiv.Perm.decomposeFin.symm (p, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma perm4_poly (M : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 3) ℂ)) : Matrix.permanent M =
    M 0 0 * M 1 1 * M 2 2 * M 3 3 + M 0 0 * M 1 1 * M 3 2 * M 2 3 + M 0 0 * M 2 1 * M 1 2 * M 3 3
  + M 0 0 * M 2 1 * M 3 2 * M 1 3 + M 0 0 * M 3 1 * M 1 2 * M 2 3 + M 0 0 * M 3 1 * M 2 2 * M 1 3
  + M 1 0 * M 0 1 * M 2 2 * M 3 3 + M 1 0 * M 0 1 * M 3 2 * M 2 3 + M 1 0 * M 2 1 * M 0 2 * M 3 3
  + M 1 0 * M 2 1 * M 3 2 * M 0 3 + M 1 0 * M 3 1 * M 0 2 * M 2 3 + M 1 0 * M 3 1 * M 2 2 * M 0 3
  + M 2 0 * M 0 1 * M 1 2 * M 3 3 + M 2 0 * M 0 1 * M 3 2 * M 1 3 + M 2 0 * M 1 1 * M 0 2 * M 3 3
  + M 2 0 * M 1 1 * M 3 2 * M 0 3 + M 2 0 * M 3 1 * M 0 2 * M 1 3 + M 2 0 * M 3 1 * M 1 2 * M 0 3
  + M 3 0 * M 0 1 * M 1 2 * M 2 3 + M 3 0 * M 0 1 * M 2 2 * M 1 3 + M 3 0 * M 1 1 * M 0 2 * M 2 3
  + M 3 0 * M 1 1 * M 2 2 * M 0 3 + M 3 0 * M 2 1 * M 0 2 * M 1 3 + M 3 0 * M 2 1 * M 1 2 * M 0 3 := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ_poly]
  simp only [sum_perm_succ_poly (n := 2), sum_perm_succ_poly (n := 1), sum_perm_succ_poly (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring



noncomputable def certD400 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p))))

theorem certD400_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD400 (p+q) = certD400 p + certD400 q := by simp [certD400]

theorem certD400_nat (n : ℕ) : certD400 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD400]

set_option maxHeartbeats 1000000 in
theorem certD400_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD400 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      24 * (a0*b0*c0*d0) := by
  simp [certD400, starAffine] <;> ring

noncomputable def certD310 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 p))))

theorem certD310_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD310 (p+q) = certD310 p + certD310 q := by simp [certD310]

theorem certD310_nat (n : ℕ) : certD310 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD310]

set_option maxHeartbeats 1000000 in
theorem certD310_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD310 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      6 * (a0*b0*c0*d1 + a0*b0*c1*d0 + a0*b1*c0*d0 + a1*b0*c0*d0) := by
  simp [certD310, starAffine] <;> ring

noncomputable def certD301 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 p))))

theorem certD301_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD301 (p+q) = certD301 p + certD301 q := by simp [certD301]

theorem certD301_nat (n : ℕ) : certD301 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD301]

set_option maxHeartbeats 1000000 in
theorem certD301_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD301 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      6 * (a0*b0*c0*d2 + a0*b0*c2*d0 + a0*b2*c0*d0 + a2*b0*c0*d0) := by
  simp [certD301, starAffine] <;> ring

noncomputable def certD300 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p)))

theorem certD300_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD300 (p+q) = certD300 p + certD300 q := by simp [certD300]

theorem certD300_nat (n : ℕ) : certD300 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD300]

set_option maxHeartbeats 1000000 in
theorem certD300_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD300 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      6 * (b0*c0*d0 + a0*c0*d0 + a0*b0*d0 + a0*b0*c0) := by
  simp [certD300, starAffine] <;> ring

noncomputable def certD220 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p))))

theorem certD220_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD220 (p+q) = certD220 p + certD220 q := by simp [certD220]

theorem certD220_nat (n : ℕ) : certD220 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD220]

set_option maxHeartbeats 1000000 in
theorem certD220_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD220 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      4 * (a0*b0*c1*d1 + a0*b1*c0*d1 + a0*b1*c1*d0 + a1*b0*c0*d1 + a1*b0*c1*d0 + a1*b1*c0*d0) := by
  simp [certD220, starAffine] <;> ring

noncomputable def certD211 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p))))

theorem certD211_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD211 (p+q) = certD211 p + certD211 q := by simp [certD211]

theorem certD211_nat (n : ℕ) : certD211 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD211]

set_option maxHeartbeats 1000000 in
theorem certD211_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD211 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (a0*b0*c1*d2 + a0*b0*c2*d1 + a0*b1*c0*d2 + a0*b1*c2*d0 + a0*b2*c0*d1 + a0*b2*c1*d0 + a1*b0*c0*d2 + a1*b0*c2*d0 + a1*b2*c0*d0 + a2*b0*c0*d1 + a2*b0*c1*d0 + a2*b1*c0*d0) := by
  simp [certD211, starAffine] <;> ring

noncomputable def certD210 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 p)))

theorem certD210_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD210 (p+q) = certD210 p + certD210 q := by simp [certD210]

theorem certD210_nat (n : ℕ) : certD210 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD210]

set_option maxHeartbeats 1000000 in
theorem certD210_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD210 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (b0*c0*d1 + b0*c1*d0 + b1*c0*d0 + a0*c0*d1 + a0*c1*d0 + a0*b0*d1 + a0*b0*c1 + a0*b1*d0 + a0*b1*c0 + a1*c0*d0 + a1*b0*d0 + a1*b0*c0) := by
  simp [certD210, starAffine] <;> ring

noncomputable def certD202 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p))))

theorem certD202_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD202 (p+q) = certD202 p + certD202 q := by simp [certD202]

theorem certD202_nat (n : ℕ) : certD202 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD202]

set_option maxHeartbeats 1000000 in
theorem certD202_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD202 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      4 * (a0*b0*c2*d2 + a0*b2*c0*d2 + a0*b2*c2*d0 + a2*b0*c0*d2 + a2*b0*c2*d0 + a2*b2*c0*d0) := by
  simp [certD202, starAffine] <;> ring

noncomputable def certD201 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 p)))

theorem certD201_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD201 (p+q) = certD201 p + certD201 q := by simp [certD201]

theorem certD201_nat (n : ℕ) : certD201 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD201]

set_option maxHeartbeats 1000000 in
theorem certD201_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD201 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (b0*c0*d2 + b0*c2*d0 + b2*c0*d0 + a0*c0*d2 + a0*c2*d0 + a0*b0*d2 + a0*b0*c2 + a0*b2*d0 + a0*b2*c0 + a2*c0*d0 + a2*b0*d0 + a2*b0*c0) := by
  simp [certD201, starAffine] <;> ring

noncomputable def certD200 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p))

theorem certD200_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD200 (p+q) = certD200 p + certD200 q := by simp [certD200]

theorem certD200_nat (n : ℕ) : certD200 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD200]

set_option maxHeartbeats 1000000 in
theorem certD200_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD200 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (c0*d0 + b0*d0 + b0*c0 + a0*d0 + a0*c0 + a0*b0) := by
  simp [certD200, starAffine] <;> ring

noncomputable def certD130 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p))))

theorem certD130_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD130 (p+q) = certD130 p + certD130 q := by simp [certD130]

theorem certD130_nat (n : ℕ) : certD130 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD130]

set_option maxHeartbeats 1000000 in
theorem certD130_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD130 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      6 * (a0*b1*c1*d1 + a1*b0*c1*d1 + a1*b1*c0*d1 + a1*b1*c1*d0) := by
  simp [certD130, starAffine] <;> ring

noncomputable def certD121 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p))))

theorem certD121_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD121 (p+q) = certD121 p + certD121 q := by simp [certD121]

theorem certD121_nat (n : ℕ) : certD121 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD121]

set_option maxHeartbeats 1000000 in
theorem certD121_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD121 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (a0*b1*c1*d2 + a0*b1*c2*d1 + a0*b2*c1*d1 + a1*b0*c1*d2 + a1*b0*c2*d1 + a1*b1*c0*d2 + a1*b1*c2*d0 + a1*b2*c0*d1 + a1*b2*c1*d0 + a2*b0*c1*d1 + a2*b1*c0*d1 + a2*b1*c1*d0) := by
  simp [certD121, starAffine] <;> ring

noncomputable def certD120 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p)))

theorem certD120_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD120 (p+q) = certD120 p + certD120 q := by simp [certD120]

theorem certD120_nat (n : ℕ) : certD120 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD120]

set_option maxHeartbeats 1000000 in
theorem certD120_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD120 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (b0*c1*d1 + b1*c0*d1 + b1*c1*d0 + a0*c1*d1 + a0*b1*d1 + a0*b1*c1 + a1*c0*d1 + a1*c1*d0 + a1*b0*d1 + a1*b0*c1 + a1*b1*d0 + a1*b1*c0) := by
  simp [certD120, starAffine] <;> ring

noncomputable def certD112 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p))))

theorem certD112_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD112 (p+q) = certD112 p + certD112 q := by simp [certD112]

theorem certD112_nat (n : ℕ) : certD112 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD112]

set_option maxHeartbeats 1000000 in
theorem certD112_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD112 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (a0*b1*c2*d2 + a0*b2*c1*d2 + a0*b2*c2*d1 + a1*b0*c2*d2 + a1*b2*c0*d2 + a1*b2*c2*d0 + a2*b0*c1*d2 + a2*b0*c2*d1 + a2*b1*c0*d2 + a2*b1*c2*d0 + a2*b2*c0*d1 + a2*b2*c1*d0) := by
  simp [certD112, starAffine] <;> ring

noncomputable def certD111 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p)))

theorem certD111_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD111 (p+q) = certD111 p + certD111 q := by simp [certD111]

theorem certD111_nat (n : ℕ) : certD111 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD111]

set_option maxHeartbeats 1000000 in
theorem certD111_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD111 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      1 * (b0*c1*d2 + b0*c2*d1 + b1*c0*d2 + b1*c2*d0 + b2*c0*d1 + b2*c1*d0 + a0*c1*d2 + a0*c2*d1 + a0*b1*d2 + a0*b1*c2 + a0*b2*d1 + a0*b2*c1 + a1*c0*d2 + a1*c2*d0 + a1*b0*d2 + a1*b0*c2 + a1*b2*d0 + a1*b2*c0 + a2*c0*d1 + a2*c1*d0 + a2*b0*d1 + a2*b0*c1 + a2*b1*d0 + a2*b1*c0) := by
  simp [certD111, starAffine] <;> ring

noncomputable def certD110 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 p))

theorem certD110_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD110 (p+q) = certD110 p + certD110 q := by simp [certD110]

theorem certD110_nat (n : ℕ) : certD110 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD110]

set_option maxHeartbeats 1000000 in
theorem certD110_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD110 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      1 * (c0*d1 + c1*d0 + b0*d1 + b0*c1 + b1*d0 + b1*c0 + a0*d1 + a0*c1 + a0*b1 + a1*d0 + a1*c0 + a1*b0) := by
  simp [certD110, starAffine] <;> ring

noncomputable def certD103 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p))))

theorem certD103_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD103 (p+q) = certD103 p + certD103 q := by simp [certD103]

theorem certD103_nat (n : ℕ) : certD103 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD103]

set_option maxHeartbeats 1000000 in
theorem certD103_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD103 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      6 * (a0*b2*c2*d2 + a2*b0*c2*d2 + a2*b2*c0*d2 + a2*b2*c2*d0) := by
  simp [certD103, starAffine] <;> ring

noncomputable def certD102 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p)))

theorem certD102_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD102 (p+q) = certD102 p + certD102 q := by simp [certD102]

theorem certD102_nat (n : ℕ) : certD102 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD102]

set_option maxHeartbeats 1000000 in
theorem certD102_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD102 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (b0*c2*d2 + b2*c0*d2 + b2*c2*d0 + a0*c2*d2 + a0*b2*d2 + a0*b2*c2 + a2*c0*d2 + a2*c2*d0 + a2*b0*d2 + a2*b0*c2 + a2*b2*d0 + a2*b2*c0) := by
  simp [certD102, starAffine] <;> ring

noncomputable def certD101 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 p))

theorem certD101_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD101 (p+q) = certD101 p + certD101 q := by simp [certD101]

theorem certD101_nat (n : ℕ) : certD101 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD101]

set_option maxHeartbeats 1000000 in
theorem certD101_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD101 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      1 * (c0*d2 + c2*d0 + b0*d2 + b0*c2 + b2*d0 + b2*c0 + a0*d2 + a0*c2 + a0*b2 + a2*d0 + a2*c0 + a2*b0) := by
  simp [certD101, starAffine] <;> ring

noncomputable def certD040 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p))))

theorem certD040_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD040 (p+q) = certD040 p + certD040 q := by simp [certD040]

theorem certD040_nat (n : ℕ) : certD040 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD040]

set_option maxHeartbeats 1000000 in
theorem certD040_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD040 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      24 * (a1*b1*c1*d1) := by
  simp [certD040, starAffine] <;> ring

noncomputable def certD031 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p))))

theorem certD031_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD031 (p+q) = certD031 p + certD031 q := by simp [certD031]

theorem certD031_nat (n : ℕ) : certD031 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD031]

set_option maxHeartbeats 1000000 in
theorem certD031_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD031 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      6 * (a1*b1*c1*d2 + a1*b1*c2*d1 + a1*b2*c1*d1 + a2*b1*c1*d1) := by
  simp [certD031, starAffine] <;> ring

noncomputable def certD030 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p)))

theorem certD030_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD030 (p+q) = certD030 p + certD030 q := by simp [certD030]

theorem certD030_nat (n : ℕ) : certD030 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD030]

set_option maxHeartbeats 1000000 in
theorem certD030_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD030 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      6 * (b1*c1*d1 + a1*c1*d1 + a1*b1*d1 + a1*b1*c1) := by
  simp [certD030, starAffine] <;> ring

noncomputable def certD022 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p))))

theorem certD022_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD022 (p+q) = certD022 p + certD022 q := by simp [certD022]

theorem certD022_nat (n : ℕ) : certD022 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD022]

set_option maxHeartbeats 1000000 in
theorem certD022_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD022 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      4 * (a1*b1*c2*d2 + a1*b2*c1*d2 + a1*b2*c2*d1 + a2*b1*c1*d2 + a2*b1*c2*d1 + a2*b2*c1*d1) := by
  simp [certD022, starAffine] <;> ring

noncomputable def certD021 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p)))

theorem certD021_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD021 (p+q) = certD021 p + certD021 q := by simp [certD021]

theorem certD021_nat (n : ℕ) : certD021 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD021]

set_option maxHeartbeats 1000000 in
theorem certD021_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD021 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (b1*c1*d2 + b1*c2*d1 + b2*c1*d1 + a1*c1*d2 + a1*c2*d1 + a1*b1*d2 + a1*b1*c2 + a1*b2*d1 + a1*b2*c1 + a2*c1*d1 + a2*b1*d1 + a2*b1*c1) := by
  simp [certD021, starAffine] <;> ring

noncomputable def certD020 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p))

theorem certD020_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD020 (p+q) = certD020 p + certD020 q := by simp [certD020]

theorem certD020_nat (n : ℕ) : certD020 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD020]

set_option maxHeartbeats 1000000 in
theorem certD020_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD020 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (c1*d1 + b1*d1 + b1*c1 + a1*d1 + a1*c1 + a1*b1) := by
  simp [certD020, starAffine] <;> ring

noncomputable def certD013 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p))))

theorem certD013_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD013 (p+q) = certD013 p + certD013 q := by simp [certD013]

theorem certD013_nat (n : ℕ) : certD013 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD013]

set_option maxHeartbeats 1000000 in
theorem certD013_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD013 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      6 * (a1*b2*c2*d2 + a2*b1*c2*d2 + a2*b2*c1*d2 + a2*b2*c2*d1) := by
  simp [certD013, starAffine] <;> ring

noncomputable def certD012 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p)))

theorem certD012_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD012 (p+q) = certD012 p + certD012 q := by simp [certD012]

theorem certD012_nat (n : ℕ) : certD012 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD012]

set_option maxHeartbeats 1000000 in
theorem certD012_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD012 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (b1*c2*d2 + b2*c1*d2 + b2*c2*d1 + a1*c2*d2 + a1*b2*d2 + a1*b2*c2 + a2*c1*d2 + a2*c2*d1 + a2*b1*d2 + a2*b1*c2 + a2*b2*d1 + a2*b2*c1) := by
  simp [certD012, starAffine] <;> ring

noncomputable def certD011 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p))

theorem certD011_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD011 (p+q) = certD011 p + certD011 q := by simp [certD011]

theorem certD011_nat (n : ℕ) : certD011 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD011]

set_option maxHeartbeats 1000000 in
theorem certD011_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD011 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      1 * (c1*d2 + c2*d1 + b1*d2 + b1*c2 + b2*d1 + b2*c1 + a1*d2 + a1*c2 + a1*b2 + a2*d1 + a2*c1 + a2*b1) := by
  simp [certD011, starAffine] <;> ring

noncomputable def certD004 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p))))

theorem certD004_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD004 (p+q) = certD004 p + certD004 q := by simp [certD004]

theorem certD004_nat (n : ℕ) : certD004 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD004]

set_option maxHeartbeats 1000000 in
theorem certD004_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD004 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      24 * (a2*b2*c2*d2) := by
  simp [certD004, starAffine] <;> ring

noncomputable def certD003 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p)))

theorem certD003_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD003 (p+q) = certD003 p + certD003 q := by simp [certD003]

theorem certD003_nat (n : ℕ) : certD003 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD003]

set_option maxHeartbeats 1000000 in
theorem certD003_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD003 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      6 * (b2*c2*d2 + a2*c2*d2 + a2*b2*d2 + a2*b2*c2) := by
  simp [certD003, starAffine] <;> ring

noncomputable def certD002 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p))

theorem certD002_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD002 (p+q) = certD002 p + certD002 q := by simp [certD002]

theorem certD002_nat (n : ℕ) : certD002 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD002]

set_option maxHeartbeats 1000000 in
theorem certD002_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD002 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (c2*d2 + b2*d2 + b2*c2 + a2*d2 + a2*c2 + a2*b2) := by
  simp [certD002, starAffine] <;> ring

set_option maxHeartbeats 4000000 in
theorem certEq400 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d0^2*d3*d6 - d0^2*o0^2 - d0*d3^2*d6 - d0*d3*d6^2 - 2*d0*d3*d6*o0 - 2*d0*d3*d6*o3 - 2*d0*d3*d6*o6 - 2*d0*d3*d6 - d0*d3*o0^2 + d0*d3*o6^2 - d0*d6*o0^2 + d0*d6*o3^2 - d0*d6 - 2*d0*o0^3 - 2*d0*o0^2*o3 - 2*d0*o0^2*o6 - 2*d0*o0^2 + 2*d0*o0*o3*o6 - d3*d6 - d6^2 - 2*d6*o0 - 2*d6*o3 - 2*d6*o6 - 2*d6 + o6^2) = 0 := by
  have hq : certD400 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD400_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD400_add, certD400_four] at hq
  linear_combination (1/24 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq310 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d0^2*d3*d7 - d0^2*d4*d6 - 2*d0^2*o0*o1 - 2*d0*d1*d3*d6 - 2*d0*d1*o0^2 - d0*d3^2*d7 - 2*d0*d3*d4*d6 - 2*d0*d3*d6*d7 - 2*d0*d3*d6*o1 - 2*d0*d3*d6*o4 - 2*d0*d3*d6*o7 - 2*d0*d3*d6 - 2*d0*d3*d7*o0 - 2*d0*d3*d7*o3 - 2*d0*d3*d7*o6 - 2*d0*d3*d7 - 2*d0*d3*o0*o1 + 2*d0*d3*o6*o7 - d0*d4*d6^2 - 2*d0*d4*d6*o0 - 2*d0*d4*d6*o3 - 2*d0*d4*d6*o6 - 2*d0*d4*d6 - d0*d4*o0^2 + d0*d4*o6^2 - 2*d0*d6*o0*o1 + 2*d0*d6*o3*o4 - d0*d7*o0^2 + d0*d7*o3^2 - d0*d7 - 6*d0*o0^2*o1 - 2*d0*o0^2*o4 - 2*d0*o0^2*o7 - 2*d0*o0^2 - 4*d0*o0*o1*o3 - 4*d0*o0*o1*o6 - 4*d0*o0*o1 + 2*d0*o0*o3*o7 + 2*d0*o0*o4*o6 - 2*d0*o0 + 2*d0*o1*o3*o6 - d1*d3^2*d6 - d1*d3*d6^2 - 2*d1*d3*d6*o0 - 2*d1*d3*d6*o3 - 2*d1*d3*d6*o6 - 2*d1*d3*d6 - d1*d3*o0^2 + d1*d3*o6^2 - d1*d6*o0^2 + d1*d6*o3^2 - d1*d6 - 2*d1*o0^3 - 2*d1*o0^2*o3 - 2*d1*o0^2*o6 - 2*d1*o0^2 + 2*d1*o0*o3*o6 - d3*d7 - 2*d3*o0 - d4*d6 - 2*d6*d7 - 2*d6*o0 - 2*d6*o1 - 2*d6*o4 - 2*d6*o7 - 2*d6 - 2*d7*o0 - 2*d7*o3 - 2*d7*o6 - 2*d7 - 4*o0^2 - 4*o0*o3 - 4*o0*o6 - 4*o0 + 2*o3*o6 + 2*o6*o7) = 0 := by
  have hq : certD310 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD310_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD310_add, certD310_four] at hq
  linear_combination (1/6 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq301 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d0^2*d3*d8 - d0^2*d5*d6 - 2*d0^2*o0*o2 - 2*d0*d2*d3*d6 - 2*d0*d2*o0^2 - d0*d3^2*d8 - 2*d0*d3*d5*d6 - 2*d0*d3*d6*d8 - 2*d0*d3*d6*o2 - 2*d0*d3*d6*o5 - 2*d0*d3*d6*o8 - 2*d0*d3*d6 - 2*d0*d3*d8*o0 - 2*d0*d3*d8*o3 - 2*d0*d3*d8*o6 - 2*d0*d3*d8 - 2*d0*d3*o0*o2 + 2*d0*d3*o6*o8 - d0*d5*d6^2 - 2*d0*d5*d6*o0 - 2*d0*d5*d6*o3 - 2*d0*d5*d6*o6 - 2*d0*d5*d6 - d0*d5*o0^2 + d0*d5*o6^2 - 2*d0*d6*o0*o2 + 2*d0*d6*o3*o5 - d0*d8*o0^2 + d0*d8*o3^2 - d0*d8 - 6*d0*o0^2*o2 - 2*d0*o0^2*o5 - 2*d0*o0^2*o8 - 2*d0*o0^2 - 4*d0*o0*o2*o3 - 4*d0*o0*o2*o6 - 4*d0*o0*o2 + 2*d0*o0*o3*o8 + 2*d0*o0*o5*o6 + 2*d0*o2*o3*o6 - d2*d3^2*d6 - d2*d3*d6^2 - 2*d2*d3*d6*o0 - 2*d2*d3*d6*o3 - 2*d2*d3*d6*o6 - 2*d2*d3*d6 - d2*d3*o0^2 + d2*d3*o6^2 - d2*d6*o0^2 + d2*d6*o3^2 - d2*d6 - 2*d2*o0^3 - 2*d2*o0^2*o3 - 2*d2*o0^2*o6 - 2*d2*o0^2 + 2*d2*o0*o3*o6 - d3*d8 - d5*d6 - 2*d6*d8 - 2*d6*o2 + 2*d6*o3 - 2*d6*o5 - 2*d6*o8 - 2*d6 - 2*d8*o0 - 2*d8*o3 - 2*d8*o6 - 2*d8 + 2*o0*o6 + 2*o6*o8) = 0 := by
  have hq : certD301 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD301_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD301_add, certD301_four] at hq
  linear_combination (1/6 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq300 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d0^2*d3 - d0^2*d6 - 2*d0^2*o0 - d0*d3^2 - 2*d0*d3*d6 - 4*d0*d3*o0 - 2*d0*d3*o3 - 2*d0*d3 - d0*d6^2 - 4*d0*d6*o0 - 2*d0*d6*o6 - 4*d0*d6 - 4*d0*o0^2 - 2*d0*o0*o3 - 2*d0*o0*o6 - 6*d0*o0 + d0*o3^2 + 2*d0*o3*o6 + d0*o6^2 - d0 - d3^2*d6 - d3*d6^2 - 2*d3*d6*o0 - 2*d3*d6*o3 - 2*d3*d6*o6 - 4*d3*d6 - d3*o0^2 - 2*d3*o0 + d3*o6^2 - d3 - 2*d6^2 - d6*o0^2 - 6*d6*o0 + d6*o3^2 - 2*d6*o3 - 4*d6*o6 - 4*d6 - 2*o0^3 - 2*o0^2*o3 - 2*o0^2*o6 - 6*o0^2 + 2*o0*o3*o6 - 4*o0*o3 - 2*o0*o6 - 6*o0 + 2*o3*o6 - 2*o3 + 2*o6^2 - 2) = 0 := by
  have hq : certD300 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD300_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD300_add, certD300_four] at hq
  linear_combination (1/6 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq220 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d0^2*d4*d7 - d0^2*o1^2 - 2*d0*d1*d3*d7 - 2*d0*d1*d4*d6 - 4*d0*d1*o0*o1 - 2*d0*d3*d4*d7 - d0*d3*d7^2 - 2*d0*d3*d7*o1 - 2*d0*d3*d7*o4 - 2*d0*d3*d7*o7 - 2*d0*d3*d7 - d0*d3*o1^2 + d0*d3*o7^2 - d0*d3 - d0*d4^2*d6 - 2*d0*d4*d6*d7 - 2*d0*d4*d6*o1 - 2*d0*d4*d6*o4 - 2*d0*d4*d6*o7 - 2*d0*d4*d6 - 2*d0*d4*d7*o0 - 2*d0*d4*d7*o3 - 2*d0*d4*d7*o6 - 2*d0*d4*d7 - 2*d0*d4*o0*o1 + 2*d0*d4*o6*o7 - d0*d6*o1^2 + d0*d6*o4^2 - 2*d0*d7*o0*o1 + 2*d0*d7*o3*o4 - 6*d0*o0*o1^2 - 4*d0*o0*o1*o4 - 4*d0*o0*o1*o7 - 4*d0*o0*o1 + 2*d0*o0*o4*o7 - 2*d0*o1^2*o3 - 2*d0*o1^2*o6 - 2*d0*o1^2 + 2*d0*o1*o3*o7 + 2*d0*o1*o4*o6 - 2*d0*o1 - d1^2*d3*d6 - d1^2*o0^2 - d1*d3^2*d7 - 2*d1*d3*d4*d6 - 2*d1*d3*d6*d7 - 2*d1*d3*d6*o1 - 2*d1*d3*d6*o4 - 2*d1*d3*d6*o7 - 2*d1*d3*d6 - 2*d1*d3*d7*o0 - 2*d1*d3*d7*o3 - 2*d1*d3*d7*o6 - 2*d1*d3*d7 - 2*d1*d3*o0*o1 + 2*d1*d3*o6*o7 - d1*d4*d6^2 - 2*d1*d4*d6*o0 - 2*d1*d4*d6*o3 - 2*d1*d4*d6*o6 - 2*d1*d4*d6 - d1*d4*o0^2 + d1*d4*o6^2 - 2*d1*d6*o0*o1 + 2*d1*d6*o3*o4 - d1*d7*o0^2 + d1*d7*o3^2 - d1*d7 - 6*d1*o0^2*o1 - 2*d1*o0^2*o4 - 2*d1*o0^2*o7 - 2*d1*o0^2 - 4*d1*o0*o1*o3 - 4*d1*o0*o1*o6 - 4*d1*o0*o1 + 2*d1*o0*o3*o7 + 2*d1*o0*o4*o6 - 2*d1*o0 + 2*d1*o1*o3*o6 - d3^2 - d3*d6 - 2*d3*o0 - 2*d3*o1 - 2*d3*o3 - 2*d3*o6 - 2*d3 - d4*d7 - 2*d4*o0 - 2*d6*o1 - d7^2 - 2*d7*o0 - 2*d7*o1 - 2*d7*o4 - 2*d7*o7 - 2*d7 - 8*o0*o1 - 4*o0*o4 - 4*o0*o7 - 4*o0 - 4*o1*o3 - 4*o1*o6 - 4*o1 + o3^2 + 2*o3*o7 + 2*o4*o6 + o7^2) = 0 := by
  have hq : certD220 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD220_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD220_add, certD220_four] at hq
  linear_combination (1/4 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq211 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d0^2*d4*d8 - d0^2*d5*d7 - 2*d0^2*o1*o2 - 2*d0*d1*d3*d8 - 2*d0*d1*d5*d6 - 4*d0*d1*o0*o2 - 2*d0*d2*d3*d7 - 2*d0*d2*d4*d6 - 4*d0*d2*o0*o1 - 2*d0*d3*d4*d8 - 2*d0*d3*d5*d7 - 2*d0*d3*d7*d8 - 2*d0*d3*d7*o2 - 2*d0*d3*d7*o5 - 2*d0*d3*d7*o8 - 2*d0*d3*d7 - 2*d0*d3*d8*o1 - 2*d0*d3*d8*o4 - 2*d0*d3*d8*o7 - 2*d0*d3*d8 - 2*d0*d3*o1*o2 + 2*d0*d3*o7*o8 - 2*d0*d4*d5*d6 - 2*d0*d4*d6*d8 - 2*d0*d4*d6*o2 - 2*d0*d4*d6*o5 - 2*d0*d4*d6*o8 - 2*d0*d4*d6 - 2*d0*d4*d8*o0 - 2*d0*d4*d8*o3 - 2*d0*d4*d8*o6 - 2*d0*d4*d8 - 2*d0*d4*o0*o2 + 2*d0*d4*o6*o8 - 2*d0*d5*d6*d7 - 2*d0*d5*d6*o1 - 2*d0*d5*d6*o4 - 2*d0*d5*d6*o7 - 2*d0*d5*d6 - 2*d0*d5*d7*o0 - 2*d0*d5*d7*o3 - 2*d0*d5*d7*o6 - 2*d0*d5*d7 - 2*d0*d5*o0*o1 + 2*d0*d5*o6*o7 - 2*d0*d6*o1*o2 + 2*d0*d6*o4*o5 - 2*d0*d7*o0*o2 + 2*d0*d7*o3*o5 - 2*d0*d8*o0*o1 + 2*d0*d8*o3*o4 - 12*d0*o0*o1*o2 - 4*d0*o0*o1*o5 - 4*d0*o0*o1*o8 - 4*d0*o0*o1 - 4*d0*o0*o2*o4 - 4*d0*o0*o2*o7 - 4*d0*o0*o2 + 2*d0*o0*o4*o8 + 2*d0*o0*o5*o7 - 4*d0*o1*o2*o3 - 4*d0*o1*o2*o6 - 4*d0*o1*o2 + 2*d0*o1*o3*o8 + 2*d0*o1*o5*o6 + 2*d0*o2*o3*o7 + 2*d0*o2*o4*o6 - 2*d0*o2 - 2*d1*d2*d3*d6 - 2*d1*d2*o0^2 - d1*d3^2*d8 - 2*d1*d3*d5*d6 - 2*d1*d3*d6*d8 - 2*d1*d3*d6*o2 - 2*d1*d3*d6*o5 - 2*d1*d3*d6*o8 - 2*d1*d3*d6 - 2*d1*d3*d8*o0 - 2*d1*d3*d8*o3 - 2*d1*d3*d8*o6 - 2*d1*d3*d8 - 2*d1*d3*o0*o2 + 2*d1*d3*o6*o8 - d1*d5*d6^2 - 2*d1*d5*d6*o0 - 2*d1*d5*d6*o3 - 2*d1*d5*d6*o6 - 2*d1*d5*d6 - d1*d5*o0^2 + d1*d5*o6^2 - 2*d1*d6*o0*o2 + 2*d1*d6*o3*o5 - d1*d8*o0^2 + d1*d8*o3^2 - d1*d8 - 6*d1*o0^2*o2 - 2*d1*o0^2*o5 - 2*d1*o0^2*o8 - 2*d1*o0^2 - 4*d1*o0*o2*o3 - 4*d1*o0*o2*o6 - 4*d1*o0*o2 + 2*d1*o0*o3*o8 + 2*d1*o0*o5*o6 + 2*d1*o2*o3*o6 - d2*d3^2*d7 - 2*d2*d3*d4*d6 - 2*d2*d3*d6*d7 - 2*d2*d3*d6*o1 - 2*d2*d3*d6*o4 - 2*d2*d3*d6*o7 - 2*d2*d3*d6 - 2*d2*d3*d7*o0 - 2*d2*d3*d7*o3 - 2*d2*d3*d7*o6 - 2*d2*d3*d7 - 2*d2*d3*o0*o1 + 2*d2*d3*o6*o7 - d2*d4*d6^2 - 2*d2*d4*d6*o0 - 2*d2*d4*d6*o3 - 2*d2*d4*d6*o6 - 2*d2*d4*d6 - d2*d4*o0^2 + d2*d4*o6^2 - 2*d2*d6*o0*o1 + 2*d2*d6*o3*o4 - d2*d7*o0^2 + d2*d7*o3^2 - d2*d7 - 6*d2*o0^2*o1 - 2*d2*o0^2*o4 - 2*d2*o0^2*o7 - 2*d2*o0^2 - 4*d2*o0*o1*o3 - 4*d2*o0*o1*o6 - 4*d2*o0*o1 + 2*d2*o0*o3*o7 + 2*d2*o0*o4*o6 - 2*d2*o0 + 2*d2*o1*o3*o6 - 2*d3*o2 + 2*d3*o6 - d4*d8 - d5*d7 - 2*d5*o0 - 2*d6*o2 + 2*d6*o4 - 2*d7*d8 - 2*d7*o2 + 2*d7*o3 - 2*d7*o5 - 2*d7*o8 - 2*d7 - 2*d8*o0 - 2*d8*o1 - 2*d8*o4 - 2*d8*o7 - 2*d8 - 8*o0*o2 + 2*o0*o3 - 4*o0*o5 + 2*o0*o7 - 4*o0*o8 - 4*o0 + 2*o1*o6 - 4*o2*o3 - 4*o2*o6 - 4*o2 + 2*o3*o8 + 2*o5*o6 + 2*o7*o8) = 0 := by
  have hq : certD211 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD211_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD211_add, certD211_four] at hq
  linear_combination (1/2 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq210 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d0^2*d4 - d0^2*d7 - 2*d0^2*o1 - 2*d0*d1*d3 - 2*d0*d1*d6 - 4*d0*d1*o0 - 2*d0*d3*d4 - 2*d0*d3*d7 - 4*d0*d3*o1 - 2*d0*d3*o4 - 4*d0*d3 - 2*d0*d4*d6 - 4*d0*d4*o0 - 2*d0*d4*o3 - 2*d0*d4 - 2*d0*d6*d7 - 4*d0*d6*o1 - 2*d0*d6*o7 - 2*d0*d6 - 4*d0*d7*o0 - 2*d0*d7*o6 - 4*d0*d7 - 8*d0*o0*o1 - 2*d0*o0*o4 - 2*d0*o0*o7 - 6*d0*o0 - 2*d0*o1*o3 - 2*d0*o1*o6 - 6*d0*o1 + 2*d0*o3*o4 + 2*d0*o3*o7 + 2*d0*o4*o6 + 2*d0*o6*o7 - 2*d0 - d1*d3^2 - 2*d1*d3*d6 - 4*d1*d3*o0 - 2*d1*d3*o3 - 2*d1*d3 - d1*d6^2 - 4*d1*d6*o0 - 2*d1*d6*o6 - 4*d1*d6 - 4*d1*o0^2 - 2*d1*o0*o3 - 2*d1*o0*o6 - 6*d1*o0 + d1*o3^2 + 2*d1*o3*o6 + d1*o6^2 - d1 - d3^2*d7 - 2*d3^2 - 2*d3*d4*d6 - 2*d3*d6*d7 - 2*d3*d6*o1 - 2*d3*d6*o4 - 2*d3*d6*o7 - 4*d3*d6 - 2*d3*d7*o0 - 2*d3*d7*o3 - 2*d3*d7*o6 - 4*d3*d7 - 2*d3*o0*o1 - 6*d3*o0 - 2*d3*o1 - 4*d3*o3 + 2*d3*o6*o7 - 2*d3*o6 - 6*d3 - d4*d6^2 - 2*d4*d6*o0 - 2*d4*d6*o3 - 2*d4*d6*o6 - 4*d4*d6 - d4*o0^2 - 2*d4*o0 + d4*o6^2 - d4 - 4*d6*d7 - 2*d6*o0*o1 - 2*d6*o0 - 6*d6*o1 + 2*d6*o3*o4 - 2*d6*o4 - 4*d6*o7 - 6*d6 - d7*o0^2 - 6*d7*o0 + d7*o3^2 - 2*d7*o3 - 4*d7*o6 - 4*d7 - 6*o0^2*o1 - 2*o0^2*o4 - 2*o0^2*o7 - 6*o0^2 - 4*o0*o1*o3 - 4*o0*o1*o6 - 12*o0*o1 + 2*o0*o3*o7 - 2*o0*o3 + 2*o0*o4*o6 - 4*o0*o4 - 4*o0*o6 - 2*o0*o7 - 10*o0 + 2*o1*o3*o6 - 4*o1*o3 - 2*o1*o6 - 6*o1 + 2*o3^2 + 2*o3*o6 + 2*o3*o7 - 2*o3 + 2*o4*o6 - 2*o4 + 4*o6*o7 - 2*o6 - 6) = 0 := by
  have hq : certD210 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD210_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD210_add, certD210_four] at hq
  linear_combination (1/2 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq202 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d0^2*d5*d8 - d0^2*o2^2 - 2*d0*d2*d3*d8 - 2*d0*d2*d5*d6 - 4*d0*d2*o0*o2 - 2*d0*d3*d5*d8 - d0*d3*d8^2 - 2*d0*d3*d8*o2 - 2*d0*d3*d8*o5 - 2*d0*d3*d8*o8 - 2*d0*d3*d8 - d0*d3*o2^2 + d0*d3*o8^2 - d0*d5^2*d6 - 2*d0*d5*d6*d8 - 2*d0*d5*d6*o2 - 2*d0*d5*d6*o5 - 2*d0*d5*d6*o8 - 2*d0*d5*d6 - 2*d0*d5*d8*o0 - 2*d0*d5*d8*o3 - 2*d0*d5*d8*o6 - 2*d0*d5*d8 - 2*d0*d5*o0*o2 + 2*d0*d5*o6*o8 - d0*d6*o2^2 + d0*d6*o5^2 - 2*d0*d8*o0*o2 + 2*d0*d8*o3*o5 - 6*d0*o0*o2^2 - 4*d0*o0*o2*o5 - 4*d0*o0*o2*o8 - 4*d0*o0*o2 + 2*d0*o0*o5*o8 - 2*d0*o2^2*o3 - 2*d0*o2^2*o6 - 2*d0*o2^2 + 2*d0*o2*o3*o8 + 2*d0*o2*o5*o6 - d2^2*d3*d6 - d2^2*o0^2 - d2*d3^2*d8 - 2*d2*d3*d5*d6 - 2*d2*d3*d6*d8 - 2*d2*d3*d6*o2 - 2*d2*d3*d6*o5 - 2*d2*d3*d6*o8 - 2*d2*d3*d6 - 2*d2*d3*d8*o0 - 2*d2*d3*d8*o3 - 2*d2*d3*d8*o6 - 2*d2*d3*d8 - 2*d2*d3*o0*o2 + 2*d2*d3*o6*o8 - d2*d5*d6^2 - 2*d2*d5*d6*o0 - 2*d2*d5*d6*o3 - 2*d2*d5*d6*o6 - 2*d2*d5*d6 - d2*d5*o0^2 + d2*d5*o6^2 - 2*d2*d6*o0*o2 + 2*d2*d6*o3*o5 - d2*d8*o0^2 + d2*d8*o3^2 - d2*d8 - 6*d2*o0^2*o2 - 2*d2*o0^2*o5 - 2*d2*o0^2*o8 - 2*d2*o0^2 - 4*d2*o0*o2*o3 - 4*d2*o0*o2*o6 - 4*d2*o0*o2 + 2*d2*o0*o3*o8 + 2*d2*o0*o5*o6 + 2*d2*o2*o3*o6 + d3*d6 - d5*d8 + 2*d6*o5 - d8^2 - 2*d8*o2 + 2*d8*o3 - 2*d8*o5 - 2*d8*o8 - 2*d8 + o0^2 + 2*o0*o8 + 2*o2*o6 + o8^2) = 0 := by
  have hq : certD202 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD202_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD202_add, certD202_four] at hq
  linear_combination (1/4 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq201 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d0^2*d5 - d0^2*d8 - 2*d0^2*o2 - 2*d0*d2*d3 - 2*d0*d2*d6 - 4*d0*d2*o0 - 2*d0*d3*d5 - 2*d0*d3*d8 - 4*d0*d3*o2 - 2*d0*d3*o5 - 2*d0*d3 - 2*d0*d5*d6 - 4*d0*d5*o0 - 2*d0*d5*o3 - 2*d0*d5 - 2*d0*d6*d8 - 4*d0*d6*o2 - 2*d0*d6*o8 - 2*d0*d6 - 4*d0*d8*o0 - 2*d0*d8*o6 - 4*d0*d8 - 8*d0*o0*o2 - 2*d0*o0*o5 - 2*d0*o0*o8 - 4*d0*o0 - 2*d0*o2*o3 - 2*d0*o2*o6 - 6*d0*o2 + 2*d0*o3*o5 + 2*d0*o3*o8 + 2*d0*o5*o6 + 2*d0*o6*o8 - d2*d3^2 - 2*d2*d3*d6 - 4*d2*d3*o0 - 2*d2*d3*o3 - 2*d2*d3 - d2*d6^2 - 4*d2*d6*o0 - 2*d2*d6*o6 - 4*d2*d6 - 4*d2*o0^2 - 2*d2*o0*o3 - 2*d2*o0*o6 - 6*d2*o0 + d2*o3^2 + 2*d2*o3*o6 + d2*o6^2 - d2 - d3^2*d8 - 2*d3*d5*d6 - 2*d3*d6*d8 - 2*d3*d6*o2 - 2*d3*d6*o5 - 2*d3*d6*o8 - 2*d3*d8*o0 - 2*d3*d8*o3 - 2*d3*d8*o6 - 4*d3*d8 - 2*d3*o0*o2 - 2*d3*o2 + 2*d3*o6*o8 + 2*d3*o6 - d5*d6^2 - 2*d5*d6*o0 - 2*d5*d6*o3 - 2*d5*d6*o6 - 4*d5*d6 - d5*o0^2 - 2*d5*o0 + d5*o6^2 - d5 - 4*d6*d8 - 2*d6*o0*o2 - 6*d6*o2 + 2*d6*o3*o5 + 2*d6*o3 - 2*d6*o5 - 4*d6*o8 - 2*d6 - d8*o0^2 - 6*d8*o0 + d8*o3^2 - 2*d8*o3 - 4*d8*o6 - 4*d8 - 6*o0^2*o2 - 2*o0^2*o5 - 2*o0^2*o8 - 4*o0*o2*o3 - 4*o0*o2*o6 - 12*o0*o2 + 2*o0*o3*o8 + 2*o0*o3 + 2*o0*o5*o6 - 4*o0*o5 + 2*o0*o6 - 2*o0*o8 - 2*o0 + 2*o2*o3*o6 - 4*o2*o3 - 2*o2*o6 - 6*o2 + 2*o3*o8 + 2*o3 + 2*o5*o6 - 2*o5 + 4*o6*o8 + 2*o6 - 2) = 0 := by
  have hq : certD201 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD201_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD201_add, certD201_four] at hq
  linear_combination (1/2 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq200 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d0^2 - d0*d3 - d0*d6 - 2*d0*o0 - 4*d0 - d3^2 - d3*d6 - 4*d3*o0 - 2*d3*o3 - 4*d3 - d6^2 - 4*d6*o0 - 2*d6*o6 - 2*d6 - 3*o0^2 - 2*o0*o3 - 2*o0*o6 - 6*o0 + o3^2 + 2*o3*o6 - 2*o3 + o6^2 - 3) = 0 := by
  have hq : certD200 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD200_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD200_add, certD200_four] at hq
  linear_combination (1/4 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq130 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-2*d0*d1*d4*d7 - 2*d0*d1*o1^2 - d0*d4^2*d7 - d0*d4*d7^2 - 2*d0*d4*d7*o1 - 2*d0*d4*d7*o4 - 2*d0*d4*d7*o7 - 2*d0*d4*d7 - d0*d4*o1^2 + d0*d4*o7^2 - d0*d4 - d0*d7*o1^2 + d0*d7*o4^2 - 2*d0*o1^3 - 2*d0*o1^2*o4 - 2*d0*o1^2*o7 - 2*d0*o1^2 + 2*d0*o1*o4*o7 - d1^2*d3*d7 - d1^2*d4*d6 - 2*d1^2*o0*o1 - 2*d1*d3*d4*d7 - d1*d3*d7^2 - 2*d1*d3*d7*o1 - 2*d1*d3*d7*o4 - 2*d1*d3*d7*o7 - 2*d1*d3*d7 - d1*d3*o1^2 + d1*d3*o7^2 - d1*d3 - d1*d4^2*d6 - 2*d1*d4*d6*d7 - 2*d1*d4*d6*o1 - 2*d1*d4*d6*o4 - 2*d1*d4*d6*o7 - 2*d1*d4*d6 - 2*d1*d4*d7*o0 - 2*d1*d4*d7*o3 - 2*d1*d4*d7*o6 - 2*d1*d4*d7 - 2*d1*d4*o0*o1 + 2*d1*d4*o6*o7 - d1*d6*o1^2 + d1*d6*o4^2 - 2*d1*d7*o0*o1 + 2*d1*d7*o3*o4 - 6*d1*o0*o1^2 - 4*d1*o0*o1*o4 - 4*d1*o0*o1*o7 - 4*d1*o0*o1 + 2*d1*o0*o4*o7 - 2*d1*o1^2*o3 - 2*d1*o1^2*o6 - 2*d1*o1^2 + 2*d1*o1*o3*o7 + 2*d1*o1*o4*o6 - 2*d1*o1 - 2*d3*d4 - d3*d7 - 2*d3*o1 - 2*d3*o4 - 2*d3*o7 - 2*d3 - d4*d6 - 2*d4*o0 - 2*d4*o1 - 2*d4*o3 - 2*d4*o6 - 2*d4 - 2*d7*o1 - 4*o1^2 - 4*o1*o4 - 4*o1*o7 - 4*o1 + 2*o3*o4 + 2*o4*o7) = 0 := by
  have hq : certD130 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD130_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD130_add, certD130_four] at hq
  linear_combination (1/6 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq121 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-2*d0*d1*d4*d8 - 2*d0*d1*d5*d7 - 4*d0*d1*o1*o2 - 2*d0*d2*d4*d7 - 2*d0*d2*o1^2 - d0*d4^2*d8 - 2*d0*d4*d5*d7 - 2*d0*d4*d7*d8 - 2*d0*d4*d7*o2 - 2*d0*d4*d7*o5 - 2*d0*d4*d7*o8 - 2*d0*d4*d7 - 2*d0*d4*d8*o1 - 2*d0*d4*d8*o4 - 2*d0*d4*d8*o7 - 2*d0*d4*d8 - 2*d0*d4*o1*o2 + 2*d0*d4*o7*o8 - d0*d5*d7^2 - 2*d0*d5*d7*o1 - 2*d0*d5*d7*o4 - 2*d0*d5*d7*o7 - 2*d0*d5*d7 - d0*d5*o1^2 + d0*d5*o7^2 - d0*d5 - 2*d0*d7*o1*o2 + 2*d0*d7*o4*o5 - d0*d8*o1^2 + d0*d8*o4^2 - 6*d0*o1^2*o2 - 2*d0*o1^2*o5 - 2*d0*o1^2*o8 - 2*d0*o1^2 - 4*d0*o1*o2*o4 - 4*d0*o1*o2*o7 - 4*d0*o1*o2 + 2*d0*o1*o4*o8 + 2*d0*o1*o5*o7 + 2*d0*o2*o4*o7 - d1^2*d3*d8 - d1^2*d5*d6 - 2*d1^2*o0*o2 - 2*d1*d2*d3*d7 - 2*d1*d2*d4*d6 - 4*d1*d2*o0*o1 - 2*d1*d3*d4*d8 - 2*d1*d3*d5*d7 - 2*d1*d3*d7*d8 - 2*d1*d3*d7*o2 - 2*d1*d3*d7*o5 - 2*d1*d3*d7*o8 - 2*d1*d3*d7 - 2*d1*d3*d8*o1 - 2*d1*d3*d8*o4 - 2*d1*d3*d8*o7 - 2*d1*d3*d8 - 2*d1*d3*o1*o2 + 2*d1*d3*o7*o8 - 2*d1*d4*d5*d6 - 2*d1*d4*d6*d8 - 2*d1*d4*d6*o2 - 2*d1*d4*d6*o5 - 2*d1*d4*d6*o8 - 2*d1*d4*d6 - 2*d1*d4*d8*o0 - 2*d1*d4*d8*o3 - 2*d1*d4*d8*o6 - 2*d1*d4*d8 - 2*d1*d4*o0*o2 + 2*d1*d4*o6*o8 - 2*d1*d5*d6*d7 - 2*d1*d5*d6*o1 - 2*d1*d5*d6*o4 - 2*d1*d5*d6*o7 - 2*d1*d5*d6 - 2*d1*d5*d7*o0 - 2*d1*d5*d7*o3 - 2*d1*d5*d7*o6 - 2*d1*d5*d7 - 2*d1*d5*o0*o1 + 2*d1*d5*o6*o7 - 2*d1*d6*o1*o2 + 2*d1*d6*o4*o5 - 2*d1*d7*o0*o2 + 2*d1*d7*o3*o5 - 2*d1*d8*o0*o1 + 2*d1*d8*o3*o4 - 12*d1*o0*o1*o2 - 4*d1*o0*o1*o5 - 4*d1*o0*o1*o8 - 4*d1*o0*o1 - 4*d1*o0*o2*o4 - 4*d1*o0*o2*o7 - 4*d1*o0*o2 + 2*d1*o0*o4*o8 + 2*d1*o0*o5*o7 - 4*d1*o1*o2*o3 - 4*d1*o1*o2*o6 - 4*d1*o1*o2 + 2*d1*o1*o3*o8 + 2*d1*o1*o5*o6 + 2*d1*o2*o3*o7 + 2*d1*o2*o4*o6 - 2*d1*o2 - 2*d2*d3*d4*d7 - d2*d3*d7^2 - 2*d2*d3*d7*o1 - 2*d2*d3*d7*o4 - 2*d2*d3*d7*o7 - 2*d2*d3*d7 - d2*d3*o1^2 + d2*d3*o7^2 - d2*d3 - d2*d4^2*d6 - 2*d2*d4*d6*d7 - 2*d2*d4*d6*o1 - 2*d2*d4*d6*o4 - 2*d2*d4*d6*o7 - 2*d2*d4*d6 - 2*d2*d4*d7*o0 - 2*d2*d4*d7*o3 - 2*d2*d4*d7*o6 - 2*d2*d4*d7 - 2*d2*d4*o0*o1 + 2*d2*d4*o6*o7 - d2*d6*o1^2 + d2*d6*o4^2 - 2*d2*d7*o0*o1 + 2*d2*d7*o3*o4 - 6*d2*o0*o1^2 - 4*d2*o0*o1*o4 - 4*d2*o0*o1*o7 - 4*d2*o0*o1 + 2*d2*o0*o4*o7 - 2*d2*o1^2*o3 - 2*d2*o1^2*o6 - 2*d2*o1^2 + 2*d2*o1*o3*o7 + 2*d2*o1*o4*o6 - 2*d2*o1 - 2*d3*d5 - d3*d8 - 2*d3*o2 - 2*d3*o5 + 2*d3*o7 - 2*d3*o8 - 2*d3 - 2*d4*o2 + 2*d4*o6 - d5*d6 - 2*d5*o0 - 2*d5*o1 - 2*d5*o3 - 2*d5*o6 - 2*d5 - 2*d7*o2 + 2*d7*o4 - 2*d8*o1 + 2*o0*o4 - 8*o1*o2 + 2*o1*o3 - 4*o1*o5 + 2*o1*o7 - 4*o1*o8 - 4*o1 - 4*o2*o4 - 4*o2*o7 - 4*o2 + 2*o3*o5 + 2*o4*o8 + 2*o5*o7) = 0 := by
  have hq : certD121 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD121_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD121_add, certD121_four] at hq
  linear_combination (1/2 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq120 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-2*d0*d1*d4 - 2*d0*d1*d7 - 4*d0*d1*o1 - d0*d4^2 - 2*d0*d4*d7 - 4*d0*d4*o1 - 2*d0*d4*o4 - 4*d0*d4 - d0*d7^2 - 4*d0*d7*o1 - 2*d0*d7*o7 - 2*d0*d7 - 4*d0*o1^2 - 2*d0*o1*o4 - 2*d0*o1*o7 - 6*d0*o1 + d0*o4^2 + 2*d0*o4*o7 + d0*o7^2 - d0 - d1^2*d3 - d1^2*d6 - 2*d1^2*o0 - 2*d1*d3*d4 - 2*d1*d3*d7 - 4*d1*d3*o1 - 2*d1*d3*o4 - 4*d1*d3 - 2*d1*d4*d6 - 4*d1*d4*o0 - 2*d1*d4*o3 - 2*d1*d4 - 2*d1*d6*d7 - 4*d1*d6*o1 - 2*d1*d6*o7 - 2*d1*d6 - 4*d1*d7*o0 - 2*d1*d7*o6 - 4*d1*d7 - 8*d1*o0*o1 - 2*d1*o0*o4 - 2*d1*o0*o7 - 6*d1*o0 - 2*d1*o1*o3 - 2*d1*o1*o6 - 6*d1*o1 + 2*d1*o3*o4 + 2*d1*o3*o7 + 2*d1*o4*o6 + 2*d1*o6*o7 - 2*d1 - 2*d3*d4*d7 - 4*d3*d4 - d3*d7^2 - 2*d3*d7*o1 - 2*d3*d7*o4 - 2*d3*d7*o7 - 4*d3*d7 - d3*o1^2 - 6*d3*o1 - 4*d3*o4 + d3*o7^2 - 2*d3*o7 - 4*d3 - d4^2*d6 - 2*d4*d6*d7 - 2*d4*d6*o1 - 2*d4*d6*o4 - 2*d4*d6*o7 - 4*d4*d6 - 2*d4*d7*o0 - 2*d4*d7*o3 - 2*d4*d7*o6 - 4*d4*d7 - 2*d4*o0*o1 - 6*d4*o0 - 2*d4*o1 - 4*d4*o3 + 2*d4*o6*o7 - 2*d4*o6 - 6*d4 - d6*o1^2 - 2*d6*o1 + d6*o4^2 - d6 - 2*d7^2 - 2*d7*o0*o1 - 2*d7*o0 - 6*d7*o1 + 2*d7*o3*o4 - 2*d7*o4 - 4*d7*o7 - 6*d7 - 6*o0*o1^2 - 4*o0*o1*o4 - 4*o0*o1*o7 - 12*o0*o1 + 2*o0*o4*o7 - 2*o0*o4 - 4*o0*o7 - 6*o0 - 2*o1^2*o3 - 2*o1^2*o6 - 6*o1^2 + 2*o1*o3*o7 - 2*o1*o3 + 2*o1*o4*o6 - 4*o1*o4 - 4*o1*o6 - 2*o1*o7 - 10*o1 + 4*o3*o4 + 2*o3*o7 + 2*o4*o6 + 2*o4*o7 - 2*o4 - 2*o6 + 2*o7^2 - 2*o7 - 6) = 0 := by
  have hq : certD120 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD120_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD120_add, certD120_four] at hq
  linear_combination (1/2 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq112 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-2*d0*d1*d5*d8 - 2*d0*d1*o2^2 - 2*d0*d2*d4*d8 - 2*d0*d2*d5*d7 - 4*d0*d2*o1*o2 - 2*d0*d4*d5*d8 - d0*d4*d8^2 - 2*d0*d4*d8*o2 - 2*d0*d4*d8*o5 - 2*d0*d4*d8*o8 - 2*d0*d4*d8 - d0*d4*o2^2 + d0*d4*o8^2 - d0*d5^2*d7 - 2*d0*d5*d7*d8 - 2*d0*d5*d7*o2 - 2*d0*d5*d7*o5 - 2*d0*d5*d7*o8 - 2*d0*d5*d7 - 2*d0*d5*d8*o1 - 2*d0*d5*d8*o4 - 2*d0*d5*d8*o7 - 2*d0*d5*d8 - 2*d0*d5*o1*o2 + 2*d0*d5*o7*o8 - d0*d7*o2^2 + d0*d7*o5^2 - 2*d0*d8*o1*o2 + 2*d0*d8*o4*o5 - 6*d0*o1*o2^2 - 4*d0*o1*o2*o5 - 4*d0*o1*o2*o8 - 4*d0*o1*o2 + 2*d0*o1*o5*o8 - 2*d0*o2^2*o4 - 2*d0*o2^2*o7 - 2*d0*o2^2 + 2*d0*o2*o4*o8 + 2*d0*o2*o5*o7 - 2*d1*d2*d3*d8 - 2*d1*d2*d5*d6 - 4*d1*d2*o0*o2 - 2*d1*d3*d5*d8 - d1*d3*d8^2 - 2*d1*d3*d8*o2 - 2*d1*d3*d8*o5 - 2*d1*d3*d8*o8 - 2*d1*d3*d8 - d1*d3*o2^2 + d1*d3*o8^2 - d1*d5^2*d6 - 2*d1*d5*d6*d8 - 2*d1*d5*d6*o2 - 2*d1*d5*d6*o5 - 2*d1*d5*d6*o8 - 2*d1*d5*d6 - 2*d1*d5*d8*o0 - 2*d1*d5*d8*o3 - 2*d1*d5*d8*o6 - 2*d1*d5*d8 - 2*d1*d5*o0*o2 + 2*d1*d5*o6*o8 - d1*d6*o2^2 + d1*d6*o5^2 - 2*d1*d8*o0*o2 + 2*d1*d8*o3*o5 - 6*d1*o0*o2^2 - 4*d1*o0*o2*o5 - 4*d1*o0*o2*o8 - 4*d1*o0*o2 + 2*d1*o0*o5*o8 - 2*d1*o2^2*o3 - 2*d1*o2^2*o6 - 2*d1*o2^2 + 2*d1*o2*o3*o8 + 2*d1*o2*o5*o6 - d2^2*d3*d7 - d2^2*d4*d6 - 2*d2^2*o0*o1 - 2*d2*d3*d4*d8 - 2*d2*d3*d5*d7 - 2*d2*d3*d7*d8 - 2*d2*d3*d7*o2 - 2*d2*d3*d7*o5 - 2*d2*d3*d7*o8 - 2*d2*d3*d7 - 2*d2*d3*d8*o1 - 2*d2*d3*d8*o4 - 2*d2*d3*d8*o7 - 2*d2*d3*d8 - 2*d2*d3*o1*o2 + 2*d2*d3*o7*o8 - 2*d2*d4*d5*d6 - 2*d2*d4*d6*d8 - 2*d2*d4*d6*o2 - 2*d2*d4*d6*o5 - 2*d2*d4*d6*o8 - 2*d2*d4*d6 - 2*d2*d4*d8*o0 - 2*d2*d4*d8*o3 - 2*d2*d4*d8*o6 - 2*d2*d4*d8 - 2*d2*d4*o0*o2 + 2*d2*d4*o6*o8 - 2*d2*d5*d6*d7 - 2*d2*d5*d6*o1 - 2*d2*d5*d6*o4 - 2*d2*d5*d6*o7 - 2*d2*d5*d6 - 2*d2*d5*d7*o0 - 2*d2*d5*d7*o3 - 2*d2*d5*d7*o6 - 2*d2*d5*d7 - 2*d2*d5*o0*o1 + 2*d2*d5*o6*o7 - 2*d2*d6*o1*o2 + 2*d2*d6*o4*o5 - 2*d2*d7*o0*o2 + 2*d2*d7*o3*o5 - 2*d2*d8*o0*o1 + 2*d2*d8*o3*o4 - 12*d2*o0*o1*o2 - 4*d2*o0*o1*o5 - 4*d2*o0*o1*o8 - 4*d2*o0*o1 - 4*d2*o0*o2*o4 - 4*d2*o0*o2*o7 - 4*d2*o0*o2 + 2*d2*o0*o4*o8 + 2*d2*o0*o5*o7 - 4*d2*o1*o2*o3 - 4*d2*o1*o2*o6 - 4*d2*o1*o2 + 2*d2*o1*o3*o8 + 2*d2*o1*o5*o6 + 2*d2*o2*o3*o7 + 2*d2*o2*o4*o6 - 2*d2*o2 + d3*d7 + 2*d3*o8 + d4*d6 - 2*d5*o2 + 2*d5*o6 + 2*d7*o5 - 2*d8*o2 + 2*d8*o4 + 2*o0*o1 + 2*o0*o5 + 2*o1*o8 - 4*o2^2 + 2*o2*o3 - 4*o2*o5 + 2*o2*o7 - 4*o2*o8 - 4*o2 + 2*o5*o8) = 0 := by
  have hq : certD112 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD112_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD112_add, certD112_four] at hq
  linear_combination (1/2 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq111 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d0*d1*d5 - d0*d1*d8 - 2*d0*d1*o2 - d0*d2*d4 - d0*d2*d7 - 2*d0*d2*o1 - d0*d4*d5 - d0*d4*d8 - 2*d0*d4*o2 - d0*d4*o5 - d0*d4 - d0*d5*d7 - 2*d0*d5*o1 - d0*d5*o4 - 2*d0*d5 - d0*d7*d8 - 2*d0*d7*o2 - d0*d7*o8 - d0*d7 - 2*d0*d8*o1 - d0*d8*o7 - d0*d8 - 4*d0*o1*o2 - d0*o1*o5 - d0*o1*o8 - 2*d0*o1 - d0*o2*o4 - d0*o2*o7 - 3*d0*o2 + d0*o4*o5 + d0*o4*o8 + d0*o5*o7 + d0*o7*o8 - d1*d2*d3 - d1*d2*d6 - 2*d1*d2*o0 - d1*d3*d5 - d1*d3*d8 - 2*d1*d3*o2 - d1*d3*o5 - d1*d3 - d1*d5*d6 - 2*d1*d5*o0 - d1*d5*o3 - d1*d5 - d1*d6*d8 - 2*d1*d6*o2 - d1*d6*o8 - d1*d6 - 2*d1*d8*o0 - d1*d8*o6 - 2*d1*d8 - 4*d1*o0*o2 - d1*o0*o5 - d1*o0*o8 - 2*d1*o0 - d1*o2*o3 - d1*o2*o6 - 3*d1*o2 + d1*o3*o5 + d1*o3*o8 + d1*o5*o6 + d1*o6*o8 - d2*d3*d4 - d2*d3*d7 - 2*d2*d3*o1 - d2*d3*o4 - 2*d2*d3 - d2*d4*d6 - 2*d2*d4*o0 - d2*d4*o3 - d2*d4 - d2*d6*d7 - 2*d2*d6*o1 - d2*d6*o7 - d2*d6 - 2*d2*d7*o0 - d2*d7*o6 - 2*d2*d7 - 4*d2*o0*o1 - d2*o0*o4 - d2*o0*o7 - 3*d2*o0 - d2*o1*o3 - d2*o1*o6 - 3*d2*o1 + d2*o3*o4 + d2*o3*o7 + d2*o4*o6 + d2*o6*o7 - d2 - d3*d4*d8 - d3*d5*d7 - 2*d3*d5 - d3*d7*d8 - d3*d7*o2 - d3*d7*o5 - d3*d7*o8 - d3*d8*o1 - d3*d8*o4 - d3*d8*o7 - 2*d3*d8 - d3*o1*o2 - 3*d3*o2 - 2*d3*o5 + d3*o7*o8 + d3*o7 - d3*o8 - d3 - d4*d5*d6 - d4*d6*d8 - d4*d6*o2 - d4*d6*o5 - d4*d6*o8 - d4*d8*o0 - d4*d8*o3 - d4*d8*o6 - 2*d4*d8 - d4*o0*o2 - d4*o2 + d4*o6*o8 + d4*o6 - d5*d6*d7 - d5*d6*o1 - d5*d6*o4 - d5*d6*o7 - 2*d5*d6 - d5*d7*o0 - d5*d7*o3 - d5*d7*o6 - 2*d5*d7 - d5*o0*o1 - 3*d5*o0 - d5*o1 - 2*d5*o3 + d5*o6*o7 - d5*o6 - 3*d5 - d6*o1*o2 - d6*o2 + d6*o4*o5 + d6*o4 - 2*d7*d8 - d7*o0*o2 - 3*d7*o2 + d7*o3*o5 + d7*o3 - d7*o5 - 2*d7*o8 - d7 - d8*o0*o1 - d8*o0 - 3*d8*o1 + d8*o3*o4 - d8*o4 - 2*d8*o7 - 3*d8 - 6*o0*o1*o2 - 2*o0*o1*o5 - 2*o0*o1*o8 - 2*o0*o2*o4 - 2*o0*o2*o7 - 6*o0*o2 + o0*o4*o8 + o0*o4 + o0*o5*o7 - o0*o5 + o0*o7 - 2*o0*o8 - o0 - 2*o1*o2*o3 - 2*o1*o2*o6 - 6*o1*o2 + o1*o3*o8 + o1*o3 + o1*o5*o6 - 2*o1*o5 + o1*o6 - o1*o8 - o1 + o2*o3*o7 - o2*o3 + o2*o4*o6 - 2*o2*o4 - 2*o2*o6 - o2*o7 - 5*o2 + 2*o3*o5 + o3*o8 + o3 + o4*o8 + o4 + o5*o6 + o5*o7 - o5 + o6 + 2*o7*o8 + o7 - o8 - 2) = 0 := by
  have hq : certD111 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD111_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD111_add, certD111_four] at hq
  linear_combination (1/2 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq110 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-2*d0*d1 - d0*d4 - d0*d7 - 2*d0*o1 - 4*d0 - d1*d3 - d1*d6 - 2*d1*o0 - 4*d1 - 2*d3*d4 - d3*d7 - 4*d3*o1 - 2*d3*o4 - 2*d3 - d4*d6 - 4*d4*o0 - 2*d4*o3 - 4*d4 - 2*d6*d7 - 4*d6*o1 - 2*d6*o7 - 4*d6 - 4*d7*o0 - 2*d7*o6 - 2*d7 - 6*o0*o1 - 2*o0*o4 - 2*o0*o7 - 6*o0 - 2*o1*o3 - 2*o1*o6 - 6*o1 + 2*o3*o4 + 2*o3*o7 + 2*o4*o6 - 2*o4 + 2*o6*o7 - 2*o6 - 6) = 0 := by
  have hq : certD110 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD110_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD110_add, certD110_four] at hq
  linear_combination (1/2 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq103 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-2*d0*d2*d5*d8 - 2*d0*d2*o2^2 - d0*d5^2*d8 - d0*d5*d8^2 - 2*d0*d5*d8*o2 - 2*d0*d5*d8*o5 - 2*d0*d5*d8*o8 - 2*d0*d5*d8 - d0*d5*o2^2 + d0*d5*o8^2 - d0*d8*o2^2 + d0*d8*o5^2 - 2*d0*o2^3 - 2*d0*o2^2*o5 - 2*d0*o2^2*o8 - 2*d0*o2^2 + 2*d0*o2*o5*o8 - d2^2*d3*d8 - d2^2*d5*d6 - 2*d2^2*o0*o2 - 2*d2*d3*d5*d8 - d2*d3*d8^2 - 2*d2*d3*d8*o2 - 2*d2*d3*d8*o5 - 2*d2*d3*d8*o8 - 2*d2*d3*d8 - d2*d3*o2^2 + d2*d3*o8^2 - d2*d5^2*d6 - 2*d2*d5*d6*d8 - 2*d2*d5*d6*o2 - 2*d2*d5*d6*o5 - 2*d2*d5*d6*o8 - 2*d2*d5*d6 - 2*d2*d5*d8*o0 - 2*d2*d5*d8*o3 - 2*d2*d5*d8*o6 - 2*d2*d5*d8 - 2*d2*d5*o0*o2 + 2*d2*d5*o6*o8 - d2*d6*o2^2 + d2*d6*o5^2 - 2*d2*d8*o0*o2 + 2*d2*d8*o3*o5 - 6*d2*o0*o2^2 - 4*d2*o0*o2*o5 - 4*d2*o0*o2*o8 - 4*d2*o0*o2 + 2*d2*o0*o5*o8 - 2*d2*o2^2*o3 - 2*d2*o2^2*o6 - 2*d2*o2^2 + 2*d2*o2*o3*o8 + 2*d2*o2*o5*o6 + d3*d8 + d5*d6 + 2*d8*o5 + 2*o0*o2 + 2*o2*o8) = 0 := by
  have hq : certD103 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD103_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD103_add, certD103_four] at hq
  linear_combination (1/6 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq102 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-2*d0*d2*d5 - 2*d0*d2*d8 - 4*d0*d2*o2 - d0*d5^2 - 2*d0*d5*d8 - 4*d0*d5*o2 - 2*d0*d5*o5 - 2*d0*d5 - d0*d8^2 - 4*d0*d8*o2 - 2*d0*d8*o8 - 2*d0*d8 - 4*d0*o2^2 - 2*d0*o2*o5 - 2*d0*o2*o8 - 4*d0*o2 + d0*o5^2 + 2*d0*o5*o8 + d0*o8^2 - d2^2*d3 - d2^2*d6 - 2*d2^2*o0 - 2*d2*d3*d5 - 2*d2*d3*d8 - 4*d2*d3*o2 - 2*d2*d3*o5 - 2*d2*d3 - 2*d2*d5*d6 - 4*d2*d5*o0 - 2*d2*d5*o3 - 2*d2*d5 - 2*d2*d6*d8 - 4*d2*d6*o2 - 2*d2*d6*o8 - 2*d2*d6 - 4*d2*d8*o0 - 2*d2*d8*o6 - 4*d2*d8 - 8*d2*o0*o2 - 2*d2*o0*o5 - 2*d2*o0*o8 - 4*d2*o0 - 2*d2*o2*o3 - 2*d2*o2*o6 - 6*d2*o2 + 2*d2*o3*o5 + 2*d2*o3*o8 + 2*d2*o5*o6 + 2*d2*o6*o8 - 2*d3*d5*d8 - d3*d8^2 - 2*d3*d8*o2 - 2*d3*d8*o5 - 2*d3*d8*o8 - d3*o2^2 + d3*o8^2 + 2*d3*o8 + d3 - d5^2*d6 - 2*d5*d6*d8 - 2*d5*d6*o2 - 2*d5*d6*o5 - 2*d5*d6*o8 - 2*d5*d8*o0 - 2*d5*d8*o3 - 2*d5*d8*o6 - 4*d5*d8 - 2*d5*o0*o2 - 2*d5*o2 + 2*d5*o6*o8 + 2*d5*o6 - d6*o2^2 + d6*o5^2 + 2*d6*o5 + d6 - 2*d8^2 - 2*d8*o0*o2 - 6*d8*o2 + 2*d8*o3*o5 + 2*d8*o3 - 2*d8*o5 - 4*d8*o8 - 2*d8 - 6*o0*o2^2 - 4*o0*o2*o5 - 4*o0*o2*o8 + 2*o0*o5*o8 + 2*o0*o5 + 2*o0*o8 + 2*o0 - 2*o2^2*o3 - 2*o2^2*o6 - 6*o2^2 + 2*o2*o3*o8 + 2*o2*o3 + 2*o2*o5*o6 - 4*o2*o5 + 2*o2*o6 - 2*o2*o8 - 2*o2 + 2*o5*o8 + 2*o5 + 2*o8^2 + 2*o8) = 0 := by
  have hq : certD102 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD102_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD102_add, certD102_four] at hq
  linear_combination (1/2 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq101 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-2*d0*d2 - d0*d5 - d0*d8 - 2*d0*o2 - 2*d0 - d2*d3 - d2*d6 - 2*d2*o0 - 4*d2 - 2*d3*d5 - d3*d8 - 4*d3*o2 - 2*d3*o5 - d5*d6 - 4*d5*o0 - 2*d5*o3 - 4*d5 - 2*d6*d8 - 4*d6*o2 - 2*d6*o8 - 4*d8*o0 - 2*d8*o6 - 2*d8 - 6*o0*o2 - 2*o0*o5 - 2*o0*o8 - 2*o2*o3 - 2*o2*o6 - 6*o2 + 2*o3*o5 + 2*o3*o8 + 2*o3 + 2*o5*o6 - 2*o5 + 2*o6*o8 + 2*o6 - 2) = 0 := by
  have hq : certD101 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD101_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD101_add, certD101_four] at hq
  linear_combination (1/2 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq040 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d1^2*d4*d7 - d1^2*o1^2 - d1*d4^2*d7 - d1*d4*d7^2 - 2*d1*d4*d7*o1 - 2*d1*d4*d7*o4 - 2*d1*d4*d7*o7 - 2*d1*d4*d7 - d1*d4*o1^2 + d1*d4*o7^2 - d1*d4 - d1*d7*o1^2 + d1*d7*o4^2 - 2*d1*o1^3 - 2*d1*o1^2*o4 - 2*d1*o1^2*o7 - 2*d1*o1^2 + 2*d1*o1*o4*o7 - d4^2 - d4*d7 - 2*d4*o1 - 2*d4*o4 - 2*d4*o7 - 2*d4 + o4^2) = 0 := by
  have hq : certD040 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD040_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD040_add, certD040_four] at hq
  linear_combination (1/24 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq031 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d1^2*d4*d8 - d1^2*d5*d7 - 2*d1^2*o1*o2 - 2*d1*d2*d4*d7 - 2*d1*d2*o1^2 - d1*d4^2*d8 - 2*d1*d4*d5*d7 - 2*d1*d4*d7*d8 - 2*d1*d4*d7*o2 - 2*d1*d4*d7*o5 - 2*d1*d4*d7*o8 - 2*d1*d4*d7 - 2*d1*d4*d8*o1 - 2*d1*d4*d8*o4 - 2*d1*d4*d8*o7 - 2*d1*d4*d8 - 2*d1*d4*o1*o2 + 2*d1*d4*o7*o8 - d1*d5*d7^2 - 2*d1*d5*d7*o1 - 2*d1*d5*d7*o4 - 2*d1*d5*d7*o7 - 2*d1*d5*d7 - d1*d5*o1^2 + d1*d5*o7^2 - d1*d5 - 2*d1*d7*o1*o2 + 2*d1*d7*o4*o5 - d1*d8*o1^2 + d1*d8*o4^2 - 6*d1*o1^2*o2 - 2*d1*o1^2*o5 - 2*d1*o1^2*o8 - 2*d1*o1^2 - 4*d1*o1*o2*o4 - 4*d1*o1*o2*o7 - 4*d1*o1*o2 + 2*d1*o1*o4*o8 + 2*d1*o1*o5*o7 + 2*d1*o2*o4*o7 - d2*d4^2*d7 - d2*d4*d7^2 - 2*d2*d4*d7*o1 - 2*d2*d4*d7*o4 - 2*d2*d4*d7*o7 - 2*d2*d4*d7 - d2*d4*o1^2 + d2*d4*o7^2 - d2*d4 - d2*d7*o1^2 + d2*d7*o4^2 - 2*d2*o1^3 - 2*d2*o1^2*o4 - 2*d2*o1^2*o7 - 2*d2*o1^2 + 2*d2*o1*o4*o7 - 2*d4*d5 - d4*d8 - 2*d4*o2 - 2*d4*o5 + 2*d4*o7 - 2*d4*o8 - 2*d4 - d5*d7 - 2*d5*o1 - 2*d5*o4 - 2*d5*o7 - 2*d5 + 2*o1*o4 + 2*o4*o5) = 0 := by
  have hq : certD031 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD031_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD031_add, certD031_four] at hq
  linear_combination (1/6 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq030 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d1^2*d4 - d1^2*d7 - 2*d1^2*o1 - d1*d4^2 - 2*d1*d4*d7 - 4*d1*d4*o1 - 2*d1*d4*o4 - 4*d1*d4 - d1*d7^2 - 4*d1*d7*o1 - 2*d1*d7*o7 - 2*d1*d7 - 4*d1*o1^2 - 2*d1*o1*o4 - 2*d1*o1*o7 - 6*d1*o1 + d1*o4^2 + 2*d1*o4*o7 + d1*o7^2 - d1 - d4^2*d7 - 2*d4^2 - d4*d7^2 - 2*d4*d7*o1 - 2*d4*d7*o4 - 2*d4*d7*o7 - 4*d4*d7 - d4*o1^2 - 6*d4*o1 - 4*d4*o4 + d4*o7^2 - 2*d4*o7 - 4*d4 - d7*o1^2 - 2*d7*o1 + d7*o4^2 - d7 - 2*o1^3 - 2*o1^2*o4 - 2*o1^2*o7 - 6*o1^2 + 2*o1*o4*o7 - 2*o1*o4 - 4*o1*o7 - 6*o1 + 2*o4^2 + 2*o4*o7 - 2*o7 - 2) = 0 := by
  have hq : certD030 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD030_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD030_add, certD030_four] at hq
  linear_combination (1/6 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq022 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d1^2*d5*d8 - d1^2*o2^2 - 2*d1*d2*d4*d8 - 2*d1*d2*d5*d7 - 4*d1*d2*o1*o2 - 2*d1*d4*d5*d8 - d1*d4*d8^2 - 2*d1*d4*d8*o2 - 2*d1*d4*d8*o5 - 2*d1*d4*d8*o8 - 2*d1*d4*d8 - d1*d4*o2^2 + d1*d4*o8^2 - d1*d5^2*d7 - 2*d1*d5*d7*d8 - 2*d1*d5*d7*o2 - 2*d1*d5*d7*o5 - 2*d1*d5*d7*o8 - 2*d1*d5*d7 - 2*d1*d5*d8*o1 - 2*d1*d5*d8*o4 - 2*d1*d5*d8*o7 - 2*d1*d5*d8 - 2*d1*d5*o1*o2 + 2*d1*d5*o7*o8 - d1*d7*o2^2 + d1*d7*o5^2 - 2*d1*d8*o1*o2 + 2*d1*d8*o4*o5 - 6*d1*o1*o2^2 - 4*d1*o1*o2*o5 - 4*d1*o1*o2*o8 - 4*d1*o1*o2 + 2*d1*o1*o5*o8 - 2*d1*o2^2*o4 - 2*d1*o2^2*o7 - 2*d1*o2^2 + 2*d1*o2*o4*o8 + 2*d1*o2*o5*o7 - d2^2*d4*d7 - d2^2*o1^2 - d2*d4^2*d8 - 2*d2*d4*d5*d7 - 2*d2*d4*d7*d8 - 2*d2*d4*d7*o2 - 2*d2*d4*d7*o5 - 2*d2*d4*d7*o8 - 2*d2*d4*d7 - 2*d2*d4*d8*o1 - 2*d2*d4*d8*o4 - 2*d2*d4*d8*o7 - 2*d2*d4*d8 - 2*d2*d4*o1*o2 + 2*d2*d4*o7*o8 - d2*d5*d7^2 - 2*d2*d5*d7*o1 - 2*d2*d5*d7*o4 - 2*d2*d5*d7*o7 - 2*d2*d5*d7 - d2*d5*o1^2 + d2*d5*o7^2 - d2*d5 - 2*d2*d7*o1*o2 + 2*d2*d7*o4*o5 - d2*d8*o1^2 + d2*d8*o4^2 - 6*d2*o1^2*o2 - 2*d2*o1^2*o5 - 2*d2*o1^2*o8 - 2*d2*o1^2 - 4*d2*o1*o2*o4 - 4*d2*o1*o2*o7 - 4*d2*o1*o2 + 2*d2*o1*o4*o8 + 2*d2*o1*o5*o7 + 2*d2*o2*o4*o7 + d4*d7 + 2*d4*o8 - d5^2 - d5*d8 - 2*d5*o2 - 2*d5*o5 + 2*d5*o7 - 2*d5*o8 - 2*d5 + o1^2 + 2*o1*o5 + 2*o2*o4 + o5^2) = 0 := by
  have hq : certD022 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD022_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD022_add, certD022_four] at hq
  linear_combination (1/4 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq021 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d1^2*d5 - d1^2*d8 - 2*d1^2*o2 - 2*d1*d2*d4 - 2*d1*d2*d7 - 4*d1*d2*o1 - 2*d1*d4*d5 - 2*d1*d4*d8 - 4*d1*d4*o2 - 2*d1*d4*o5 - 2*d1*d4 - 2*d1*d5*d7 - 4*d1*d5*o1 - 2*d1*d5*o4 - 4*d1*d5 - 2*d1*d7*d8 - 4*d1*d7*o2 - 2*d1*d7*o8 - 2*d1*d7 - 4*d1*d8*o1 - 2*d1*d8*o7 - 2*d1*d8 - 8*d1*o1*o2 - 2*d1*o1*o5 - 2*d1*o1*o8 - 4*d1*o1 - 2*d1*o2*o4 - 2*d1*o2*o7 - 6*d1*o2 + 2*d1*o4*o5 + 2*d1*o4*o8 + 2*d1*o5*o7 + 2*d1*o7*o8 - d2*d4^2 - 2*d2*d4*d7 - 4*d2*d4*o1 - 2*d2*d4*o4 - 4*d2*d4 - d2*d7^2 - 4*d2*d7*o1 - 2*d2*d7*o7 - 2*d2*d7 - 4*d2*o1^2 - 2*d2*o1*o4 - 2*d2*o1*o7 - 6*d2*o1 + d2*o4^2 + 2*d2*o4*o7 + d2*o7^2 - d2 - d4^2*d8 - 2*d4*d5*d7 - 4*d4*d5 - 2*d4*d7*d8 - 2*d4*d7*o2 - 2*d4*d7*o5 - 2*d4*d7*o8 - 2*d4*d8*o1 - 2*d4*d8*o4 - 2*d4*d8*o7 - 4*d4*d8 - 2*d4*o1*o2 - 6*d4*o2 - 4*d4*o5 + 2*d4*o7*o8 + 2*d4*o7 - 2*d4*o8 - 2*d4 - d5*d7^2 - 2*d5*d7*o1 - 2*d5*d7*o4 - 2*d5*d7*o7 - 4*d5*d7 - d5*o1^2 - 6*d5*o1 - 4*d5*o4 + d5*o7^2 - 2*d5*o7 - 4*d5 - 2*d7*o1*o2 - 2*d7*o2 + 2*d7*o4*o5 + 2*d7*o4 - d8*o1^2 - 2*d8*o1 + d8*o4^2 - d8 - 6*o1^2*o2 - 2*o1^2*o5 - 2*o1^2*o8 - 4*o1*o2*o4 - 4*o1*o2*o7 - 12*o1*o2 + 2*o1*o4*o8 + 2*o1*o4 + 2*o1*o5*o7 - 2*o1*o5 + 2*o1*o7 - 4*o1*o8 - 2*o1 + 2*o2*o4*o7 - 2*o2*o4 - 4*o2*o7 - 6*o2 + 4*o4*o5 + 2*o4*o8 + 2*o4 + 2*o5*o7 + 2*o7 - 2*o8 - 2) = 0 := by
  have hq : certD021 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD021_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD021_add, certD021_four] at hq
  linear_combination (1/2 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq020 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d1^2 - d1*d4 - d1*d7 - 2*d1*o1 - 4*d1 - d4^2 - d4*d7 - 4*d4*o1 - 2*d4*o4 - 2*d4 - d7^2 - 4*d7*o1 - 2*d7*o7 - 4*d7 - 3*o1^2 - 2*o1*o4 - 2*o1*o7 - 6*o1 + o4^2 + 2*o4*o7 + o7^2 - 2*o7 - 3) = 0 := by
  have hq : certD020 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD020_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD020_add, certD020_four] at hq
  linear_combination (1/4 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq013 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-2*d1*d2*d5*d8 - 2*d1*d2*o2^2 - d1*d5^2*d8 - d1*d5*d8^2 - 2*d1*d5*d8*o2 - 2*d1*d5*d8*o5 - 2*d1*d5*d8*o8 - 2*d1*d5*d8 - d1*d5*o2^2 + d1*d5*o8^2 - d1*d8*o2^2 + d1*d8*o5^2 - 2*d1*o2^3 - 2*d1*o2^2*o5 - 2*d1*o2^2*o8 - 2*d1*o2^2 + 2*d1*o2*o5*o8 - d2^2*d4*d8 - d2^2*d5*d7 - 2*d2^2*o1*o2 - 2*d2*d4*d5*d8 - d2*d4*d8^2 - 2*d2*d4*d8*o2 - 2*d2*d4*d8*o5 - 2*d2*d4*d8*o8 - 2*d2*d4*d8 - d2*d4*o2^2 + d2*d4*o8^2 - d2*d5^2*d7 - 2*d2*d5*d7*d8 - 2*d2*d5*d7*o2 - 2*d2*d5*d7*o5 - 2*d2*d5*d7*o8 - 2*d2*d5*d7 - 2*d2*d5*d8*o1 - 2*d2*d5*d8*o4 - 2*d2*d5*d8*o7 - 2*d2*d5*d8 - 2*d2*d5*o1*o2 + 2*d2*d5*o7*o8 - d2*d7*o2^2 + d2*d7*o5^2 - 2*d2*d8*o1*o2 + 2*d2*d8*o4*o5 - 6*d2*o1*o2^2 - 4*d2*o1*o2*o5 - 4*d2*o1*o2*o8 - 4*d2*o1*o2 + 2*d2*o1*o5*o8 - 2*d2*o2^2*o4 - 2*d2*o2^2*o7 - 2*d2*o2^2 + 2*d2*o2*o4*o8 + 2*d2*o2*o5*o7 + d4*d8 + d5*d7 + 2*d5*o8 + 2*o1*o2 + 2*o2*o5) = 0 := by
  have hq : certD013 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD013_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD013_add, certD013_four] at hq
  linear_combination (1/6 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq012 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-2*d1*d2*d5 - 2*d1*d2*d8 - 4*d1*d2*o2 - d1*d5^2 - 2*d1*d5*d8 - 4*d1*d5*o2 - 2*d1*d5*o5 - 2*d1*d5 - d1*d8^2 - 4*d1*d8*o2 - 2*d1*d8*o8 - 2*d1*d8 - 4*d1*o2^2 - 2*d1*o2*o5 - 2*d1*o2*o8 - 4*d1*o2 + d1*o5^2 + 2*d1*o5*o8 + d1*o8^2 - d2^2*d4 - d2^2*d7 - 2*d2^2*o1 - 2*d2*d4*d5 - 2*d2*d4*d8 - 4*d2*d4*o2 - 2*d2*d4*o5 - 2*d2*d4 - 2*d2*d5*d7 - 4*d2*d5*o1 - 2*d2*d5*o4 - 4*d2*d5 - 2*d2*d7*d8 - 4*d2*d7*o2 - 2*d2*d7*o8 - 2*d2*d7 - 4*d2*d8*o1 - 2*d2*d8*o7 - 2*d2*d8 - 8*d2*o1*o2 - 2*d2*o1*o5 - 2*d2*o1*o8 - 4*d2*o1 - 2*d2*o2*o4 - 2*d2*o2*o7 - 6*d2*o2 + 2*d2*o4*o5 + 2*d2*o4*o8 + 2*d2*o5*o7 + 2*d2*o7*o8 - 2*d4*d5*d8 - d4*d8^2 - 2*d4*d8*o2 - 2*d4*d8*o5 - 2*d4*d8*o8 - d4*o2^2 + d4*o8^2 + 2*d4*o8 + d4 - d5^2*d7 - 2*d5^2 - 2*d5*d7*d8 - 2*d5*d7*o2 - 2*d5*d7*o5 - 2*d5*d7*o8 - 2*d5*d8*o1 - 2*d5*d8*o4 - 2*d5*d8*o7 - 4*d5*d8 - 2*d5*o1*o2 - 6*d5*o2 - 4*d5*o5 + 2*d5*o7*o8 + 2*d5*o7 - 2*d5*o8 - 2*d5 - d7*o2^2 + d7*o5^2 + 2*d7*o5 + d7 - 2*d8*o1*o2 - 2*d8*o2 + 2*d8*o4*o5 + 2*d8*o4 - 6*o1*o2^2 - 4*o1*o2*o5 - 4*o1*o2*o8 + 2*o1*o5*o8 + 2*o1*o5 + 2*o1*o8 + 2*o1 - 2*o2^2*o4 - 2*o2^2*o7 - 6*o2^2 + 2*o2*o4*o8 + 2*o2*o4 + 2*o2*o5*o7 - 2*o2*o5 + 2*o2*o7 - 4*o2*o8 - 2*o2 + 2*o5^2 + 2*o5*o8 + 2*o5 + 2*o8) = 0 := by
  have hq : certD012 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD012_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD012_add, certD012_four] at hq
  linear_combination (1/2 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq011 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-2*d1*d2 - d1*d5 - d1*d8 - 2*d1*o2 - 2*d1 - d2*d4 - d2*d7 - 2*d2*o1 - 4*d2 - 2*d4*d5 - d4*d8 - 4*d4*o2 - 2*d4*o5 - d5*d7 - 4*d5*o1 - 2*d5*o4 - 2*d5 - 2*d7*d8 - 4*d7*o2 - 2*d7*o8 - 4*d8*o1 - 2*d8*o7 - 4*d8 - 6*o1*o2 - 2*o1*o5 - 2*o1*o8 - 2*o2*o4 - 2*o2*o7 - 6*o2 + 2*o4*o5 + 2*o4*o8 + 2*o4 + 2*o5*o7 + 2*o7*o8 + 2*o7 - 2*o8 - 2) = 0 := by
  have hq : certD011 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD011_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD011_add, certD011_four] at hq
  linear_combination (1/2 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq004 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d2^2*d5*d8 - d2^2*o2^2 - d2*d5^2*d8 - d2*d5*d8^2 - 2*d2*d5*d8*o2 - 2*d2*d5*d8*o5 - 2*d2*d5*d8*o8 - 2*d2*d5*d8 - d2*d5*o2^2 + d2*d5*o8^2 - d2*d8*o2^2 + d2*d8*o5^2 - 2*d2*o2^3 - 2*d2*o2^2*o5 - 2*d2*o2^2*o8 - 2*d2*o2^2 + 2*d2*o2*o5*o8 + d5*d8 + o2^2) = 0 := by
  have hq : certD004 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD004_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD004_add, certD004_four] at hq
  linear_combination (1/24 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq003 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d2^2*d5 - d2^2*d8 - 2*d2^2*o2 - d2*d5^2 - 2*d2*d5*d8 - 4*d2*d5*o2 - 2*d2*d5*o5 - 2*d2*d5 - d2*d8^2 - 4*d2*d8*o2 - 2*d2*d8*o8 - 2*d2*d8 - 4*d2*o2^2 - 2*d2*o2*o5 - 2*d2*o2*o8 - 4*d2*o2 + d2*o5^2 + 2*d2*o5*o8 + d2*o8^2 - d5^2*d8 - d5*d8^2 - 2*d5*d8*o2 - 2*d5*d8*o5 - 2*d5*d8*o8 - d5*o2^2 + d5*o8^2 + 2*d5*o8 + d5 - d8*o2^2 + d8*o5^2 + 2*d8*o5 + d8 - 2*o2^3 - 2*o2^2*o5 - 2*o2^2*o8 + 2*o2*o5*o8 + 2*o2*o5 + 2*o2*o8 + 2*o2) = 0 := by
  have hq : certD003 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD003_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD003_add, certD003_four] at hq
  linear_combination (1/6 : ℂ) * hq

set_option maxHeartbeats 4000000 in
theorem certEq002 (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d2^2 - d2*d5 - d2*d8 - 2*d2*o2 - 2*d2 - d5^2 - d5*d8 - 4*d5*o2 - 2*d5*o5 - d8^2 - 4*d8*o2 - 2*d8*o8 - 3*o2^2 - 2*o2*o5 - 2*o2*o8 + o5^2 + 2*o5*o8 + 2*o5 + o8^2 + 2*o8 + 1) = 0 := by
  have hq : certD002 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
    rw [h]
    exact certD002_nat 24
  rw [perm4_poly] at hq
  simp [fullStarMatrix, certD002_add, certD002_four] at hq
  linear_combination (1/4 : ℂ) * hq




section CommonPlaneIntegration

open Matrix

theorem block_zero_det_square {R : Type*} [CommRing R]
    (B D : Matrix (Fin 2) (Fin 2) R) :
    (Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) R) B Bᵀ D).det = B.det ^ 2 := by
  have hs : Equiv.Perm.sign (Equiv.sumComm (Fin 2) (Fin 2)) = 1 := by decide
  have hm :
      (Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) R) B Bᵀ D).submatrix
          (Equiv.sumComm (Fin 2) (Fin 2)) id =
        Matrix.fromBlocks Bᵀ D (0 : Matrix (Fin 2) (Fin 2) R) B := by
    ext i j
    cases i <;> cases j <;> rfl
  have hd := Matrix.det_permute (Equiv.sumComm (Fin 2) (Fin 2))
    (Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) R) B Bᵀ D)
  simpa [hm, hs, Matrix.det_fromBlocks_zero₂₁, pow_two] using hd.symm

theorem block_zero_det_congruence {R : Type*} [CommRing R]
    (M P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
    (B D : Matrix (Fin 2) (Fin 2) R)
    (h : Pᵀ * M * P = Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) R) B Bᵀ D) :
    P.det ^ 2 * M.det = B.det ^ 2 := by
  simpa [Matrix.det_mul, block_zero_det_square, pow_two, mul_assoc, mul_left_comm, mul_comm]
    using congrArg Matrix.det h

open Polynomial

theorem polynomial_det_square_of_constant_congruence
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ[X])
    (P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)
    (B D : Matrix (Fin 2) (Fin 2) ℂ[X]) (hp : P.det ≠ 0)
    (h : (P.map C)ᵀ * M * P.map C =
      Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) ℂ[X]) B Bᵀ D) :
    ∃ p : ℂ[X], M.det = p ^ 2 := by
  have hd : (P.map C).det = C P.det := (C.map_det P).symm
  have hs := block_zero_det_congruence M (P.map C) B D h
  rw [hd] at hs
  have hi : C (P.det)⁻¹ * C P.det = (1 : ℂ[X]) := by
    rw [← map_mul, inv_mul_cancel₀ hp, map_one]
  refine ⟨C (P.det)⁻¹ * B.det, ?_⟩
  calc
    M.det = (C (P.det)⁻¹ * C P.det) ^ 2 * M.det := by rw [hi]; simp
    _ = C (P.det)⁻¹ ^ 2 * (C P.det ^ 2 * M.det) := by ring
    _ = (C (P.det)⁻¹ * B.det) ^ 2 := by rw [hs]; ring

theorem symmetric_zero_block {R : Type*} [CommRing R]
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) (hm : M.IsSymm)
    (hz : ∀ i j : Fin 2, M (Sum.inl i) (Sum.inl j) = 0) :
    M = Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) R)
      (fun i j => M (Sum.inl i) (Sum.inr j))
      (fun i j => M (Sum.inl i) (Sum.inr j))ᵀ
      (fun i j => M (Sum.inr i) (Sum.inr j)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · exact hz i j
  · rfl
  · exact (hm.apply (Sum.inr i) (Sum.inl j)).symm
  · rfl

theorem symmetric_congruence {R : Type*} [CommRing R]
    {n : Type*} [Fintype n]
    (M P : Matrix n n R) (hm : M.IsSymm) : (Pᵀ * M * P).IsSymm := by
  simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose, hm.eq,
    Matrix.mul_assoc]

theorem determinant_pencil_square_of_adapted
    (M N P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)
    (hm : M.IsSymm) (hn : N.IsSymm) (hp : P.det ≠ 0)
    (hm0 : ∀ i j : Fin 2, (Pᵀ * M * P) (Sum.inl i) (Sum.inl j) = 0)
    (hn0 : ∀ i j : Fin 2, (Pᵀ * N * P) (Sum.inl i) (Sum.inl j) = 0) :
    ∃ p : ℂ[X], Matrix.det (fun i j => C (N i j) - X * C (M i j)) = p ^ 2 := by
  let L : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ[X] :=
    N.map C - (X : ℂ[X]) • M.map C
  have hi : (P.map C)ᵀ * L * P.map C =
      (Pᵀ * N * P).map C - (X : ℂ[X]) • (Pᵀ * M * P).map C := by
    simp only [L, Matrix.map_mul, Matrix.transpose_map, mul_sub, sub_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  have hz : ∀ i j : Fin 2, ((P.map C)ᵀ * L * P.map C) (Sum.inl i) (Sum.inl j) = 0 := by
    intro i j
    rw [hi]
    change C ((Pᵀ * N * P) (Sum.inl i) (Sum.inl j)) -
      X * C ((Pᵀ * M * P) (Sum.inl i) (Sum.inl j)) = 0
    rw [hn0, hm0, map_zero, mul_zero, sub_zero]
  have hl : L.IsSymm := (hn.map C).sub ((hm.map C).smul X)
  exact polynomial_det_square_of_constant_congruence L P _ _ hp
    (symmetric_zero_block _ (symmetric_congruence L (P.map C) hl) hz)

theorem symmetric_quadratic_vanishing_polarizes
    {n : Type*} [Fintype n] (M : Matrix n n ℂ) (hm : M.IsSymm)
    (W : Submodule ℂ (n → ℂ))
    (h : ∀ u ∈ W, dotProduct u (M.mulVec u) = 0) :
    ∀ u ∈ W, ∀ v ∈ W, dotProduct u (M.mulVec v) = 0 := by
  intro u hu v hv
  have hz := h (u + v) (W.add_mem hu hv)
  have hu0 := h u hu
  have hv0 := h v hv
  have hc := hm.dotProduct_mulVec_comm (x := u) (y := v)
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, hu0, hv0,
    zero_add, add_zero] at hz
  rw [← hc] at hz
  linear_combination (1 / 2 : ℂ) * hz

theorem congruence_entry_is_pairing {R : Type*} [CommSemiring R]
    {n : Type*} [Fintype n] (M P : Matrix n n R) (i j : n) :
    (Pᵀ * M * P) i j = dotProduct (fun k => P k i) (M.mulVec (fun k => P k j)) := by
  rw [Matrix.mul_assoc]
  rfl

theorem determinant_pencil_square_of_isotropic_columns
    (M N P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)
    (hm : M.IsSymm) (hn : N.IsSymm) (hp : P.det ≠ 0)
    (W : Submodule ℂ ((Fin 2 ⊕ Fin 2) → ℂ))
    (hmem : ∀ j : Fin 2, (fun i => P i (Sum.inl j)) ∈ W)
    (hM : ∀ u ∈ W, ∀ v ∈ W, dotProduct u (M.mulVec v) = 0)
    (hN : ∀ u ∈ W, ∀ v ∈ W, dotProduct u (N.mulVec v) = 0) :
    ∃ p : ℂ[X], Matrix.det (fun i j => C (N i j) - X * C (M i j)) = p ^ 2 := by
  apply determinant_pencil_square_of_adapted M N P hm hn hp
  · intro i j
    rw [congruence_entry_is_pairing]
    exact hM _ (hmem i) _ (hmem j)
  · intro i j
    rw [congruence_entry_is_pairing]
    exact hN _ (hmem i) _ (hmem j)

theorem determinant_pencil_square_of_quadratic_columns
    (M N P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)
    (hm : M.IsSymm) (hn : N.IsSymm) (hp : P.det ≠ 0)
    (W : Submodule ℂ ((Fin 2 ⊕ Fin 2) → ℂ))
    (hmem : ∀ j : Fin 2, (fun i => P i (Sum.inl j)) ∈ W)
    (hM : ∀ u ∈ W, dotProduct u (M.mulVec u) = 0)
    (hN : ∀ u ∈ W, dotProduct u (N.mulVec u) = 0) :
    ∃ p : ℂ[X], Matrix.det (fun i j => C (N i j) - X * C (M i j)) = p ^ 2 := by
  exact determinant_pencil_square_of_isotropic_columns M N P hm hn hp W hmem
    (symmetric_quadratic_vanishing_polarizes M hm W hM)
    (symmetric_quadratic_vanishing_polarizes N hn W hN)


abbrev Index4 := Fin 2 ⊕ Fin 2

theorem exists_adapted_basis
    (W : Submodule ℂ (Index4 → ℂ)) (hdim : Module.finrank ℂ W = 2) :
    ∃ b : Module.Basis Index4 ℂ (Index4 → ℂ),
      ∀ j : Fin 2, b (Sum.inl j) ∈ W := by
  classical
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl W
  have htotal : Module.finrank ℂ (Index4 → ℂ) = 4 := by
    simp [Index4, Module.finrank_fintype_fun_eq_card]
  have hdimU : Module.finrank ℂ U = 2 := by
    have hadd := Submodule.finrank_add_eq_of_isCompl hU
    rw [hdim, htotal] at hadd
    exact Nat.add_left_cancel (show 2 + Module.finrank ℂ U = 2 + 2 from hadd)
  let bW : Module.Basis (Fin 2) ℂ W := Module.finBasisOfFinrankEq ℂ W hdim
  let bU : Module.Basis (Fin 2) ℂ U := Module.finBasisOfFinrankEq ℂ U hdimU
  refine ⟨(bW.prod bU).map (W.prodEquivOfIsCompl U hU), ?_⟩
  intro j
  simp only [Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl',
    Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd,
    ZeroMemClass.coe_zero, add_zero]
  exact (bW j).property

theorem exists_adapted_matrix
    (W : Submodule ℂ (Index4 → ℂ)) (hdim : Module.finrank ℂ W = 2) :
    ∃ P : Matrix Index4 Index4 ℂ,
      P.det ≠ 0 ∧ ∀ j : Fin 2, (fun i => P i (Sum.inl j)) ∈ W := by
  classical
  obtain ⟨b, hb⟩ := exists_adapted_basis W hdim
  let P : Matrix Index4 Index4 ℂ := fun i j => b j i
  refine ⟨P, ?_, ?_⟩
  · apply Matrix.nonsingular_iff_det_ne_zero.mp
    apply Matrix.Nonsingular.of_linearIndependent_col
    change LinearIndependent ℂ (fun j => b j)
    exact b.linearIndependent
  · exact hb


theorem determinant_pencil_square_of_common_isotropic_plane
    (M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)
    (hm : M.IsSymm) (hn : N.IsSymm)
    (W : Submodule ℂ ((Fin 2 ⊕ Fin 2) → ℂ)) (hdim : Module.finrank ℂ W = 2)
    (hM : ∀ u ∈ W, dotProduct u (M.mulVec u) = 0)
    (hN : ∀ u ∈ W, dotProduct u (N.mulVec u) = 0) :
    ∃ p : ℂ[X], Matrix.det (fun i j => C (N i j) - X * C (M i j)) = p ^ 2 := by
  obtain ⟨P, hp, hmem⟩ := exists_adapted_matrix W hdim
  exact determinant_pencil_square_of_quadratic_columns M N P hm hn hp W hmem hM hN


open Polynomial

theorem quartic_square_coefficient_identities {R : Type*} [CommRing R] [NoZeroDivisors R]
    (q p : R[X]) (hdeg : q.natDegree ≤ 4) (hsq : q = p ^ 2) :
    8 * q.coeff 4 ^ 2 * q.coeff 1 -
        4 * q.coeff 4 * q.coeff 3 * q.coeff 2 + q.coeff 3 ^ 3 = 0 ∧
      (4 * q.coeff 4 * q.coeff 2 - q.coeff 3 ^ 2) ^ 2 -
        64 * q.coeff 4 ^ 3 * q.coeff 0 = 0 := by
  have hroot : p.natDegree ≤ 2 := by
    rw [hsq, Polynomial.natDegree_pow] at hdeg
    omega
  have hp3 : p.coeff 3 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hp4 : p.coeff 4 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have h4 : q.coeff 4 = p.coeff 2 ^ 2 := by
    simp [hsq, pow_two, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, hp3, hp4]
  have h3 : q.coeff 3 = 2 * p.coeff 2 * p.coeff 1 := by
    simp [hsq, pow_two, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, hp3]
    ring
  have h2 : q.coeff 2 = p.coeff 1 ^ 2 + 2 * p.coeff 2 * p.coeff 0 := by
    simp [hsq, pow_two, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
    ring
  have h1 : q.coeff 1 = 2 * p.coeff 1 * p.coeff 0 := by
    simp [hsq, pow_two, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
    ring
  have h0 : q.coeff 0 = p.coeff 0 ^ 2 := by simp [hsq, pow_two]
  constructor
  · rw [h4, h3, h2, h1]
    ring
  · rw [h4, h3, h2, h0]
    ring

theorem common_isotropic_plane_coefficient_identities
    (M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)
    (hm : M.IsSymm) (hn : N.IsSymm)
    (W : Submodule ℂ ((Fin 2 ⊕ Fin 2) → ℂ)) (hdim : Module.finrank ℂ W = 2)
    (hM : ∀ u ∈ W, dotProduct u (M.mulVec u) = 0)
    (hN : ∀ u ∈ W, dotProduct u (N.mulVec u) = 0) :
    let q : ℂ[X] := Matrix.det (fun i j => C (N i j) - X * C (M i j))
    8 * q.coeff 4 ^ 2 * q.coeff 1 -
        4 * q.coeff 4 * q.coeff 3 * q.coeff 2 + q.coeff 3 ^ 3 = 0 ∧
      (4 * q.coeff 4 * q.coeff 2 - q.coeff 3 ^ 2) ^ 2 -
        64 * q.coeff 4 ^ 3 * q.coeff 0 = 0 := by
  let q : ℂ[X] := Matrix.det (fun i j => C (N i j) - X * C (M i j))
  obtain ⟨p, hp⟩ := determinant_pencil_square_of_common_isotropic_plane M N hm hn W hdim hM hN
  have hdeg : q.natDegree ≤ 4 := by
    have h := Polynomial.natDegree_det_X_add_C_le (-M) N
    have heq : (X : ℂ[X]) • (-M).map C + N.map C =
        (fun i j => C (N i j) - X * C (M i j)) := by
      apply Matrix.ext
      intro i j
      change X * C (-(M i j)) + C (N i j) = C (N i j) - X * C (M i j)
      rw [map_neg]
      ring
    rw [heq] at h
    simpa [q] using h
  exact quartic_square_coefficient_identities q p hdeg hp

end CommonPlaneIntegration

section FactorMatchingIntegration

open MvPolynomial

noncomputable def binaryLinear (a : Fin 2 → ℂ) : MvPolynomial (Fin 2) ℂ :=
  C (a 0) * X 0 + C (a 1) * X 1

lemma pair_proportional_of_kernel
    (a₀ a₁ d₀ d₁ : ℂ) (ha : a₀ ≠ 0 ∨ a₁ ≠ 0)
    (h : d₀ * (-a₁) + d₁ * a₀ = 0) :
    ∃ r : ℂ, d₀ = r * a₀ ∧ d₁ = r * a₁ := by
  by_cases h₀ : a₀ = 0
  · have h₁ : a₁ ≠ 0 := ha.resolve_left (not_not_intro h₀)
    have hd₀ : d₀ = 0 := by
      have hz : d₀ * a₁ = 0 := by simpa [h₀] using h
      exact (mul_eq_zero.mp hz).resolve_right h₁
    refine ⟨d₁ / a₁, ?_, ?_⟩
    · simp [hd₀, h₀]
    · simp [div_mul_cancel₀ _ h₁]
  · refine ⟨d₀ / a₀, ?_, ?_⟩
    · simp [div_mul_cancel₀ _ h₀]
    · field_simp
      linear_combination h

lemma binaryLinear_proportional_of_kernel
    (a d : Fin 2 → ℂ) (ha : a ≠ 0) (hd : d ≠ 0)
    (h : d 0 * (-a 1) + d 1 * a 0 = 0) :
    ∃ r : ℂ, r ≠ 0 ∧ binaryLinear d = C r * binaryLinear a := by
  have ha' : a 0 ≠ 0 ∨ a 1 ≠ 0 := by
    by_contra hn
    push Not at hn
    apply ha
    funext i
    fin_cases i <;> simp_all
  obtain ⟨r, hr₀, hr₁⟩ := pair_proportional_of_kernel (a 0) (a 1) (d 0) (d 1) ha' h
  have hr : r ≠ 0 := by
    intro hz
    apply hd
    funext i
    fin_cases i <;> simp_all
  refine ⟨r, hr, ?_⟩
  simp only [binaryLinear, hr₀, hr₁, map_mul]
  ring

lemma binaryLinear_one_factor_matches
    (a b c d e f : Fin 2 → ℂ)
    (ha : a ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
    (h : binaryLinear a * binaryLinear b * binaryLinear c =
      binaryLinear d * binaryLinear e * binaryLinear f) :
    (∃ r : ℂ, r ≠ 0 ∧ binaryLinear d = C r * binaryLinear a) ∨
    (∃ r : ℂ, r ≠ 0 ∧ binaryLinear e = C r * binaryLinear a) ∨
    (∃ r : ℂ, r ≠ 0 ∧ binaryLinear f = C r * binaryLinear a) := by
  let point : Fin 2 → ℂ := ![-a 1, a 0]
  have hz := congrArg (MvPolynomial.eval point) h
  have hea : MvPolynomial.eval point (binaryLinear a) = 0 := by
    simp [binaryLinear, point]
    ring
  simp only [map_mul, hea, zero_mul] at hz
  have hz' := mul_eq_zero.mp hz.symm
  rcases hz' with hde | hff
  · rcases mul_eq_zero.mp hde with hdd | hee
    · left
      apply binaryLinear_proportional_of_kernel a d ha hd
      simpa [binaryLinear, point] using hdd
    · right; left
      apply binaryLinear_proportional_of_kernel a e ha he
      simpa [binaryLinear, point] using hee
  · right; right
    apply binaryLinear_proportional_of_kernel a f ha hf
    simpa [binaryLinear, point] using hff

lemma binaryLinear_ne_zero (a : Fin 2 → ℂ) (ha : a ≠ 0) :
    binaryLinear a ≠ 0 := by
  intro hz
  have h₀ := congrArg (MvPolynomial.eval ![(1 : ℂ), 0]) hz
  have h₁ := congrArg (MvPolynomial.eval ![(0 : ℂ), 1]) hz
  simp [binaryLinear] at h₀ h₁
  apply ha
  funext i
  fin_cases i <;> simp_all

lemma binaryLinear_finish_two
    (b c e f : Fin 2 → ℂ) (hb : b ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
    (r : ℂ) (hr : r ≠ 0)
    (h : binaryLinear b * binaryLinear c = C r * binaryLinear e * binaryLinear f) :
    ∃ s t : ℂ, s ≠ 0 ∧ t ≠ 0 ∧ r * s * t = 1 ∧
      ((binaryLinear e = C s * binaryLinear b ∧ binaryLinear f = C t * binaryLinear c) ∨
       (binaryLinear f = C s * binaryLinear b ∧ binaryLinear e = C t * binaryLinear c)) := by
  let point : Fin 2 → ℂ := ![-b 1, b 0]
  have hz := congrArg (MvPolynomial.eval point) h
  have heb : MvPolynomial.eval point (binaryLinear b) = 0 := by
    simp [binaryLinear, point]
    ring
  simp only [map_mul, heb, zero_mul, eval_C] at hz
  have hzero : MvPolynomial.eval point (binaryLinear e) = 0 ∨
      MvPolynomial.eval point (binaryLinear f) = 0 := by
    rcases mul_eq_zero.mp hz.symm with hleft | hright
    · exact Or.inl ((mul_eq_zero.mp hleft).resolve_left hr)
    · exact Or.inr hright
  have finish : ∀ (p q : Fin 2 → ℂ), p ≠ 0 →
      MvPolynomial.eval point (binaryLinear p) = 0 →
      binaryLinear b * binaryLinear c = C r * binaryLinear p * binaryLinear q →
      ∃ s t : ℂ, s ≠ 0 ∧ t ≠ 0 ∧ r * s * t = 1 ∧
        binaryLinear p = C s * binaryLinear b ∧ binaryLinear q = C t * binaryLinear c := by
    intro p q hp hpe hpq
    obtain ⟨s, hs, hps⟩ := binaryLinear_proportional_of_kernel b p hb hp
      (by simpa [binaryLinear, point] using hpe)
    have hrs : r * s ≠ 0 := mul_ne_zero hr hs
    have hc : binaryLinear c = C (r * s) * binaryLinear q := by
      apply mul_left_cancel₀ (binaryLinear_ne_zero b hb)
      calc
        binaryLinear b * binaryLinear c = C r * binaryLinear p * binaryLinear q := hpq
        _ = binaryLinear b * (C (r * s) * binaryLinear q) := by rw [hps, map_mul]; ring
    refine ⟨s, (r * s)⁻¹, hs, inv_ne_zero hrs, mul_inv_cancel₀ hrs, hps, ?_⟩
    rw [hc]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hrs, map_one, one_mul]
  rcases hzero with hez | hfz
  · obtain ⟨s, t, hs, ht, hst, hes, hft⟩ := finish e f he hez h
    exact ⟨s, t, hs, ht, hst, Or.inl ⟨hes, hft⟩⟩
  · have h' : binaryLinear b * binaryLinear c = C r * binaryLinear f * binaryLinear e := by
      calc
        binaryLinear b * binaryLinear c = C r * binaryLinear e * binaryLinear f := h
        _ = C r * binaryLinear f * binaryLinear e := by ring
    obtain ⟨s, t, hs, ht, hst, hfs, het⟩ := finish f e hf hfz h'
    exact ⟨s, t, hs, ht, hst, Or.inr ⟨hfs, het⟩⟩

lemma binaryLinear_cancel_first
    (a b c p q t : Fin 2 → ℂ) (ha : a ≠ 0) (r : ℂ)
    (hp : binaryLinear p = C r * binaryLinear a)
    (h : binaryLinear a * binaryLinear b * binaryLinear c =
      binaryLinear p * binaryLinear q * binaryLinear t) :
    binaryLinear b * binaryLinear c = C r * binaryLinear q * binaryLinear t := by
  apply mul_left_cancel₀ (binaryLinear_ne_zero a ha)
  calc
    binaryLinear a * (binaryLinear b * binaryLinear c) =
        binaryLinear a * binaryLinear b * binaryLinear c := by ring
    _ = binaryLinear p * binaryLinear q * binaryLinear t := h
    _ = binaryLinear a * (C r * binaryLinear q * binaryLinear t) := by rw [hp]; ring

theorem binaryLinear_three_factors_match
    (a b c d e f : Fin 2 → ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
    (h : binaryLinear a * binaryLinear b * binaryLinear c =
      binaryLinear d * binaryLinear e * binaryLinear f) :
    ∃ (π : Equiv.Perm (Fin 3)) (s : Fin 3 → ℂ),
      (∀ i, s i ≠ 0) ∧ s 0 * s 1 * s 2 = 1 ∧
      ∀ i, binaryLinear (![d, e, f] i) = C (s i) * binaryLinear (![a, b, c] (π i)) := by
  rcases binaryLinear_one_factor_matches a b c d e f ha hd he hf h with
    ⟨r, hr, hdr⟩ | ⟨r, hr, her⟩ | ⟨r, hr, hfr⟩
  · have hh := binaryLinear_cancel_first a b c d e f ha r hdr h
    obtain ⟨s, t, hs, ht, hst, hcase⟩ := binaryLinear_finish_two b c e f hb he hf r hr hh
    rcases hcase with ⟨hes, hft⟩ | ⟨hfs, het⟩
    · refine ⟨Equiv.refl _, ![r, s, t], ?_, hst, ?_⟩
      · intro i; fin_cases i <;> simp [hr, hs, ht]
      · intro i; fin_cases i <;> simp [hdr, hes, hft]
    · refine ⟨Equiv.swap 1 2, ![r, t, s], ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp [hr, hs, ht]
      · simpa [mul_assoc, mul_comm, mul_left_comm] using hst
      · intro i; fin_cases i <;> simp [Equiv.swap_apply_def, hdr, het, hfs]
  · have h' : binaryLinear a * binaryLinear b * binaryLinear c =
        binaryLinear e * binaryLinear d * binaryLinear f := by
      calc
        _ = binaryLinear d * binaryLinear e * binaryLinear f := h
        _ = _ := by ring
    have hh := binaryLinear_cancel_first a b c e d f ha r her h'
    obtain ⟨s, t, hs, ht, hst, hcase⟩ := binaryLinear_finish_two b c d f hb hd hf r hr hh
    rcases hcase with ⟨hds, hft⟩ | ⟨hfs, hdt⟩
    · refine ⟨Equiv.swap 0 1, ![s, r, t], ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp [hr, hs, ht]
      · simpa [mul_assoc, mul_comm, mul_left_comm] using hst
      · intro i; fin_cases i <;> simp [Equiv.swap_apply_def, hds, her, hft]
    · refine ⟨(Equiv.swap 0 1).trans (Equiv.swap 1 2), ![t, r, s], ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp [hr, hs, ht]
      · simpa [mul_assoc, mul_comm, mul_left_comm] using hst
      · intro i; fin_cases i <;> simp [Equiv.swap_apply_def, hdt, her, hfs]
  · have h' : binaryLinear a * binaryLinear b * binaryLinear c =
        binaryLinear f * binaryLinear d * binaryLinear e := by
      calc
        _ = binaryLinear d * binaryLinear e * binaryLinear f := h
        _ = _ := by ring
    have hh := binaryLinear_cancel_first a b c f d e ha r hfr h'
    obtain ⟨s, t, hs, ht, hst, hcase⟩ := binaryLinear_finish_two b c d e hb hd he r hr hh
    rcases hcase with ⟨hds, het⟩ | ⟨hes, hdt⟩
    · refine ⟨(Equiv.swap 1 2).trans (Equiv.swap 0 1), ![s, t, r], ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp [hr, hs, ht]
      · simpa [mul_assoc, mul_comm, mul_left_comm] using hst
      · intro i; fin_cases i <;> simp [Equiv.swap_apply_def, hds, het, hfr]
    · refine ⟨Equiv.swap 0 2, ![t, s, r], ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp [hr, hs, ht]
      · simpa [mul_assoc, mul_comm, mul_left_comm] using hst
      · intro i; fin_cases i <;> simp [Equiv.swap_apply_def, hdt, hes, hfr]

end FactorMatchingIntegration

namespace C4Coordinates

lemma sum_perm_succ {n : ℕ} {R : Type*} [CommRing R] (f : Equiv.Perm (Fin (n + 1)) → R) :
    ∑ σ, f σ = ∑ p : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n), f (Equiv.Perm.decomposeFin.symm (p, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma perm4 {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) : Matrix.permanent M =
    M 0 0 * M 1 1 * M 2 2 * M 3 3 + M 0 0 * M 1 1 * M 3 2 * M 2 3 + M 0 0 * M 2 1 * M 1 2 * M 3 3
  + M 0 0 * M 2 1 * M 3 2 * M 1 3 + M 0 0 * M 3 1 * M 1 2 * M 2 3 + M 0 0 * M 3 1 * M 2 2 * M 1 3
  + M 1 0 * M 0 1 * M 2 2 * M 3 3 + M 1 0 * M 0 1 * M 3 2 * M 2 3 + M 1 0 * M 2 1 * M 0 2 * M 3 3
  + M 1 0 * M 2 1 * M 3 2 * M 0 3 + M 1 0 * M 3 1 * M 0 2 * M 2 3 + M 1 0 * M 3 1 * M 2 2 * M 0 3
  + M 2 0 * M 0 1 * M 1 2 * M 3 3 + M 2 0 * M 0 1 * M 3 2 * M 1 3 + M 2 0 * M 1 1 * M 0 2 * M 3 3
  + M 2 0 * M 1 1 * M 3 2 * M 0 3 + M 2 0 * M 3 1 * M 0 2 * M 1 3 + M 2 0 * M 3 1 * M 1 2 * M 0 3
  + M 3 0 * M 0 1 * M 1 2 * M 2 3 + M 3 0 * M 0 1 * M 2 2 * M 1 3 + M 3 0 * M 1 1 * M 0 2 * M 2 3
  + M 3 0 * M 1 1 * M 2 2 * M 0 3 + M 3 0 * M 2 1 * M 0 2 * M 1 3 + M 3 0 * M 2 1 * M 1 2 * M 0 3 := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring

def scaledMatrix {R : Type*} [CommRing R] (e f a b H X Y : R) :
    Matrix (Fin 4) (Fin 4) R :=
  !![2*H+2*b-4*e, 2*e+2*f+2*X-a-b, 0, 2*e-2*f-2*Y-b+a;
     2*e+2*f+2*X-a-b, -2*H+2*a-4*e, 2*e-2*f+2*Y+b-a, 0;
     0, 2*e-2*f+2*Y+b-a, 2*H-2*b-4*e, 2*e+2*f-2*X+a+b;
     2*e-2*f-2*Y-b+a, 0, 2*e+2*f-2*X+a+b, -2*H-2*a-4*e]

def quadratic {R : Type*} [CommRing R] (e f a b H X Y : R) : R :=
  6*e^2+2*f^2+a^2+b^2-H^2-X^2-Y^2-X*(a+b)+Y*(b-a)

def cubic {R : Type*} [CommRing R] (e f a b H X Y : R) : R :=
  2*f*a*b-2*H*X*Y +
    e*(-4*X^2-4*Y^2+4*X*(a+b)+4*Y*(a-b)-a^2-b^2+4*f^2)-4*e^3

lemma scaledMatrix_symmetric {R : Type*} [CommRing R] (e f a b H X Y : R) :
    ∀ i j, scaledMatrix e f a b H X Y i j = scaledMatrix e f a b H X Y j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

lemma scaledMatrix_tangent {R : Type*} [CommRing R] (e f a b H X Y : R) :
    (∑ i : Fin 4, ∑ j : Fin 4, scaledMatrix e f a b H X Y i j) = 0 := by
  simp [scaledMatrix, Fin.sum_univ_succ]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
lemma scaled_permanent_expansion {R : Type*} [CommRing R]
    (e f a b H X Y z : R) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1 + z * scaledMatrix e f a b H X Y i j) =
      24 + (16 * quadratic e f a b H X Y) * z^2 +
        (32 * cubic e f a b H X Y) * z^3 +
        Matrix.permanent (scaledMatrix e f a b H X Y) * z^4 := by
  rw [perm4 (Matrix.of fun (i j : Fin 4) => 1 + z * scaledMatrix e f a b H X Y i j),
    perm4 (scaledMatrix e f a b H X Y)]
  simp +decide [scaledMatrix, Matrix.of_apply, quadratic, cubic]
  ring



open Polynomial

lemma quartic_expansion_coeff_two_three
    (p : ℂ[X]) (q c r : ℂ)
    (h : p = C 24 + C q * X ^ 2 + C c * X ^ 3 + C r * X ^ 4) :
    p.coeff 2 = q ∧ p.coeff 3 = c := by
  rw [h]
  constructor <;> simp

lemma quartic_coeffs_zero_of_eval_constant
    (p : ℂ[X]) (q c r : ℂ)
    (h : p = C 24 + C q * X ^ 2 + C c * X ^ 3 + C r * X ^ 4)
    (heval : ∀ z : ℂ, p.eval z = 24) :
    q = 0 ∧ c = 0 := by
  have hp : p = C 24 := by
    apply Polynomial.funext
    intro z
    simpa only [eval_C] using heval z
  obtain ⟨h2, h3⟩ := quartic_expansion_coeff_two_three p q c r h
  constructor
  · rw [← h2, hp]
    simp
  · rw [← h3, hp]
    simp

lemma quartic_coeffs_zero_of_pointwise
    (q c r : ℂ)
    (h : ∀ z : ℂ, 24 + q * z ^ 2 + c * z ^ 3 + r * z ^ 4 = 24) :
    q = 0 ∧ c = 0 := by
  apply quartic_coeffs_zero_of_eval_constant
    (C 24 + C q * X ^ 2 + C c * X ^ 3 + C r * X ^ 4) q c r rfl
  intro z
  simpa only [eval_add, eval_C, eval_mul, eval_pow, eval_X] using h z

noncomputable def matrix (e f a b H X Y : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((1 : ℂ) / 8) • scaledMatrix e f a b H X Y

lemma matrix_symmetric (e f a b H X Y : ℂ) :
    ∀ i j, matrix e f a b H X Y i j = matrix e f a b H X Y j i := by
  intro i j
  change (1 / 8 : ℂ) * scaledMatrix e f a b H X Y i j =
    (1 / 8 : ℂ) * scaledMatrix e f a b H X Y j i
  rw [scaledMatrix_symmetric e f a b H X Y i j]

lemma matrix_tangent (e f a b H X Y : ℂ) :
    (∑ i : Fin 4, ∑ j : Fin 4, matrix e f a b H X Y i j) = 0 := by
  simp only [matrix, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rw [scaledMatrix_tangent, mul_zero]

lemma permanent_expansion (e f a b H X Y z : ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1 + z * matrix e f a b H X Y i j) =
      24 + (quadratic e f a b H X Y / 4) * z^2 +
        (cubic e f a b H X Y / 16) * z^3 +
        Matrix.permanent (matrix e f a b H X Y) * z^4 := by
  have hm : (Matrix.of fun (i j : Fin 4) => 1 + z * matrix e f a b H X Y i j) =
      (Matrix.of fun (i j : Fin 4) => 1 + (z / 8) * scaledMatrix e f a b H X Y i j) := by
    ext i j
    simp only [matrix, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hm, scaled_permanent_expansion, matrix, Matrix.permanent_smul]
  simp only [Fintype.card_fin]
  ring

noncomputable def linePolynomial (M : Matrix (Fin 4) (Fin 4) ℂ) : ℂ[X] :=
  Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1 + Polynomial.X * C (M i j))

lemma linePolynomial_eval (M : Matrix (Fin 4) (Fin 4) ℂ) (z : ℂ) :
    (linePolynomial M).eval z =
      Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1 + z * M i j) := by
  simp only [linePolynomial, Matrix.permanent, Matrix.of_apply, eval_finsetSum,
    eval_prod, eval_add, eval_one, eval_mul, eval_X, eval_C]

lemma linePolynomial_expansion (e f a b H X Y : ℂ) :
    linePolynomial (matrix e f a b H X Y) =
      C 24 + C (quadratic e f a b H X Y / 4) * Polynomial.X^2 +
        C (cubic e f a b H X Y / 16) * Polynomial.X^3 +
        C (Matrix.permanent (matrix e f a b H X Y)) * Polynomial.X^4 := by
  apply Polynomial.funext
  intro z
  rw [linePolynomial_eval]
  simpa only [eval_add, eval_C, eval_mul, eval_pow, eval_X] using
    permanent_expansion e f a b H X Y z

theorem coefficient_formulas (e f a b H X Y : ℂ) :
    (linePolynomial (matrix e f a b H X Y)).coeff 2 = quadratic e f a b H X Y / 4 ∧
    (linePolynomial (matrix e f a b H X Y)).coeff 3 = cubic e f a b H X Y / 16 := by
  exact quartic_expansion_coeff_two_three _ _ _ _ (linePolynomial_expansion e f a b H X Y)

theorem quadratic_cubic_zero_of_constant_line (e f a b H X Y : ℂ)
    (h : ∀ z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + z * matrix e f a b H X Y i j) = 24) :
    quadratic e f a b H X Y = 0 ∧ cubic e f a b H X Y = 0 := by
  have hzero := quartic_coeffs_zero_of_pointwise
    (quadratic e f a b H X Y / 4) (cubic e f a b H X Y / 16)
    (Matrix.permanent (matrix e f a b H X Y))
    (fun z => (permanent_expansion e f a b H X Y z).symm.trans (h z))
  constructor
  · linear_combination (4 : ℂ) * hzero.1
  · linear_combination (16 : ℂ) * hzero.2

lemma cubic_at_e_zero (f a b H X Y : ℂ) :
    cubic 0 f a b H X Y = 2 * (f*a*b-H*X*Y) := by
  unfold cubic
  ring

theorem product_identity_of_constant_line (f a b H X Y : ℂ)
    (h : ∀ z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + z * matrix 0 f a b H X Y i j) = 24) :
    f*a*b = H*X*Y := by
  have hc := (quadratic_cubic_zero_of_constant_line 0 f a b H X Y h).2
  rw [cubic_at_e_zero] at hc
  linear_combination (1 / 2 : ℂ) * hc


-- Append inside namespace PEqualNP.Outside.L_gct_231_aux.C4Coordinates.
-- Requires the existing scaledMatrix and the Matrix.IsSymm API.

lemma scaledMatrix_reconstruct_entries
    (d0 d1 d2 d3 p s q r : ℂ)
    (ht : d0 + d1 + d2 + d3 + 2 * (p + r + q + s) = 0) :
    ((1 : ℂ) / 8) • scaledMatrix
      (p + r + q + s) (p + r - q - s)
      (2 * (d1 - d3)) (2 * (d0 - d2))
      (2 * (d0 + d2 + (p + r + q + s)))
      (2 * (p - r) + (2 * (d1 - d3) + 2 * (d0 - d2)) / 2)
      (2 * (q - s) - (2 * (d0 - d2) - 2 * (d1 - d3)) / 2) =
      !![d0, p, 0, s; p, d1, q, 0; 0, q, d2, r; s, 0, r, d3] := by
  have hd3 : d3 = -d0 - d1 - d2 - 2 * (p + r + q + s) := by
    linear_combination ht
  rw [hd3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scaledMatrix, Matrix.smul_apply, smul_eq_mul] <;> ring

lemma scaledMatrix_reconstruct_supported
    (M : Matrix (Fin 4) (Fin 4) ℂ) (hsym : M.IsSymm)
    (h02 : M 0 2 = 0) (h13 : M 1 3 = 0)
    (htangent : (∑ i : Fin 4, ∑ j : Fin 4, M i j) = 0) :
    let e := M 0 1 + M 2 3 + M 1 2 + M 0 3
    let f := M 0 1 + M 2 3 - M 1 2 - M 0 3
    let a := 2 * (M 1 1 - M 3 3)
    let b := 2 * (M 0 0 - M 2 2)
    let H := 2 * (M 0 0 + M 2 2 + e)
    let X := 2 * (M 0 1 - M 2 3) + (a + b) / 2
    let Y := 2 * (M 1 2 - M 0 3) - (b - a) / 2
    ((1 : ℂ) / 8) • scaledMatrix e f a b H X Y = M := by
  have h10 : M 1 0 = M 0 1 := hsym.apply 0 1
  have h20 : M 2 0 = 0 := (hsym.apply 0 2).trans h02
  have h30 : M 3 0 = M 0 3 := hsym.apply 0 3
  have h21 : M 2 1 = M 1 2 := hsym.apply 1 2
  have h31 : M 3 1 = 0 := (hsym.apply 1 3).trans h13
  have h32 : M 3 2 = M 2 3 := hsym.apply 2 3
  have ht : M 0 0 + M 1 1 + M 2 2 + M 3 3 +
      2 * (M 0 1 + M 2 3 + M 1 2 + M 0 3) = 0 := by
    have h := htangent
    simp [Fin.sum_univ_succ, h10, h20, h30, h21, h31, h32, h02, h13] at h
    linear_combination h
  dsimp only
  rw [scaledMatrix_reconstruct_entries
    (M 0 0) (M 1 1) (M 2 2) (M 3 3) (M 0 1) (M 0 3) (M 1 2) (M 2 3) ht]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h10, h20, h30, h21, h31, h32, h02, h13]

end C4Coordinates

section PolynomialNonsquareIntegration

open Polynomial

theorem polynomial_not_square_of_coefficients {R : Type*} [CommRing R] [NoZeroDivisors R]
    (q : R[X]) (h0 : q.coeff 0 = 0) (h2 : q.coeff 2 = 0) (h3 : q.coeff 3 ≠ 0) :
    ¬ ∃ p : R[X], q = p ^ 2 := by
  rintro ⟨p, hp⟩
  have hp0 : p.coeff 0 = 0 := by
    have hz : p.coeff 0 * p.coeff 0 = 0 := by simpa [hp, pow_two] using h0
    exact (mul_eq_zero.mp hz).elim id id
  have hp1 : p.coeff 1 = 0 := by
    have hz : p.coeff 1 * p.coeff 1 = 0 := by
      simpa [hp, pow_two, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, hp0] using h2
    exact (mul_eq_zero.mp hz).elim id id
  apply h3
  simp [hp, pow_two, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, hp0, hp1]

end PolynomialNonsquareIntegration

namespace IsolatedVertex

lemma sum_perm_succ {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, f σ = ∑ p : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n), f (Equiv.Perm.decomposeFin.symm (p, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma perm4 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix.permanent M =
    M 0 0 * M 1 1 * M 2 2 * M 3 3 + M 0 0 * M 1 1 * M 3 2 * M 2 3 + M 0 0 * M 2 1 * M 1 2 * M 3 3
  + M 0 0 * M 2 1 * M 3 2 * M 1 3 + M 0 0 * M 3 1 * M 1 2 * M 2 3 + M 0 0 * M 3 1 * M 2 2 * M 1 3
  + M 1 0 * M 0 1 * M 2 2 * M 3 3 + M 1 0 * M 0 1 * M 3 2 * M 2 3 + M 1 0 * M 2 1 * M 0 2 * M 3 3
  + M 1 0 * M 2 1 * M 3 2 * M 0 3 + M 1 0 * M 3 1 * M 0 2 * M 2 3 + M 1 0 * M 3 1 * M 2 2 * M 0 3
  + M 2 0 * M 0 1 * M 1 2 * M 3 3 + M 2 0 * M 0 1 * M 3 2 * M 1 3 + M 2 0 * M 1 1 * M 0 2 * M 3 3
  + M 2 0 * M 1 1 * M 3 2 * M 0 3 + M 2 0 * M 3 1 * M 0 2 * M 1 3 + M 2 0 * M 3 1 * M 1 2 * M 0 3
  + M 3 0 * M 0 1 * M 1 2 * M 2 3 + M 3 0 * M 0 1 * M 2 2 * M 1 3 + M 3 0 * M 1 1 * M 0 2 * M 2 3
  + M 3 0 * M 1 1 * M 2 2 * M 0 3 + M 3 0 * M 2 1 * M 0 2 * M 1 3 + M 3 0 * M 2 1 * M 1 2 * M 0 3 := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring


lemma four_coefficients_zero (L Q C F : ℂ)
    (h : ∀ z : ℂ, 24 + L*z + Q*z^2 + C*z^3 + F*z^4 = 24) :
    L = 0 ∧ Q = 0 ∧ C = 0 ∧ F = 0 := by
  have h1 := h 1
  have hn1 := h (-1)
  have h2 := h 2
  have hn2 := h (-2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (2/3 : ℂ) * h1 - (2/3 : ℂ) * hn1 -
      (1/12 : ℂ) * h2 + (1/12 : ℂ) * hn2
  · linear_combination (2/3 : ℂ) * h1 + (2/3 : ℂ) * hn1 -
      (1/24 : ℂ) * h2 - (1/24 : ℂ) * hn2
  · linear_combination -(1/6 : ℂ) * h1 + (1/6 : ℂ) * hn1 +
      (1/12 : ℂ) * h2 - (1/12 : ℂ) * hn2
  · linear_combination -(1/6 : ℂ) * h1 - (1/6 : ℂ) * hn1 +
      (1/24 : ℂ) * h2 + (1/24 : ℂ) * hn2

def blockSum (a b c e f g : ℂ) : ℂ := a + e + g + 2*b + 2*c + 2*f

def blockRookTwo (a b c e f g : ℂ) : ℂ :=
  a*e + a*g + e*g + b^2 + c^2 + f^2 + 2*(a*f + b*c + b*f + c*e + b*g + c*f)

def blockPermanent (a b c e f g : ℂ) : ℂ :=
  a*e*g + 2*b*c*f + a*f^2 + e*c^2 + g*b^2

def isolatedMatrix (d a b c e f g : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![d,0,0,0; 0,a,b,c; 0,b,e,f; 0,c,f,g]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
lemma isolated_permanent_expansion (d a b c e f g z : ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1 + z * isolatedMatrix d a b c e f g i j) =
    24 + (6*(blockSum a b c e f g+d))*z +
      (2*(blockRookTwo a b c e f g + blockSum a b c e f g*d))*z^2 +
      (blockPermanent a b c e f g + d*blockRookTwo a b c e f g)*z^3 +
      (d*blockPermanent a b c e f g)*z^4 := by
  rw [perm4]
  simp +decide [isolatedMatrix, Matrix.of_apply, blockSum, blockRookTwo, blockPermanent]
  ring

theorem isolated_matrix_diagonal_zero (d a b c e f g : ℂ)
    (h : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1 + z * isolatedMatrix d a b c e f g i j) = 24) : d = 0 := by
  obtain ⟨hL,hQ,hC,hF⟩ := four_coefficients_zero
    (6*(blockSum a b c e f g+d))
    (2*(blockRookTwo a b c e f g + blockSum a b c e f g*d))
    (blockPermanent a b c e f g + d*blockRookTwo a b c e f g)
    (d*blockPermanent a b c e f g)
    (fun z => (isolated_permanent_expansion d a b c e f g z).symm.trans (h z))
  have hd4 : d^4 = 0 := by
    linear_combination (d^3/6)*hL - (d^2/2)*hQ + d*hC - hF
  exact eq_zero_of_pow_eq_zero hd4

theorem isolated_vertex_zero_diagonal
    (M : Matrix (Fin 4) (Fin 4) ℂ) (hsym : M.IsSymm)
    (h01 : M 0 1 = 0) (h02 : M 0 2 = 0) (h03 : M 0 3 = 0)
    (h : ∀ z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + z * M i j) = 24) : M 0 0 = 0 := by
  have h10 : M 1 0 = 0 := (hsym.apply 0 1).trans h01
  have h20 : M 2 0 = 0 := (hsym.apply 0 2).trans h02
  have h30 : M 3 0 = 0 := (hsym.apply 0 3).trans h03
  have h21 : M 2 1 = M 1 2 := hsym.apply 1 2
  have h31 : M 3 1 = M 1 3 := hsym.apply 1 3
  have h32 : M 3 2 = M 2 3 := hsym.apply 2 3
  have hm : M = isolatedMatrix (M 0 0) (M 1 1) (M 1 2) (M 1 3) (M 2 2) (M 2 3) (M 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [isolatedMatrix, h01, h02, h03, h10, h20, h30, h21, h31, h32]
  apply isolated_matrix_diagonal_zero (M 0 0) (M 1 1) (M 1 2) (M 1 3) (M 2 2) (M 2 3) (M 3 3)
  intro z
  simpa only [← hm] using h z

theorem isolated_vertex_diagonal_zero
    (M : Matrix (Fin 4) (Fin 4) ℂ) (hsym : M.IsSymm) (v : Fin 4)
    (hoff : ∀ j : Fin 4, j ≠ v → M v j = 0)
    (h : ∀ z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + z * M i j) = 24) : M v v = 0 := by
  let p : Equiv.Perm (Fin 4) := Equiv.swap 0 v
  let N : Matrix (Fin 4) (Fin 4) ℂ := fun i j => M (p i) (p j)
  have hp0 : p 0 = v := by simp [p]
  have hsymN : N.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact hsym.apply (p i) (p j)
  have hoffN : ∀ j : Fin 4, j ≠ 0 → N 0 j = 0 := by
    intro j hj
    have hpj : p j ≠ v := by
      intro heq
      exact hj (p.injective (heq.trans hp0.symm))
    change M (p 0) (p j) = 0
    rw [hp0]
    exact hoff (p j) hpj
  have hN : ∀ z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + z * N i j) = 24 := by
    intro z
    change Matrix.permanent (((Matrix.of fun (i j : Fin 4) => 1 + z * M i j).submatrix p id).submatrix id p) = 24
    rw [Matrix.permanent_permute_rows, Matrix.permanent_permute_cols]
    exact h z
  have hz := isolated_vertex_zero_diagonal N hsymN
    (hoffN 1 (by decide)) (hoffN 2 (by decide)) (hoffN 3 (by decide)) hN
  simpa only [N, hp0] using hz

end IsolatedVertex

namespace C4OpenCertificates

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
theorem c4_open_0_v_zero (x0 x1 : ℂ)
    (h0 : (((((4) + (4 * x1)) + ((-5 * x1 ^ 2) + (-4 * x0))) + (((-6 * x0 * x1) + (4 * x0 * x1 ^ 2)) + ((-5 * x0 ^ 2) + ((-4 * x0 ^ 2 * x1) + (4 * x0 ^ 2 * x1 ^ 2))))) : ℂ) = 0)
    (h1 : ((((((((32) + (64 * x1)) + ((984 * x1 ^ 2) + (1600 * x1 ^ 3))) + (((722 * x1 ^ 4) + (-128 * x0)) + ((-432 * x0 * x1) + (-5712 * x0 * x1 ^ 2)))) + ((((-8512 * x0 * x1 ^ 3) + (-3684 * x0 * x1 ^ 4)) + ((24 * x0 ^ 2) + (-224 * x0 ^ 2 * x1))) + (((6524 * x0 ^ 2 * x1 ^ 2) + (9040 * x0 ^ 2 * x1 ^ 3)) + ((2030 * x0 ^ 2 * x1 ^ 4) + ((-3020 * x0 ^ 2 * x1 ^ 5) + (-1369 * x0 ^ 2 * x1 ^ 6)))))) + (((((304 * x0 ^ 3) + (3424 * x0 ^ 3 * x1)) + ((12568 * x0 ^ 3 * x1 ^ 2) + (17544 * x0 ^ 3 * x1 ^ 3))) + (((16852 * x0 ^ 3 * x1 ^ 4) + (16790 * x0 ^ 3 * x1 ^ 5)) + ((7548 * x0 ^ 3 * x1 ^ 6) + (226 * x0 ^ 4)))) + ((((-496 * x0 ^ 4 * x1) + (-17436 * x0 ^ 4 * x1 ^ 2)) + ((-21856 * x0 ^ 4 * x1 ^ 3) + (-18980 * x0 ^ 4 * x1 ^ 4))) + (((-20292 * x0 ^ 4 * x1 ^ 5) + (-8752 * x0 ^ 4 * x1 ^ 6)) + ((-724 * x0 ^ 5) + ((-7992 * x0 ^ 5 * x1) + (-16736 * x0 ^ 5 * x1 ^ 2))))))) + ((((((-27664 * x0 ^ 5 * x1 ^ 3) + (-32056 * x0 ^ 5 * x1 ^ 4)) + ((-28608 * x0 ^ 5 * x1 ^ 5) + (-12752 * x0 ^ 5 * x1 ^ 6))) + (((-706 * x0 ^ 6) + (588 * x0 ^ 6 * x1)) + ((11491 * x0 ^ 6 * x1 ^ 2) + (14296 * x0 ^ 6 * x1 ^ 3)))) + ((((34248 * x0 ^ 6 * x1 ^ 4) + (46768 * x0 ^ 6 * x1 ^ 5)) + ((18034 * x0 ^ 6 * x1 ^ 6) + (684 * x0 ^ 7))) + (((6242 * x0 ^ 7 * x1) + (14012 * x0 ^ 7 * x1 ^ 2)) + ((32784 * x0 ^ 7 * x1 ^ 3) + ((36176 * x0 ^ 7 * x1 ^ 4) + (31336 * x0 ^ 7 * x1 ^ 5)))))) + (((((16160 * x0 ^ 7 * x1 ^ 6) + (722 * x0 ^ 8)) + ((1580 * x0 ^ 8 * x1) + (3512 * x0 ^ 8 * x1 ^ 2))) + (((2768 * x0 ^ 8 * x1 ^ 3) + (-15940 * x0 ^ 8 * x1 ^ 4)) + ((-27904 * x0 ^ 8 * x1 ^ 5) + ((-9744 * x0 ^ 8 * x1 ^ 6) + (-1728 * x0 ^ 9 * x1 ^ 2))))) + ((((-12952 * x0 ^ 9 * x1 ^ 3) + (-21216 * x0 ^ 9 * x1 ^ 4)) + ((-24096 * x0 ^ 9 * x1 ^ 5) + (-12160 * x0 ^ 9 * x1 ^ 6))) + (((-1294 * x0 ^ 10 * x1 ^ 2) + (-3520 * x0 ^ 10 * x1 ^ 3)) + ((-5712 * x0 ^ 10 * x1 ^ 4) + ((-4096 * x0 ^ 10 * x1 ^ 5) + (-3040 * x0 ^ 10 * x1 ^ 6)))))))) : ℂ) = 0)
    (h2 : ((((((((96 * x1) + (468 * x1 ^ 2)) + ((720 * x1 ^ 3) + (336 * x1 ^ 4))) + (((-456 * x0 * x1) + (-2664 * x0 * x1 ^ 2)) + ((-4212 * x0 * x1 ^ 3) + (-1902 * x0 * x1 ^ 4)))) + ((((-44 * x0 ^ 2) + (2936 * x0 ^ 2 * x1 ^ 2)) + ((5384 * x0 ^ 2 * x1 ^ 3) + (2271 * x0 ^ 2 * x1 ^ 4))) + (((10 * x0 ^ 2 * x1 ^ 5) + (120 * x0 ^ 3)) + ((2220 * x0 ^ 3 * x1) + (5860 * x0 ^ 3 * x1 ^ 2))))) + (((((7068 * x0 ^ 3 * x1 ^ 3) + (3258 * x0 ^ 3 * x1 ^ 4)) + ((17 * x0 ^ 3 * x1 ^ 5) + (144 * x0 ^ 4))) + (((-696 * x0 ^ 4 * x1) + (-7914 * x0 ^ 4 * x1 ^ 2)) + ((-12440 * x0 ^ 4 * x1 ^ 3) + (-4923 * x0 ^ 4 * x1 ^ 4)))) + ((((-90 * x0 ^ 4 * x1 ^ 5) + (-4 * x0 ^ 4 * x1 ^ 6)) + ((-358 * x0 ^ 5) + (-4380 * x0 ^ 5 * x1))) + (((-7280 * x0 ^ 5 * x1 ^ 2) + (-7574 * x0 ^ 5 * x1 ^ 3)) + ((-4080 * x0 ^ 5 * x1 ^ 4) + (-96 * x0 ^ 5 * x1 ^ 5)))))) + ((((((-4 * x0 ^ 5 * x1 ^ 6) + (-357 * x0 ^ 6)) + ((558 * x0 ^ 6 * x1) + (4690 * x0 ^ 6 * x1 ^ 2))) + (((7724 * x0 ^ 6 * x1 ^ 3) + (3072 * x0 ^ 6 * x1 ^ 4)) + ((256 * x0 ^ 6 * x1 ^ 5) + (31 * x0 ^ 6 * x1 ^ 6)))) + ((((342 * x0 ^ 7) + (3189 * x0 ^ 7 * x1)) + ((5360 * x0 ^ 7 * x1 ^ 2) + (5904 * x0 ^ 7 * x1 ^ 3))) + (((3144 * x0 ^ 7 * x1 ^ 4) + (172 * x0 ^ 7 * x1 ^ 5)) + ((32 * x0 ^ 7 * x1 ^ 6) + (361 * x0 ^ 8))))) + (((((750 * x0 ^ 8 * x1) + (1604 * x0 ^ 8 * x1 ^ 2)) + ((704 * x0 ^ 8 * x1 ^ 3) + (354 * x0 ^ 8 * x1 ^ 4))) + (((-208 * x0 ^ 8 * x1 ^ 5) + (-56 * x0 ^ 8 * x1 ^ 6)) + ((60 * x0 ^ 9 * x1 ^ 2) + (44 * x0 ^ 9 * x1 ^ 3)))) + ((((-192 * x0 ^ 9 * x1 ^ 4) + (-240 * x0 ^ 9 * x1 ^ 5)) + ((-64 * x0 ^ 9 * x1 ^ 6) + (-25 * x0 ^ 10 * x1 ^ 2))) + (((80 * x0 ^ 10 * x1 ^ 3) + (-24 * x0 ^ 10 * x1 ^ 4)) + ((-64 * x0 ^ 10 * x1 ^ 5) + (-16 * x0 ^ 10 * x1 ^ 6))))))) : ℂ) = 0)
    (h3 : (((4) + ((-4 * x0 ^ 2 * x1 ^ 2) + (x0 ^ 4 * x1 ^ 4))) : ℂ) = 0)
    : False := by
  have h4 : ((((((((-32) + (-64 * x1)) + ((-984 * x1 ^ 2) + (-1600 * x1 ^ 3))) + (((-722 * x1 ^ 4) + (128 * x0)) + ((432 * x0 * x1) + (5712 * x0 * x1 ^ 2)))) + ((((8512 * x0 * x1 ^ 3) + (3684 * x0 * x1 ^ 4)) + ((-24 * x0 ^ 2) + (224 * x0 ^ 2 * x1))) + (((-6524 * x0 ^ 2 * x1 ^ 2) + (-9040 * x0 ^ 2 * x1 ^ 3)) + ((-2030 * x0 ^ 2 * x1 ^ 4) + ((3020 * x0 ^ 2 * x1 ^ 5) + (1369 * x0 ^ 2 * x1 ^ 6)))))) + (((((-304 * x0 ^ 3) + (-3424 * x0 ^ 3 * x1)) + ((-12568 * x0 ^ 3 * x1 ^ 2) + (-17544 * x0 ^ 3 * x1 ^ 3))) + (((-16852 * x0 ^ 3 * x1 ^ 4) + (-16790 * x0 ^ 3 * x1 ^ 5)) + ((-7548 * x0 ^ 3 * x1 ^ 6) + (-226 * x0 ^ 4)))) + ((((496 * x0 ^ 4 * x1) + (17436 * x0 ^ 4 * x1 ^ 2)) + ((21856 * x0 ^ 4 * x1 ^ 3) + (18980 * x0 ^ 4 * x1 ^ 4))) + (((20292 * x0 ^ 4 * x1 ^ 5) + (8752 * x0 ^ 4 * x1 ^ 6)) + ((724 * x0 ^ 5) + ((7992 * x0 ^ 5 * x1) + (16736 * x0 ^ 5 * x1 ^ 2))))))) + ((((((27664 * x0 ^ 5 * x1 ^ 3) + (32056 * x0 ^ 5 * x1 ^ 4)) + ((28608 * x0 ^ 5 * x1 ^ 5) + (12752 * x0 ^ 5 * x1 ^ 6))) + (((706 * x0 ^ 6) + (-588 * x0 ^ 6 * x1)) + ((-11491 * x0 ^ 6 * x1 ^ 2) + (-14296 * x0 ^ 6 * x1 ^ 3)))) + ((((-34248 * x0 ^ 6 * x1 ^ 4) + (-46768 * x0 ^ 6 * x1 ^ 5)) + ((-18034 * x0 ^ 6 * x1 ^ 6) + (-684 * x0 ^ 7))) + (((-6242 * x0 ^ 7 * x1) + (-14012 * x0 ^ 7 * x1 ^ 2)) + ((-32784 * x0 ^ 7 * x1 ^ 3) + ((-36176 * x0 ^ 7 * x1 ^ 4) + (-31336 * x0 ^ 7 * x1 ^ 5)))))) + (((((-16160 * x0 ^ 7 * x1 ^ 6) + (-722 * x0 ^ 8)) + ((-1580 * x0 ^ 8 * x1) + (-3512 * x0 ^ 8 * x1 ^ 2))) + (((-2768 * x0 ^ 8 * x1 ^ 3) + (15940 * x0 ^ 8 * x1 ^ 4)) + ((27904 * x0 ^ 8 * x1 ^ 5) + ((9744 * x0 ^ 8 * x1 ^ 6) + (1728 * x0 ^ 9 * x1 ^ 2))))) + ((((12952 * x0 ^ 9 * x1 ^ 3) + (21216 * x0 ^ 9 * x1 ^ 4)) + ((24096 * x0 ^ 9 * x1 ^ 5) + (12160 * x0 ^ 9 * x1 ^ 6))) + (((1294 * x0 ^ 10 * x1 ^ 2) + (3520 * x0 ^ 10 * x1 ^ 3)) + ((5712 * x0 ^ 10 * x1 ^ 4) + ((4096 * x0 ^ 10 * x1 ^ 5) + (3040 * x0 ^ 10 * x1 ^ 6)))))))) : ℂ) = 0 := by
    linear_combination ((-1)) * h1
  have h5 : ((((((((-96 * x1) + (-468 * x1 ^ 2)) + ((-720 * x1 ^ 3) + (-336 * x1 ^ 4))) + (((456 * x0 * x1) + (2664 * x0 * x1 ^ 2)) + ((4212 * x0 * x1 ^ 3) + (1902 * x0 * x1 ^ 4)))) + ((((44 * x0 ^ 2) + (-2936 * x0 ^ 2 * x1 ^ 2)) + ((-5384 * x0 ^ 2 * x1 ^ 3) + (-2271 * x0 ^ 2 * x1 ^ 4))) + (((-10 * x0 ^ 2 * x1 ^ 5) + (-120 * x0 ^ 3)) + ((-2220 * x0 ^ 3 * x1) + (-5860 * x0 ^ 3 * x1 ^ 2))))) + (((((-7068 * x0 ^ 3 * x1 ^ 3) + (-3258 * x0 ^ 3 * x1 ^ 4)) + ((-17 * x0 ^ 3 * x1 ^ 5) + (-144 * x0 ^ 4))) + (((696 * x0 ^ 4 * x1) + (7914 * x0 ^ 4 * x1 ^ 2)) + ((12440 * x0 ^ 4 * x1 ^ 3) + (4923 * x0 ^ 4 * x1 ^ 4)))) + ((((90 * x0 ^ 4 * x1 ^ 5) + (4 * x0 ^ 4 * x1 ^ 6)) + ((358 * x0 ^ 5) + (4380 * x0 ^ 5 * x1))) + (((7280 * x0 ^ 5 * x1 ^ 2) + (7574 * x0 ^ 5 * x1 ^ 3)) + ((4080 * x0 ^ 5 * x1 ^ 4) + (96 * x0 ^ 5 * x1 ^ 5)))))) + ((((((4 * x0 ^ 5 * x1 ^ 6) + (357 * x0 ^ 6)) + ((-558 * x0 ^ 6 * x1) + (-4690 * x0 ^ 6 * x1 ^ 2))) + (((-7724 * x0 ^ 6 * x1 ^ 3) + (-3072 * x0 ^ 6 * x1 ^ 4)) + ((-256 * x0 ^ 6 * x1 ^ 5) + (-31 * x0 ^ 6 * x1 ^ 6)))) + ((((-342 * x0 ^ 7) + (-3189 * x0 ^ 7 * x1)) + ((-5360 * x0 ^ 7 * x1 ^ 2) + (-5904 * x0 ^ 7 * x1 ^ 3))) + (((-3144 * x0 ^ 7 * x1 ^ 4) + (-172 * x0 ^ 7 * x1 ^ 5)) + ((-32 * x0 ^ 7 * x1 ^ 6) + (-361 * x0 ^ 8))))) + (((((-750 * x0 ^ 8 * x1) + (-1604 * x0 ^ 8 * x1 ^ 2)) + ((-704 * x0 ^ 8 * x1 ^ 3) + (-354 * x0 ^ 8 * x1 ^ 4))) + (((208 * x0 ^ 8 * x1 ^ 5) + (56 * x0 ^ 8 * x1 ^ 6)) + ((-60 * x0 ^ 9 * x1 ^ 2) + (-44 * x0 ^ 9 * x1 ^ 3)))) + ((((192 * x0 ^ 9 * x1 ^ 4) + (240 * x0 ^ 9 * x1 ^ 5)) + ((64 * x0 ^ 9 * x1 ^ 6) + (25 * x0 ^ 10 * x1 ^ 2))) + (((-80 * x0 ^ 10 * x1 ^ 3) + (24 * x0 ^ 10 * x1 ^ 4)) + ((64 * x0 ^ 10 * x1 ^ 5) + (16 * x0 ^ 10 * x1 ^ 6))))))) : ℂ) = 0 := by
    linear_combination ((-1)) * h2
  have h6 : ((((((100) + (-76 * x1)) + ((-85 * x1 ^ 2) + (-12 * x1 ^ 3))) + (((90 * x1 ^ 4) + (76 * x0)) + ((154 * x0 * x1) + (104 * x0 * x1 ^ 2)))) + ((((72 * x0 * x1 ^ 3) + (-112 * x0 * x1 ^ 4)) + ((-85 * x0 ^ 2) + (-104 * x0 ^ 2 * x1))) + (((12 * x0 ^ 3) + (72 * x0 ^ 3 * x1)) + ((90 * x0 ^ 4) + (112 * x0 ^ 4 * x1))))) : ℂ) = 0 := by
    linear_combination (((32)) * h3 + (((((-8 * x0 ^ 2 * x1 ^ 2) + (-8 * x0 ^ 2 * x1)) + ((8 * x0 * x1 ^ 2) + (-18 * x0 ^ 2))) + (((4 * x0 * x1) + (-18 * x1 ^ 2)) + ((12 * x0) + ((-12 * x1) + (-7)))))) * h0)
  have h7 : ((((((14356) + (-9020 * x1)) + ((-9649 * x1 ^ 2) + (3548 * x1 ^ 3))) + (((9762 * x1 ^ 4) + (-5040 * x1 ^ 5)) + ((1180 * x0) + (2674 * x0 * x1)))) + ((((8936 * x0 * x1 ^ 2) + (1448 * x0 * x1 ^ 3)) + ((-15344 * x0 * x1 ^ 4) + (6272 * x0 * x1 ^ 5))) + (((-5393 * x0 ^ 2) + (-368 * x0 ^ 2 * x1)) + ((-2260 * x0 ^ 3) + ((-568 * x0 ^ 3 * x1) + (1250 * x0 ^ 4)))))) : ℂ) = 0 := by
    linear_combination ((((-56 * x1) + (101))) * h6 + (((1568 * x0 ^ 2) + ((-560 * x0) + (1064)))) * h0)
  have h8 : ((((((1600884) + (-822172 * x1)) + ((-655913 * x1 ^ 2) + (526860 * x1 ^ 3))) + (((25250 * x1 ^ 4) + (-70000 * x1 ^ 5)) + ((822172 * x0) + (-363006 * x0 * x1)))) + ((((24368 * x0 * x1 ^ 2) + (-57528 * x0 * x1 ^ 3)) + ((-655913 * x0 ^ 2) + (-24368 * x0 ^ 2 * x1))) + (((-526860 * x0 ^ 3) + (-57528 * x0 ^ 3 * x1)) + ((25250 * x0 ^ 4) + (70000 * x0 ^ 5))))) : ℂ) = 0 := by
    linear_combination ((((56 * x0) + (101))) * h7 + (((((-87808 * x1 ^ 3) + (127008 * x1 ^ 2)) + ((-3024 * x1) + (30632)))) * h0 + ((284)) * h6))
  have h9 : ((((((-17127580) + (-11496076 * x1)) + ((19017723 * x1 ^ 2) + (3827732 * x1 ^ 3))) + (((-9107290 * x1 ^ 4) + (434000 * x1 ^ 5)) + ((980000 * x1 ^ 6) + (-10496692 * x0)))) + ((((-11321030 * x0 * x1) + (4438424 * x0 * x1 ^ 2)) + ((-1096712 * x0 * x1 ^ 3) + (2849392 * x0 * x1 ^ 4))) + (((7647707 * x0 ^ 2) + (10702520 * x0 ^ 2 * x1)) + ((6160540 * x0 ^ 3) + ((7740872 * x0 ^ 3 * x1) + (-401250 * x0 ^ 4)))))) : ℂ) = 0 := by
    linear_combination ((((-14 * x1) + ((-45 / 4 : ℂ)))) * h8 + ((((8750 * x0) + ((-9875 / 4 : ℂ)))) * h6 + ((((245000 * x1 ^ 2) + (-201348 * x0)) + ((87500 * x1) + (282310)))) * h0))
  have h10 : (((((-2477198848740) + ((3476072519612 * x1) + (2465416314069 * x1 ^ 2))) + (((-2352530308704 * x1 ^ 3) + (-108196471570 * x1 ^ 4)) + ((1967547310564 * x0) + (-5928646300922 * x0 * x1)))) + ((((-3959198531852 * x0 * x1 ^ 2) + (3270116195288 * x0 * x1 ^ 3)) + ((102134118176 * x0 * x1 ^ 4) + (844384734261 * x0 ^ 2))) + (((-567962131276 * x0 ^ 2 * x1) + (383843359160 * x0 ^ 3)) + ((1827871871640 * x0 ^ 3 * x1) + (-48585519650 * x0 ^ 4))))) : ℂ) = 0 := by
    linear_combination (((((-1503296875 / 81 : ℂ))) * h4 + (((((((((1184776000000 / 81 : ℂ) * x0 ^ 8 * x1 ^ 4) + ((2893233500000 / 81 : ℂ) * x0 ^ 8 * x1 ^ 3)) + (((1184776000000 / 27 : ℂ) * x0 ^ 7 * x1 ^ 4) + (((6584317000000 / 81 : ℂ) * x0 ^ 8 * x1 ^ 2) + ((12128174500000 / 81 : ℂ) * x0 ^ 7 * x1 ^ 3)))) + ((((1736619500000 / 81 : ℂ) * x0 ^ 6 * x1 ^ 4) + (((1256934250000 / 9 : ℂ) * x0 ^ 8 * x1) + ((23992124875000 / 81 : ℂ) * x0 ^ 7 * x1 ^ 2))) + (((8408216750000 / 81 : ℂ) * x0 ^ 6 * x1 ^ 3) + (((-3451569625000 / 81 : ℂ) * x0 ^ 5 * x1 ^ 4) + (248088500000 * x0 ^ 8))))) + (((((5040119500000 / 9 : ℂ) * x0 ^ 7 * x1) + ((17541248750000 / 81 : ℂ) * x0 ^ 6 * x1 ^ 2)) + (((-9880201250000 / 81 : ℂ) * x0 ^ 5 * x1 ^ 3) + (((-1237168812500 / 81 : ℂ) * x0 ^ 4 * x1 ^ 4) + ((2937033437500 / 3 : ℂ) * x0 ^ 7)))) + ((((32569587875000 / 81 : ℂ) * x0 ^ 6 * x1) + (((9254419375000 / 81 : ℂ) * x0 ^ 5 * x1 ^ 2) + ((-6013543625000 / 81 : ℂ) * x0 ^ 4 * x1 ^ 3))) + (((1725784812500 / 81 : ℂ) * x0 ^ 3 * x1 ^ 4) + (((68894719750000 / 81 : ℂ) * x0 ^ 6) + ((-212042077906250 / 567 : ℂ) * x0 ^ 5 * x1)))))) + ((((((1171033269265625 / 1134 : ℂ) * x0 ^ 4 * x1 ^ 2) + ((78375389046875 / 1134 : ℂ) * x0 ^ 3 * x1 ^ 3)) + (((27535328125 / 81 : ℂ) * x0 ^ 2 * x1 ^ 4) + (((-298676070031250 / 567 : ℂ) * x0 ^ 5) + ((230669319599375 / 15876 : ℂ) * x0 ^ 4 * x1)))) + ((((5767908816100625 / 63504 : ℂ) * x0 ^ 3 * x1 ^ 2) + (((-7758822216546875 / 63504 : ℂ) * x0 ^ 2 * x1 ^ 3) + ((-78558390625 / 9 : ℂ) * x0 * x1 ^ 4))) + (((5483083289365625 / 31752 : ℂ) * x0 ^ 4) + (((486208705517349125 / 889056 : ℂ) * x0 ^ 3 * x1) + ((-4756060735985319125 / 3556224 : ℂ) * x0 ^ 2 * x1 ^ 2))))) + (((((16531924407453125 / 131712 : ℂ) * x0 * x1 ^ 3) + ((15505531250 * x1 ^ 4) + ((1294377562023221875 / 1778112 : ℂ) * x0 ^ 3))) + (((-21809200715088829625 / 49787136 : ℂ) * x0 ^ 2 * x1) + (((11818137759614479625 / 199148544 : ℂ) * x0 * x1 ^ 2) + ((-1506576460977565625 / 7375872 : ℂ) * x1 ^ 3)))) + ((((-67281564963901115375 / 99574272 : ℂ) * x0 ^ 2) + (((-639811003981723647235 / 2788079616 : ℂ) * x0 * x1) + ((4717421268495970520435 / 11152318464 : ℂ) * x1 ^ 2))) + (((-540785365497527355175 / 1858719744 : ℂ) * x0) + (((57667950309747932194351 / 156132458496 : ℂ) * x1) + ((68029184240508563189225 / 312264916992 : ℂ))))))))) * h0 + (((((950991078125 / 63 : ℂ) * x0 ^ 6) + (((20150635234375 / 294 : ℂ) * x0 ^ 5) + ((3698491917438125 / 49392 : ℂ) * x0 ^ 4))) + ((((-121681497019936625 / 2765952 : ℂ) * x0 ^ 3) + ((-11225497312612428875 / 154893312 : ℂ) * x0 ^ 2)) + (((158435556402246413335 / 8674025472 : ℂ) * x0) + ((2199701798135070101549 / 485745426432 : ℂ)))))) * h6)) + (((((((-661450625 / 392 : ℂ) * x0 ^ 5) + (((-131613855875 / 21952 : ℂ) * x0 ^ 4) + ((1750974571375 / 1229312 : ℂ) * x0 ^ 3))) + (((2061331742734685 / 619573248 : ℂ) * x0 ^ 2) + (((114879730772546639 / 34696101888 : ℂ) * x0) + ((-3021826848090694585 / 647660568576 : ℂ)))))) * h8 + ((((-950991078125 / 56448 : ℂ) * x1) + ((159625253600521808125 / 647660568576 : ℂ)))) * h7) + ((((-661450625 / 87808 : ℂ))) * h9 + (((-3522531250 / 27 : ℂ))) * h5)))
  have h11 : (((((-53342170706820924) + ((57722108850015492 * x1) + (43130216396039443 * x1 ^ 2))) + (((-41238463511955960 * x1 ^ 3) + (-664562414152750 * x1 ^ 4)) + ((446836767020000 * x1 ^ 5) + (29551277593231708 * x0)))) + ((((-88244207305435734 * x0 * x1) + (-61920311462118348 * x0 * x1 ^ 2)) + ((53851324187839208 * x0 * x1 ^ 3) + (22376229579461043 * x0 ^ 2))) + (((-7229758189105052 * x0 ^ 2 * x1) + (6880952210974560 * x0 ^ 3)) + ((28495779458863208 * x0 ^ 3 * x1) + (-1941146046266750 * x0 ^ 4))))) : ℂ) = 0 := by
    linear_combination (((((-5326185156250 / 3 : ℂ))) * h5 + (((((((((17440850350000000 / 81 : ℂ) * x0 ^ 8 * x1 ^ 4) + ((42465969297500000 / 81 : ℂ) * x0 ^ 8 * x1 ^ 3)) + (((17440850350000000 / 27 : ℂ) * x0 ^ 7 * x1 ^ 4) + (((96819490967500000 / 81 : ℂ) * x0 ^ 8 * x1 ^ 2) + ((178328525987500000 / 81 : ℂ) * x0 ^ 7 * x1 ^ 3)))) + ((((25550567840000000 / 81 : ℂ) * x0 ^ 6 * x1 ^ 4) + (((18506047551250000 / 9 : ℂ) * x0 ^ 8 * x1) + ((352659054829375000 / 81 : ℂ) * x0 ^ 7 * x1 ^ 2))) + (((123634103573750000 / 81 : ℂ) * x0 ^ 6 * x1 ^ 3) + ((3650081120000000 * x0 ^ 8) + ((74109448997500000 / 9 : ℂ) * x0 ^ 7 * x1))))) + (((((259552782518750000 / 81 : ℂ) * x0 ^ 6 * x1 ^ 2) + ((-145704839026250000 / 81 : ℂ) * x0 ^ 5 * x1 ^ 3)) + (((-18275227939062500 / 81 : ℂ) * x0 ^ 4 * x1 ^ 4) + ((14397939401562500 * x0 ^ 7) + ((482668429079375000 / 81 : ℂ) * x0 ^ 6 * x1)))) + ((((142343325446875000 / 81 : ℂ) * x0 ^ 5 * x1 ^ 2) + (((-88674159363125000 / 81 : ℂ) * x0 ^ 4 * x1 ^ 3) + ((1023058887641875000 / 81 : ℂ) * x0 ^ 6))) + (((-424794025550468750 / 81 : ℂ) * x0 ^ 5 * x1) + (((2465316961877421875 / 162 : ℂ) * x0 ^ 4 * x1 ^ 2) + ((164830969628515625 / 162 : ℂ) * x0 ^ 3 * x1 ^ 3)))))) + ((((((379044769140625 / 81 : ℂ) * x0 ^ 2 * x1 ^ 4) + ((-586519992804218750 / 81 : ℂ) * x0 ^ 5)) + (((921058442484153125 / 2268 : ℂ) * x0 ^ 4 * x1) + (((13340876261474346875 / 9072 : ℂ) * x0 ^ 3 * x1 ^ 2) + ((-16287140899591015625 / 9072 : ℂ) * x0 ^ 2 * x1 ^ 3)))) + ((((-1156627971953125 / 9 : ℂ) * x0 * x1 ^ 4) + (((13523878456509171875 / 4536 : ℂ) * x0 ^ 4) + ((1002967357806734864375 / 127008 : ℂ) * x0 ^ 3 * x1))) + (((-9682804352760730214375 / 508032 : ℂ) * x0 ^ 2 * x1 ^ 2) + (((11485662823156328125 / 6272 : ℂ) * x0 * x1 ^ 3) + (228130070000000 * x1 ^ 4))))) + (((((2653368145419215640625 / 254016 : ℂ) * x0 ^ 3) + (((-45320953998077953149875 / 7112448 : ℂ) * x0 ^ 2 * x1) + ((21779727837101945859875 / 28449792 : ℂ) * x0 * x1 ^ 2))) + (((-3237823067302763421875 / 1053696 : ℂ) * x1 ^ 3) + (((-137484821836503925653125 / 14224896 : ℂ) * x0 ^ 2) + ((-1314875433347021027017825 / 398297088 : ℂ) * x0 * x1)))) + ((((9025566904755361822571825 / 1593188352 : ℂ) * x1 ^ 2) + (((-1131366342468734541158125 / 265531392 : ℂ) * x0) + ((121453212796566219368429125 / 22304636928 : ℂ) * x1))) + (((123822014973773743794299075 / 44609273856 : ℂ)) + (((-50951932793125000 / 81 : ℂ) * x0 ^ 5 * x1 ^ 4) + ((25475966396562500 / 81 : ℂ) * x0 ^ 3 * x1 ^ 4)))))))) * h0 + (((((1999403197109375 / 9 : ℂ) * x0 ^ 6) + (((14111730610234375 / 14 : ℂ) * x0 ^ 5) + ((7821319424114159375 / 7056 : ℂ) * x0 ^ 4))) + ((((-241083832409230926875 / 395136 : ℂ) * x0 ^ 3) + ((-22744816926536742037625 / 22127616 : ℂ) * x0 ^ 2)) + (((306714936537258925995325 / 1239146496 : ℂ) * x0) + ((2845132034708783608038575 / 69392203776 : ℂ)))))) * h6)) + (((((((-828598405731875 / 9408 : ℂ) * x0 ^ 4) + (((10767141935695375 / 526848 : ℂ) * x0 ^ 3) + ((3891914610729648575 / 88510464 : ℂ) * x0 ^ 2))) + (((272336671834355452325 / 4956585984 : ℂ) * x0) + (((-7163964106307152415923 / 92522938368 : ℂ)) + ((-1394901096875 / 56 : ℂ) * x0 ^ 5))))) * h8 + ((((-1999403197109375 / 8064 : ℂ) * x1) + ((344779597492398109609375 / 92522938368 : ℂ)))) * h7) + ((((-22191608359375 / 81 : ℂ))) * h4 + (((-1394901096875 / 12544 : ℂ))) * h9)))
  have h12 : (((((10680712869111698054717281848) + (2992115253632752759307788028 * x1)) + ((-3042209158963395137622212180 * x1 ^ 2) + ((-711788817891698298612092975 * x1 ^ 3) + (-5130678244270657573298561876 * x0)))) + (((-4512469168946262617930465288 * x0 * x1) + ((1326813988274865466570577019 * x0 * x1 ^ 2) + (-8497668296131549062649507220 * x0 ^ 2))) + ((1106377897502439499398784215 * x0 ^ 2 * x1) + ((1349200468417994442787534013 * x0 ^ 3) + (109959874040473739342411112 * x0 ^ 4))))) : ℂ) = 0 := by
    linear_combination ((((((-26966084205418504645885935853 / 15013715371872000 : ℂ) * x1) + (((823286639034591718473801849 / 625571473828000 : ℂ)) + ((5658315459885528651351696887 / 3002743074374400 : ℂ) * x0)))) * h11 + ((((26966084205418504645885935853 / 32928000 : ℂ))) * h9 + (((244732384638696894091181634748807 / 26342400 : ℂ))) * h6)) + (((((((1258119596304458540973515483876723 / 1176000 : ℂ) * x0) + ((-70658871245109542924972994456161 / 156800 : ℂ))) + (((214103342738060405683438204159873 / 235200 : ℂ) * x1) + ((2674275368516433947454203722993 / 3360 : ℂ) * x1 ^ 2)))) * h0 + ((((-1183775336655993675678666538241 / 53620412042400 : ℂ)) + (((3668961555253320724549901737049 / 142987765446400 : ℂ) * x1) + ((-2674275368516433947454203722993 / 85792659267840 : ℂ) * x0)))) * h10) + ((((-7271665914094208790372257882761 / 13171200 : ℂ))) * h7 + (((1344330063692141253162647649517 / 43904000 : ℂ))) * h8)))
  have h13 : (((((35820355171508687654761906000) + (9981716477680239730633498060 * x1)) + ((-10644831382956767338247155770 * x1 ^ 2) + ((-2358124296196552646412250475 * x1 ^ 3) + (-17948786524952001314219835108 * x0)))) + (((-16133255561328886241177017996 * x0 * x1) + ((5247571946327937994438486631 * x0 * x1 ^ 2) + (-27889742601076577774916085034 * x0 ^ 2))) + ((5073802177804157713249645835 * x0 ^ 2 * x1) + ((5086649269986293091321818041 * x0 ^ 3) + (366532913468245797808037040 * x0 ^ 3 * x1))))) : ℂ) = 0 := by
    linear_combination ((((((5475289975695937721681028526151 / 61280470905600 : ℂ) * x1) + (((-593291043638483888589879822081 / 7149388272320 : ℂ)) + ((-640337560274716311993502910649 / 5719510617856 : ℂ) * x0)))) * h10 + ((((-8511290623640265194069673303947 / 4390400 : ℂ))) * h7 + (((31739514943131754207875171993805 / 1053696 : ℂ))) * h6)) + (((((((635887390495733962870804211787359 / 168000 : ℂ) * x0) + ((-742202823346139716336530106413133 / 470400 : ℂ))) + (((28125236790220493619856761100783 / 9408 : ℂ) * x1) + ((640337560274716311993502910649 / 224 : ℂ) * x1 ^ 2)))) * h0 + ((((3753192759595848490781006141 / 750685768593600 : ℂ)) + (((-13432073274007451282953833649 / 2144816481696000 : ℂ) * x1) + ((815405690366081735209653769 / 120109722974976 : ℂ) * x0)))) * h11) + ((((13432073274007451282953833649 / 4704000 : ℂ))) * h9 + (((2912210738092428155705154726413 / 26342400 : ℂ))) * h8)))
  have h14 : (((((-20651383345246035863807536720) + (-5381913310437009490484412300 * x1)) + ((6321789349871872434304661810 * x1 ^ 2) + ((1090716248541766380687891175 * x1 ^ 3) + (10437505418544196820319689348 * x0)))) + (((8600639125172097353837534076 * x0 * x1) + ((-3412721303632167469434798371 * x0 * x1 ^ 2) + (366532913468245797808037040 * x0 * x1 ^ 3))) + ((15981411459355457477226011074 * x0 ^ 2) + ((-2880605133398471827179789095 * x0 ^ 2 * x1) + (-2847225730060342757742963741 * x0 ^ 3))))) : ℂ) = 0 := by
    linear_combination ((((((-3154701400778159880908019 / 817072945408 : ℂ) * x0) + (((-2128148101119361858093247651 / 750685768593600 : ℂ)) + ((53595450274217229969575340623 / 15013715371872000 : ℂ) * x1)))) * h11 + ((((14546550771429343712674929507301 / 13171200 : ℂ))) * h7 + (((-4828870213978459680531309851 / 76800 : ℂ))) * h8)) + (((((-17902433634353489414624066799029 / 1053696 : ℂ))) * h6 + (((((-325932539771011480133757302591 / 192 : ℂ) * x1) + ((423318282938465989005777125751613 / 470400 : ℂ))) + (((-2537088620356657171366433616849793 / 1176000 : ℂ) * x0) + ((-156067584222114134495499951101 / 96 : ℂ) * x1 ^ 2)))) * h0) + (((((1011711285297260482331561596493 / 21448164816960 : ℂ)) + (((-21847146762946351448889252873977 / 428963296339200 : ℂ) * x1) + ((156067584222114134495499951101 / 2451218836224 : ℂ) * x0)))) * h10 + (((-53595450274217229969575340623 / 32928000 : ℂ))) * h9)))
  have h15 : (((((-1619167181582909218620937759464) + (-508491247572179149408622376908 * x1)) + ((477972255767493141629828129168 * x1 ^ 2) + ((114737768225135091081780315695 * x1 ^ 3) + (2748996851011843483560277800 * x1 ^ 4)))) + (((803305589996173021937123151908 * x0) + ((758071247075711867179564455440 * x0 * x1) + (-231414502218070886648887199115 * x0 * x1 ^ 2))) + ((1282015548835435304970975655568 * x0 ^ 2) + ((-164273084044068233267759119335 * x0 ^ 2 * x1) + (-215078670162999955406059977245 * x0 ^ 3))))) : ℂ) = 0 := by
    linear_combination ((((((426336141599414729956353946372537 / 85792659267840 : ℂ) * x0) + (((1432161342284480812612601649611 / 403160992800 : ℂ)) + ((-2913173175422635935994184856439861 / 714938827232000 : ℂ) * x1)))) * h10 + ((((((-426336141599414729956353946372537 / 3360 : ℂ) * x1 ^ 2) + ((-1255557242649141599378831158368625 / 9408 : ℂ) * x1)) + (((57786055972888942030132241545038637 / 784000 : ℂ)) + ((-203572519205231836912370150281269563 / 1176000 : ℂ) * x0)))) * h0 + (((-215369618166739390525028290838101 / 43904000 : ℂ))) * h8)) + (((((-190450405384404625548343150545217 / 150528 : ℂ))) * h6 + ((((-200581104727963146134015247 / 940708983200 : ℂ)) + (((4289017727673620814102434415973 / 15013715371872000 : ℂ) * x1) + ((-180931432559911488174381749347 / 600548614874880 : ℂ) * x0)))) * h11) + ((((-4289017727673620814102434415973 / 32928000 : ℂ))) * h9 + (((5783286580008262405353634701433229 / 65856000 : ℂ))) * h7)))
  have h16 : ((((88935695238717873213617) + (23853844768132701136127 * x1)) + ((5761012053078082706475 * x1 ^ 2) + ((-133523236407762221555684 * x0) + (83193749560330574023310 * x0 ^ 3)))) : ℂ) = 0 := by
    linear_combination (((((((-47514853665931175411706412981547312640089803162340223106390619071871687 / 1794945916577995913344747215436649660888192982176055196018149254963735635200 : ℂ) * x1) + (((-720154395070147102181721841717693016061627982598414360273150936419645947161459644903 / 716114134231662781776552607540053546510410262361965168076626955653408320156012599200000 : ℂ)) + ((33388722225539132553301004989755847690732796771306833494431 / 4649312350901653933532424344213126536709590165674820890972090000 : ℂ) * x0)))) * h15 + (((47514853665931175411706412981547312640089803162340223106390619071871687 / 291760185190552936953106389822234177767336896481388802999680000 : ℂ))) * h11) + (((((-23912833443391520651090221824351797661476701119959887460795292433282284275331542849791 / 716114134231662781776552607540053546510410262361965168076626955653408320156012599200000 : ℂ)) + ((-16596540057131135289051305190169773738187549951397418905081834748670762787 / 86295476758557495833882077665223541388855431835387269039334098796333444000000 : ℂ) * x1))) * h12 + ((((1120904803286695641995120316467882195554445476902213425185170718189596487721847990941903 / 2983808892631928257402302531416889777126709426508188200319278981889201333983385830000000 : ℂ)) + ((18218709979237070744096158703933838927762468460358641301817942252881035639271 / 1558112774807288119222870846733202830632111963694492357654643450489353850000000 : ℂ) * x1))) * h13)) + ((((((9699336144419240824549023322338423482293790454770060259339822913752941132791 / 6801518630625344341868697077198138017588713579000000 : ℂ)) + (((3238975966120115340576907282611246668370738391976772566690739 / 63422849354897596801134061301710714375 : ℂ) * x1) + ((-18218709979237070744096158703933838927762468460358641301817942252881035639271 / 17003796576563360854671742692995345043971783947500000 : ℂ) * x0)))) * h0 + ((((2156472403131182273360082038446814842309403391774633449418714957054187336740016233815903 / 2983808892631928257402302531416889777126709426508188200319278981889201333983385830000000 : ℂ)) + (((35113459359349050021958348458623905534082772534891046635953108378687260764811 / 1558112774807288119222870846733202830632111963694492357654643450489353850000000 : ℂ) * x1) + ((-1079658655373371780192302427537082222790246130658924188896913 / 1937213479542355805638510143422136056962329235697842037905037500 : ℂ) * x0)))) * h14) + ((((-32406906965025601186554474933982864617084351810247687275976555276735381457429 / 400769485151858429880640645360211782647440791870039564560000000 : ℂ))) * h10 + (((16596540057131135289051305190169773738187549951397418905081834748670762787 / 87896548457312142264149316074560552842684913944000000 : ℂ))) * h6)))
  have h17 : ((((-99533628647561010350151) + (-153253531959081509763081 * x1)) + ((-26504075245676424704585 * x1 ^ 2) + ((-44530353951783899381368 * x0) + (83193749560330574023310 * x0 ^ 2 * x1)))) : ℂ) = 0 := by
    linear_combination (((((((-194677200805296106206505068340587274325032006091075141360875539380039401267039 / 4674338324421864357668612540199608491896335891083477072963930351468061550000000 : ℂ) * x1) + (((-539756115562135099645078068554478193650418023520069305456925616635079767058866970736757 / 426258413233132608200328933059555682446672775215455457188468425984171619140483690000000 : ℂ)) + ((-38162147320488993575265341740573822909034335209255906686713327 / 23246561754508269667662121721065632683547950828374104454860450000 : ℂ) * x0)))) * h14 + (((82283142452805705499559258597716693813112338508446265859196686853220290122199 / 578889256330462176494258709964750352712970032701168259920000000 : ℂ))) * h10) + (((((6196578423831700955051033398303834909539194925724187850201595513337294398039140897029 / 102302019175951825968078943934293363787201466051709309725232422236201188593716085600000 : ℂ)) + ((7040481543092821054341146739173853916896601171840799499621091198738269253673 / 1121841197861247445840467009647906038055120613860034497511343284352334772000000 : ℂ) * x1))) * h12 + ((((-279789117195609650198111695321013150145719714951988230579921767371011780855934883428757 / 426258413233132608200328933059555682446672775215455457188468425984171619140483690000000 : ℂ)) + ((-107509446927845485302139056823954384359591585440751271232468341471000598728579 / 4674338324421864357668612540199608491896335891083477072963930351468061550000000 : ℂ) * x1))) * h13)) + ((((((-49213302945374654016844510693703349120654057045210285041748355284688884071059 / 20404555891876033025606091231594414052766140737000000 : ℂ)) + (((38162147320488993575265341740573822909034335209255906686713327 / 253691397419590387204536245206842857500 : ℂ) * x1) + ((107509446927845485302139056823954384359591585440751271232468341471000598728579 / 51011389729690082564015228078986035131915351842500000 : ℂ) * x0)))) * h0 + ((((185825192677225794538671828373098372793104723950774223911876129111744952385504480157 / 102302019175951825968078943934293363787201466051709309725232422236201188593716085600000 : ℂ)) + (((99648507973218818209671521381303219657214314163113333617854534080372441 / 1794945916577995913344747215436649660888192982176055196018149254963735635200 : ℂ) * x1) + ((16345977587401192944397819451107567210180133481579797337667 / 774885391816942322255404057368854422784931694279136815162015000 : ℂ) * x0)))) * h15) + ((((-99648507973218818209671521381303219657214314163113333617854534080372441 / 291760185190552936953106389822234177767336896481388802999680000 : ℂ))) * h11 + (((-7040481543092821054341146739173853916896601171840799499621091198738269253673 / 1142655129945057849433941108969287186954903881272000000 : ℂ))) * h6)))
  have h18 : ((((143954085571837378130053) + (214292930846225783059633 * x1)) + ((-6465623049335859210065 * x1 ^ 2) + ((140434503654248709311434 * x0) + (83193749560330574023310 * x0 * x1 ^ 2)))) : ℂ) = 0 := by
    linear_combination (((((((-383175042194527000167947110016382937563196670825231690710801 / 4649312350901653933532424344213126536709590165674820890972090000 : ℂ) * x0) + (((344788498702818939336157163291559824176971151303312875373115239550648775259373710813 / 716114134231662781776552607540053546510410262361965168076626955653408320156012599200000 : ℂ)) + ((-9945599024613820817662645924607254583643340648022347923277696893192683 / 1794945916577995913344747215436649660888192982176055196018149254963735635200 : ℂ) * x1)))) * h15 + (((82368568677348117472348377757658911783472703795883715345643403842678794110289 / 1736667768991386529482776129894251058138910098103504779760000000 : ℂ))) * h10) + (((((11257852454171976311204165598512181432038123541727598677039600488210731053157765382661 / 716114134231662781776552607540053546510410262361965168076626955653408320156012599200000 : ℂ)) + ((-15466469149386047485921684017714588256912686017653904321084427132514078632299 / 1121841197861247445840467009647906038055120613860034497511343284352334772000000 : ℂ) * x1))) * h12 + ((((-685310028542246424126189552855446176608478366697172236703354689633415253436400687527213 / 2983808892631928257402302531416889777126709426508188200319278981889201333983385830000000 : ℂ)) + ((-5282019263740983251211515105923793240695926601656734322580133024784632215823 / 4674338324421864357668612540199608491896335891083477072963930351468061550000000 : ℂ) * x1))) * h13)) + ((((((-21446902625179931413876077899191363442262588117994113971547371205499897297583 / 20404555891876033025606091231594414052766140737000000 : ℂ)) + (((-37357524687234589032211699702583671880185687811372257105386944 / 63422849354897596801134061301710714375 : ℂ) * x1) + ((5282019263740983251211515105923793240695926601656734322580133024784632215823 / 51011389729690082564015228078986035131915351842500000 : ℂ) * x0)))) * h0 + ((((-1294736486363423998760587163866424452563779561192377910135596732546144975236173830739213 / 2983808892631928257402302531416889777126709426508188200319278981889201333983385830000000 : ℂ)) + (((-39554058308442421041412365134168469829910050594935850188357707788157908829843 / 4674338324421864357668612540199608491896335891083477072963930351468061550000000 : ℂ) * x1) + ((9339381171808647258052924925645917970046421952843064276346736 / 1452910109656766854228882607566602042721746926773381528428778125 : ℂ) * x0)))) * h14) + ((((9945599024613820817662645924607254583643340648022347923277696893192683 / 291760185190552936953106389822234177767336896481388802999680000 : ℂ))) * h11 + (((15466469149386047485921684017714588256912686017653904321084427132514078632299 / 1142655129945057849433941108969287186954903881272000000 : ℂ))) * h6)))
  have h19 : ((((-580295027575084943163539) + (-469557336440867236144199 * x1)) + ((159314157991945795522155 * x1 ^ 2) + ((83193749560330574023310 * x1 ^ 3) + (-514871251657104617787322 * x0)))) : ℂ) = 0 := by
    linear_combination (((((((-7282484919229414892923793055914246493832226684352592252616037 / 596065686013032555581080044129888017526870534060874473201550000 : ℂ) * x0) + (((16597363013439246670760890931986749739543699498180976602572978113380278745489259592960209 / 2983808892631928257402302531416889777126709426508188200319278981889201333983385830000000 : ℂ)) + ((261042241381552989684876929671258933752210213208096549071732599031504040585183 / 1558112774807288119222870846733202830632111963694492357654643450489353850000000 : ℂ) * x1)))) * h14 + ((((21847454757688244678771379167742739481496680053057776757848111 / 19514722878430029784964326554372527500 : ℂ) * x1) + (((76863638516039727083845981464981387548909800920712178279155915743083569957123 / 6801518630625344341868697077198138017588713579000000 : ℂ)) + ((-128805331311996033334692828175964857377561996303814502040179293424929609998563 / 17003796576563360854671742692995345043971783947500000 : ℂ) * x0)))) * h0) + (((((-181082748505271263004191527729516363205031965592268467155217254900732088710792995643273 / 716114134231662781776552607540053546510410262361965168076626955653408320156012599200000 : ℂ)) + ((17024347661114064815165173030759577894660988993008402301905464725153241887157 / 1121841197861247445840467009647906038055120613860034497511343284352334772000000 : ℂ) * x1))) * h12 + ((((8641338356795061814851711956843203533328543094923184365394155078215494324688835267386209 / 2983808892631928257402302531416889777126709426508188200319278981889201333983385830000000 : ℂ)) + ((128805331311996033334692828175964857377561996303814502040179293424929609998563 / 1558112774807288119222870846733202830632111963694492357654643450489353850000000 : ℂ) * x1))) * h13)) + ((((((-332732507058384138301539375326166054690598234591244809123009061483961371 / 1794945916577995913344747215436649660888192982176055196018149254963735635200 : ℂ) * x1) + (((-5444987054570316845273555940808380687441480746999613590609414301689291138205047032609 / 716114134231662781776552607540053546510410262361965168076626955653408320156012599200000 : ℂ)) + ((363556415868984617560272115487975070880555707277544948118409 / 2324656175450826966766212172106563268354795082837410445486045000 : ℂ) * x0)))) * h15 + (((332732507058384138301539375326166054690598234591244809123009061483961371 / 291760185190552936953106389822234177767336896481388802999680000 : ℂ))) * h11) + ((((-3239559435306203421198449341339178979298241589133023135882413585814134305757981 / 5210003306974159588448328389682753174416730294310514339280000000 : ℂ))) * h10 + (((-17024347661114064815165173030759577894660988993008402301905464725153241887157 / 1142655129945057849433941108969287186954903881272000000 : ℂ))) * h6)))
  have h20 : ((((-8680455321686459839942) + (-675762220450919060735 * x1)) + ((-232849750919128563589 * x1 ^ 2) + ((7117690054156614490439 * x0) + (8319374956033057402331 * x0 ^ 2)))) : ℂ) = 0 := by
    linear_combination (((((((-1242293679042689511747707241334043811406224726565368240183773712600606155581 / 779056387403644059611435423366601415316055981847246178827321725244676925000000 : ℂ) * x1) + ((-37594214915247894523932563473910171088402148763102730926074466722348935163016338797179 / 745952223157982064350575632854222444281677356627047050079819745472300333495846457500000 : ℂ)))) * h13 + ((((1242293679042689511747707241334043811406224726565368240183773712600606155581 / 8501898288281680427335871346497672521985891973750000 : ℂ) * x0) + (((-651556212761980739187406838539422739484677347633016099144763707609857105301 / 3400759315312672170934348538599069008794356789500000 : ℂ)) + ((-78713514400951235064688091232524632278075756547322837139089 / 19514722878430029784964326554372527500 : ℂ) * x1)))) * h0) + (((((-72349509890492882599005241056614891336440892546498703289975482465519766428416621601929 / 745952223157982064350575632854222444281677356627047050079819745472300333495846457500000 : ℂ)) + (((-2377287095031200096410090509462039948143467865223440228858790193632508058021 / 779056387403644059611435423366601415316055981847246178827321725244676925000000 : ℂ) * x1) + ((78713514400951235064688091232524632278075756547322837139089 / 1788197058039097666743240132389664052580611602182623419604650000 : ℂ) * x0)))) * h14 + ((((12133371162993783835993944569121939195197044977510074001642101858167431721929761177 / 89514266778957847722069075942506693313801282795245646009578369456676040019501574900000 : ℂ)) + (((3368426195764413395984052320717816060689490947391870808728991989292097 / 897472958288997956672373607718324830444096491088027598009074627481867817600 : ℂ) * x1) + ((-2600002790997901592149118278525292776658248333776490670707 / 4649312350901653933532424344213126536709590165674820890972090000 : ℂ) * x0)))) * h15)) + (((((-3368426195764413395984052320717816060689490947391870808728991989292097 / 145880092595276468476553194911117088883668448240694401499840000 : ℂ))) * h11 + ((((404104033043269006097177375649769976181643087631198666019528555297258709006400839019 / 89514266778957847722069075942506693313801282795245646009578369456676040019501574900000 : ℂ)) + ((52583449068131384647037726730206900639091870633303194503770251207008383241 / 560920598930623722920233504823953019027560306930017248755671642176167386000000 : ℂ) * x1))) * h12) + ((((28303737863430065403548498243497989127495861437429500151138702938851860755047 / 2605001653487079794224164194841376587208365147155257169640000000 : ℂ))) * h10 + (((-52583449068131384647037726730206900639091870633303194503770251207008383241 / 571327564972528924716970554484643593477451940636000000 : ℂ))) * h6)))
  have h21 : ((((19635815934513857380282) + (12573584580506421792359 * x1)) + ((5665594678391990336724 * x1 ^ 2) + ((7281635206678770729085 * x0) + (16638749912066114804662 * x0 * x1)))) : ℂ) = 0 := by
    linear_combination (((((((-750960477117710519027139706851864387961832388827086813872273345084832423409 / 560920598930623722920233504823953019027560306930017248755671642176167386000000 : ℂ) * x1) + ((-536249250717351401439380786135455852102231069113014467055390912603688356873558356051 / 89514266778957847722069075942506693313801282795245646009578369456676040019501574900000 : ℂ)))) * h12 + (((750960477117710519027139706851864387961832388827086813872273345084832423409 / 571327564972528924716970554484643593477451940636000000 : ℂ))) * h6) + ((((-35514225594410518982587524429107897838088724799570626384348320319532784907423 / 2605001653487079794224164194841376587208365147155257169640000000 : ℂ))) * h10 + ((((3583473383643408539326951018265868927109465726793803746721768896148942271325114928297 / 57380940242921697257736587142632495713975181279003619236909211190176948730449727500000 : ℂ)) + ((650590524138097242996242837150039943632279027515363776305494344562415148943 / 259685462467881353203811807788867138438685327282415392942440575081558975000000 : ℂ) * x1))) * h13)) + ((((((251303342659333319536727611662811618087034157154790737396727743064385048103 / 1133586438437557390311449512866356336264785596500000 : ℂ)) + (((-11622218173135430130949324887432148939457562773407081254278027 / 253691397419590387204536245206842857500 : ℂ) * x1) + ((-650590524138097242996242837150039943632279027515363776305494344562415148943 / 2833966096093893475778623782165890840661963991250000 : ℂ) * x0)))) * h0 + ((((90151492917705264042138294737606931103407151376973550189442071704307401632465701561711 / 745952223157982064350575632854222444281677356627047050079819745472300333495846457500000 : ℂ)) + (((3309906599454747179550717875675090406607224647377276375094884313638775270789 / 779056387403644059611435423366601415316055981847246178827321725244676925000000 : ℂ) * x1) + ((11622218173135430130949324887432148939457562773407081254278027 / 23246561754508269667662121721065632683547950828374104454860450000 : ℂ) * x0)))) * h14) + (((((-16041962816665171310729695035716329752175671160017403649970709636241649500685837853 / 89514266778957847722069075942506693313801282795245646009578369456676040019501574900000 : ℂ)) + (((-5890105487582892521997686888779703956023157128432668410376077514512649 / 897472958288997956672373607718324830444096491088027598009074627481867817600 : ℂ) * x1) + ((-29829516787727286587419973302795836265767591298924000720837 / 4649312350901653933532424344213126536709590165674820890972090000 : ℂ) * x0)))) * h15 + (((5890105487582892521997686888779703956023157128432668410376077514512649 / 145880092595276468476553194911117088883668448240694401499840000 : ℂ))) * h11)))
  have h22 : ((1) : ℂ) = 0 := by
    linear_combination ((((((193427771300909420480586433470519139370224006724175470221 / 3595438907025058774176404696907516471512065402265957214348487446910012084800 : ℂ) * x0) + (((-552898664490960772227218192413936852415954410378707931927 / 10786316721075176322529214090722549414536196206797871643045462340730036254400 : ℂ)) + ((-460209903295299733226282008850470776379113592572663969463 / 10786316721075176322529214090722549414536196206797871643045462340730036254400 : ℂ) * x1)))) * h20 + ((((-193427771300909420480586433470519139370224006724175470221 / 35954389070250587741764046969075164715120654022659572143484874469100120848000 : ℂ))) * h16 + (((20660866922731749995947775204429161947606514250491286561 / 107863167210751763225292140907225494145361962067978716430454623407300362544000 : ℂ))) * h18)) + (((((36457305201974875164179579346478237437611167969293639583 / 2157263344215035264505842818144509882907239241359574328609092468146007250880 : ℂ)) + (((-6041086767662384422550805299826894030484273577834766967 / 2696579180268794080632303522680637353634049051699467910761365585182509063600 : ℂ) * x1) + ((16119131119103211893045638269969104949339245030111706467 / 2696579180268794080632303522680637353634049051699467910761365585182509063600 : ℂ) * x0)))) * h21 + ((((143018604040157265272817021260115821166241478376214399 / 4314526688430070529011685636289019765814478482719148657218184936292014501760 : ℂ))) * h19 + (((110418951447491346027305634230239312261466544110590105909 / 35954389070250587741764046969075164715120654022659572143484874469100120848000 : ℂ))) * h17)))
  norm_num at h22

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
theorem c4_open_0_v_nonzero (x0 x1 : ℂ)
    (h0 : (((((4) + (4 * x1)) + ((-5 * x1 ^ 2) + (-4 * x0))) + (((-6 * x0 * x1) + (4 * x0 * x1 ^ 2)) + ((-5 * x0 ^ 2) + ((-4 * x0 ^ 2 * x1) + (4 * x0 ^ 2 * x1 ^ 2))))) : ℂ) = 0)
    (h1 : ((((((6 * x1) + ((-48 * x1 ^ 2) + (-39 * x1 ^ 3))) + (((10 * x0) + (-10 * x0 * x1)) + ((114 * x0 * x1 ^ 2) + (101 * x0 * x1 ^ 3)))) + ((((37 * x0 * x1 ^ 4) + (-14 * x0 ^ 2)) + ((-65 * x0 ^ 2 * x1) + (-114 * x0 ^ 2 * x1 ^ 2))) + (((-184 * x0 ^ 2 * x1 ^ 3) + (-130 * x0 ^ 2 * x1 ^ 4)) + ((-30 * x0 ^ 3) + (117 * x0 ^ 3 * x1))))) + (((((12 * x0 ^ 3 * x1 ^ 2) + (168 * x0 ^ 3 * x1 ^ 3)) + ((75 * x0 ^ 3 * x1 ^ 4) + (40 * x0 ^ 4))) + (((56 * x0 ^ 4 * x1) + (330 * x0 ^ 4 * x1 ^ 2)) + ((265 * x0 ^ 4 * x1 ^ 3) + (92 * x0 ^ 4 * x1 ^ 4)))) + ((((19 * x0 ^ 5) + (-44 * x0 ^ 5 * x1)) + ((-87 * x0 ^ 5 * x1 ^ 2) + (-152 * x0 ^ 5 * x1 ^ 3))) + (((-20 * x0 ^ 5 * x1 ^ 4) + (3 * x0 ^ 6 * x1)) + ((-156 * x0 ^ 6 * x1 ^ 2) + (-132 * x0 ^ 6 * x1 ^ 3)))))) : ℂ) = 0)
    (h3 : (((((((24 * x1) + ((102 * x1 ^ 2) + (207 * x1 ^ 3))) + (((156 * x1 ^ 4) + (-3 * x1 ^ 5)) + ((16 * x0) + (48 * x0 * x1)))) + ((((-57 * x0 * x1 ^ 2) + (-392 * x0 * x1 ^ 3)) + ((-639 * x0 * x1 ^ 4) + (-183 * x0 * x1 ^ 5))) + (((x0 * x1 ^ 6) + (18 * x0 ^ 2)) + ((-103 * x0 ^ 2 * x1) + (-188 * x0 ^ 2 * x1 ^ 2))))) + (((((-51 * x0 ^ 2 * x1 ^ 3) + (514 * x0 ^ 2 * x1 ^ 4)) + ((566 * x0 ^ 2 * x1 ^ 5) + (-84 * x0 ^ 2 * x1 ^ 6))) + (((-143 * x0 ^ 3) + (-516 * x0 ^ 3 * x1)) + ((-636 * x0 ^ 3 * x1 ^ 2) + (-713 * x0 ^ 3 * x1 ^ 3)))) + ((((-242 * x0 ^ 3 * x1 ^ 4) + (-1202 * x0 ^ 3 * x1 ^ 5)) + ((-205 * x0 ^ 3 * x1 ^ 6) + (-60 * x0 ^ 4))) + (((672 * x0 ^ 4 * x1) + (1444 * x0 ^ 4 * x1 ^ 2)) + ((2058 * x0 ^ 4 * x1 ^ 3) + (1392 * x0 ^ 4 * x1 ^ 4)))))) + ((((((1560 * x0 ^ 4 * x1 ^ 5) + (1328 * x0 ^ 4 * x1 ^ 6)) + ((373 * x0 ^ 5) + (1022 * x0 ^ 5 * x1))) + (((685 * x0 ^ 5 * x1 ^ 2) + (1726 * x0 ^ 5 * x1 ^ 3)) + ((1020 * x0 ^ 5 * x1 ^ 4) + (1702 * x0 ^ 5 * x1 ^ 5)))) + ((((-866 * x0 ^ 5 * x1 ^ 6) + (120 * x0 ^ 6)) + ((-928 * x0 ^ 6 * x1) + (-1040 * x0 ^ 6 * x1 ^ 2))) + (((-2184 * x0 ^ 6 * x1 ^ 3) + (-2012 * x0 ^ 6 * x1 ^ 4)) + ((-3134 * x0 ^ 6 * x1 ^ 5) + (-1360 * x0 ^ 6 * x1 ^ 6))))) + (((((-324 * x0 ^ 7) + (-648 * x0 ^ 7 * x1)) + ((-19 * x0 ^ 7 * x1 ^ 2) + (-1802 * x0 ^ 7 * x1 ^ 3))) + (((-1698 * x0 ^ 7 * x1 ^ 4) + (-1496 * x0 ^ 7 * x1 ^ 5)) + ((1204 * x0 ^ 7 * x1 ^ 6) + (604 * x0 ^ 8 * x1)))) + ((((-504 * x0 ^ 8 * x1 ^ 2) + (446 * x0 ^ 8 * x1 ^ 3)) + ((768 * x0 ^ 8 * x1 ^ 4) + (1932 * x0 ^ 8 * x1 ^ 5))) + (((388 * x0 ^ 9 * x1 ^ 2) + (776 * x0 ^ 9 * x1 ^ 3)) + ((-68 * x0 ^ 9 * x1 ^ 4) + (-540 * x0 ^ 10 * x1 ^ 3))))))) : ℂ) = 0)
    (h_open : x0 ^ 2 + x0 - 1 ≠ 0) : False := by
  have h4 : ((((((-6 * x1) + ((48 * x1 ^ 2) + (39 * x1 ^ 3))) + (((-10 * x0) + (10 * x0 * x1)) + ((-114 * x0 * x1 ^ 2) + (-101 * x0 * x1 ^ 3)))) + ((((-37 * x0 * x1 ^ 4) + (14 * x0 ^ 2)) + ((65 * x0 ^ 2 * x1) + (114 * x0 ^ 2 * x1 ^ 2))) + (((184 * x0 ^ 2 * x1 ^ 3) + (130 * x0 ^ 2 * x1 ^ 4)) + ((30 * x0 ^ 3) + (-117 * x0 ^ 3 * x1))))) + (((((-12 * x0 ^ 3 * x1 ^ 2) + (-168 * x0 ^ 3 * x1 ^ 3)) + ((-75 * x0 ^ 3 * x1 ^ 4) + (-40 * x0 ^ 4))) + (((-56 * x0 ^ 4 * x1) + (-330 * x0 ^ 4 * x1 ^ 2)) + ((-265 * x0 ^ 4 * x1 ^ 3) + (-92 * x0 ^ 4 * x1 ^ 4)))) + ((((-19 * x0 ^ 5) + (44 * x0 ^ 5 * x1)) + ((87 * x0 ^ 5 * x1 ^ 2) + (152 * x0 ^ 5 * x1 ^ 3))) + (((20 * x0 ^ 5 * x1 ^ 4) + (-3 * x0 ^ 6 * x1)) + ((156 * x0 ^ 6 * x1 ^ 2) + (132 * x0 ^ 6 * x1 ^ 3)))))) : ℂ) = 0 := by
    linear_combination ((-1)) * h1
  have h5 : (((((((-24 * x1) + ((-102 * x1 ^ 2) + (-207 * x1 ^ 3))) + (((-156 * x1 ^ 4) + (3 * x1 ^ 5)) + ((-16 * x0) + (-48 * x0 * x1)))) + ((((57 * x0 * x1 ^ 2) + (392 * x0 * x1 ^ 3)) + ((639 * x0 * x1 ^ 4) + (183 * x0 * x1 ^ 5))) + (((-(x0 * x1 ^ 6)) + (-18 * x0 ^ 2)) + ((103 * x0 ^ 2 * x1) + (188 * x0 ^ 2 * x1 ^ 2))))) + (((((51 * x0 ^ 2 * x1 ^ 3) + (-514 * x0 ^ 2 * x1 ^ 4)) + ((-566 * x0 ^ 2 * x1 ^ 5) + (84 * x0 ^ 2 * x1 ^ 6))) + (((143 * x0 ^ 3) + (516 * x0 ^ 3 * x1)) + ((636 * x0 ^ 3 * x1 ^ 2) + (713 * x0 ^ 3 * x1 ^ 3)))) + ((((242 * x0 ^ 3 * x1 ^ 4) + (1202 * x0 ^ 3 * x1 ^ 5)) + ((205 * x0 ^ 3 * x1 ^ 6) + (60 * x0 ^ 4))) + (((-672 * x0 ^ 4 * x1) + (-1444 * x0 ^ 4 * x1 ^ 2)) + ((-2058 * x0 ^ 4 * x1 ^ 3) + (-1392 * x0 ^ 4 * x1 ^ 4)))))) + ((((((-1560 * x0 ^ 4 * x1 ^ 5) + (-1328 * x0 ^ 4 * x1 ^ 6)) + ((-373 * x0 ^ 5) + (-1022 * x0 ^ 5 * x1))) + (((-685 * x0 ^ 5 * x1 ^ 2) + (-1726 * x0 ^ 5 * x1 ^ 3)) + ((-1020 * x0 ^ 5 * x1 ^ 4) + (-1702 * x0 ^ 5 * x1 ^ 5)))) + ((((866 * x0 ^ 5 * x1 ^ 6) + (-120 * x0 ^ 6)) + ((928 * x0 ^ 6 * x1) + (1040 * x0 ^ 6 * x1 ^ 2))) + (((2184 * x0 ^ 6 * x1 ^ 3) + (2012 * x0 ^ 6 * x1 ^ 4)) + ((3134 * x0 ^ 6 * x1 ^ 5) + (1360 * x0 ^ 6 * x1 ^ 6))))) + (((((324 * x0 ^ 7) + (648 * x0 ^ 7 * x1)) + ((19 * x0 ^ 7 * x1 ^ 2) + (1802 * x0 ^ 7 * x1 ^ 3))) + (((1698 * x0 ^ 7 * x1 ^ 4) + (1496 * x0 ^ 7 * x1 ^ 5)) + ((-1204 * x0 ^ 7 * x1 ^ 6) + (-604 * x0 ^ 8 * x1)))) + ((((504 * x0 ^ 8 * x1 ^ 2) + (-446 * x0 ^ 8 * x1 ^ 3)) + ((-768 * x0 ^ 8 * x1 ^ 4) + (-1932 * x0 ^ 8 * x1 ^ 5))) + (((-388 * x0 ^ 9 * x1 ^ 2) + (-776 * x0 ^ 9 * x1 ^ 3)) + ((68 * x0 ^ 9 * x1 ^ 4) + (540 * x0 ^ 10 * x1 ^ 3))))))) : ℂ) = 0 := by
    linear_combination ((-1)) * h3
  have h7 : ((((((152) + (92 * x1)) + ((-138 * x1 ^ 2) + ((167 * x1 ^ 3) + (-80 * x1 ^ 4)))) + (((-216 * x0) + (-200 * x0 * x1)) + ((102 * x0 * x1 ^ 2) + ((-320 * x0 * x1 ^ 3) + (100 * x0 * x1 ^ 4))))) + ((((274 * x0 ^ 2) + (631 * x0 ^ 2 * x1)) + ((-356 * x0 ^ 3) + ((-956 * x0 ^ 3 * x1) + (-732 * x0 ^ 4)))) + (((-948 * x0 ^ 4 * x1) + (308 * x0 ^ 5)) + ((640 * x0 ^ 5 * x1) + ((320 * x0 ^ 6) + (400 * x0 ^ 6 * x1)))))) : ℂ) = 0 := by
    linear_combination ((((8 / 9 : ℂ))) * h4 + ((((((-88 / 3 : ℂ) * x0 ^ 4 * x1) + (((-40 / 9 : ℂ) * x0 ^ 3 * x1 ^ 2) + (-64 * x0 ^ 4))) + ((((-80 / 9 : ℂ) * x0 ^ 3 * x1) + ((224 / 9 : ℂ) * x0 ^ 2 * x1 ^ 2)) + (((-124 / 9 : ℂ) * x0 ^ 3) + ((148 / 3 : ℂ) * x0 ^ 2 * x1)))) + ((((-124 / 9 : ℂ) * x0 * x1 ^ 2) + (((892 / 9 : ℂ) * x0 ^ 2) + ((44 / 9 : ℂ) * x0 * x1))) + (((16 * x1 ^ 2) + ((-124 / 9 : ℂ) * x0)) + (((-41 / 3 : ℂ) * x1) + (38)))))) * h0)
  have h8 : ((((((252) + (-4948 * x1)) + ((-283 * x1 ^ 2) + ((8772 * x1 ^ 3) + (-6220 * x1 ^ 4)))) + (((1600 * x1 ^ 5) + (-1916 * x0)) + ((5590 * x0 * x1) + ((1652 * x0 * x1 ^ 2) + (-13560 * x0 * x1 ^ 3))))) + ((((10000 * x0 * x1 ^ 4) + (-2000 * x0 * x1 ^ 5)) + ((1989 * x0 ^ 2) + ((7736 * x0 ^ 2 * x1) + (4944 * x0 ^ 3)))) + (((-2496 * x0 ^ 3 * x1) + ((-5952 * x0 ^ 4) + (-4928 * x0 ^ 4 * x1))) + ((-2912 * x0 ^ 5) + ((80 * x0 ^ 5 * x1) + (1520 * x0 ^ 6)))))) : ℂ) = 0 := by
    linear_combination ((((-20 * x1) + (36))) * h7 + ((((2000 * x0 ^ 4) + (1200 * x0 ^ 3)) + ((-3440 * x0 ^ 2) + ((160 * x0) + (-1305))))) * h0)
  have h9 : ((((((-152) + (584 * x1)) + ((1214 * x1 ^ 2) + ((-1220 * x1 ^ 3) + (-820 * x1 ^ 4)))) + (((988 * x1 ^ 5) + ((-320 * x1 ^ 6) + (892 * x0))) + ((200 * x0 * x1) + ((-2185 * x0 * x1 ^ 2) + (1596 * x0 * x1 ^ 3))))) + ((((1188 * x0 * x1 ^ 4) + (-1680 * x0 * x1 ^ 5)) + ((400 * x0 * x1 ^ 6) + ((-1350 * x0 ^ 2) + (-2714 * x0 ^ 2 * x1)))) + (((-697 * x0 ^ 3) + ((-320 * x0 ^ 3 * x1) + (1632 * x0 ^ 4))) + ((2236 * x0 ^ 4 * x1) + ((680 * x0 ^ 5) + (1040 * x0 ^ 5 * x1)))))) : ℂ) = 0 := by
    linear_combination (((((-1 / 5 : ℂ) * x1) + ((-4 / 25 : ℂ)))) * h8 + ((((19 / 25 : ℂ))) * h7 + ((((4 * x0 ^ 3) + ((-1252 / 5 : ℂ) * x0 ^ 2)) + (((653 / 5 : ℂ) * x0) + ((-284 / 5 : ℂ))))) * h0))
  have h10 : ((((((12548) + (23684 * x1)) + ((2299 * x1 ^ 2) + ((-7520 * x1 ^ 3) + (-10000 * x1 ^ 4)))) + (((-1232 * x1 ^ 5) + (-1520 * x1 ^ 6)) + ((11052 * x0) + ((10410 * x0 * x1) + (-10680 * x0 * x1 ^ 2))))) + ((((1136 * x0 * x1 ^ 3) + (2608 * x0 * x1 ^ 4)) + ((-7120 * x0 * x1 ^ 5) + ((-72805 * x0 ^ 2) + (-126364 * x0 ^ 2 * x1)))) + (((-23692 * x0 ^ 3) + ((-21080 * x0 ^ 3 * x1) + (70972 * x0 ^ 4))) + ((113536 * x0 ^ 4 * x1) + ((35280 * x0 ^ 5) + (49040 * x0 ^ 5 * x1)))))) : ℂ) = 0 := by
    linear_combination ((((20 * x0) + ((-616 / 19 : ℂ)))) * h9 + ((((((-2000 * x1 ^ 4) + ((5200 / 19 : ℂ) * x0 ^ 3)) + ((6400 * x1 ^ 3) + ((-325520 / 19 : ℂ) * x0 ^ 2))) + (((-2040 * x1 ^ 2) + ((169780 / 19 : ℂ) * x0)) + ((-2020 * x1) + ((46905 / 19 : ℂ)))))) * h0 + ((((-260 / 19 : ℂ) * x1) + ((-170 / 19 : ℂ)))) * h8))
  have h11 : ((((((4627848) + (3219348 * x1)) + ((-8359742 * x1 ^ 2) + ((2236413 * x1 ^ 3) + (703108 * x1 ^ 4)))) + (((-6234076 * x1 ^ 5) + (2293056 * x1 ^ 6)) + ((931760 * x1 ^ 7) + ((2751968 * x0) + (9282496 * x0 * x1))))) + ((((9173608 * x0 * x1 ^ 2) + (-9407540 * x0 * x1 ^ 3)) + ((-10306788 * x0 * x1 ^ 4) + ((7580400 * x0 * x1 ^ 5) + (-7986066 * x0 ^ 2)))) + (((-13167567 * x0 ^ 2 * x1) + ((-13721494 * x0 ^ 3) + (-23442752 * x0 ^ 3 * x1))) + ((-6061576 * x0 ^ 4) + ((-6592880 * x0 ^ 4 * x1) + (352260 * x0 ^ 5)))))) : ℂ) = 0 := by
    linear_combination ((((-613 * x1) + ((6427 / 5 : ℂ)))) * h10 + (((((7515380 * x0 ^ 3) + (9884012 * x0 ^ 2)) + ((-3720297 * x0) + (-3289971)))) * h0 + (((-54557 / 5 : ℂ))) * h9))
  have h12 : ((((((3399411468520413348) + (208599803952808484 * x1)) + ((-7732630425449873421 * x1 ^ 2) + ((4720969609562864120 * x1 ^ 3) + (1847208827671364240 * x1 ^ 4)))) + (((-1574355968608663352 * x1 ^ 5) + (-22945361716708720 * x1 ^ 6)) + ((-4907663644835135988 * x0) + ((-1024478839995209030 * x0 * x1) + (12607588723086961840 * x0 * x1 ^ 2))))) + ((((-6734911920760959464 * x0 * x1 ^ 3) + (-3413707723013973512 * x0 * x1 ^ 4)) + ((2055916863044595680 * x0 * x1 ^ 5) + ((-2135241084332817805 * x0 ^ 2) + (-260183577172666324 * x0 ^ 2 * x1)))) + (((1127185207613789228 * x0 ^ 3) + (-1018596651564398800 * x0 ^ 3 * x1)) + ((-757324730209240308 * x0 ^ 4) + ((1088676012358496296 * x0 ^ 4 * x1) + (452862805494079880 * x0 ^ 5)))))) : ℂ) = 0 := by
    linear_combination (((((-303569737400000 / 3 : ℂ))) * h5 + (((((((13660638183000000 * x0 ^ 8 * x1) + ((5160685535800000 / 3 : ℂ) * x0 ^ 7 * x1 ^ 2)) + ((-48874727721400000 * x0 ^ 6 * x1 ^ 3) + ((-91374490957400000 / 3 : ℂ) * x0 ^ 5 * x1 ^ 4))) + (((13660638183000000 * x0 ^ 8) + (-31571252689600000 * x0 ^ 7 * x1)) + (((-210070258280800000 / 3 : ℂ) * x0 ^ 6 * x1 ^ 2) + (((168784773994400000 / 3 : ℂ) * x0 ^ 5 * x1 ^ 3) + ((194588201673400000 / 3 : ℂ) * x0 ^ 4 * x1 ^ 4))))) + ((((-34023776620700000 * x0 ^ 7) + ((-273516333397400000 / 3 : ℂ) * x0 ^ 6 * x1)) + (((180016854278200000 / 3 : ℂ) * x0 ^ 5 * x1 ^ 2) + ((-18897216153150000 * x0 ^ 4 * x1 ^ 3) + ((-121755430729300000 / 3 : ℂ) * x0 ^ 3 * x1 ^ 4)))) + (((-75479966327300000 * x0 ^ 6) + ((215989868160100000 / 3 : ℂ) * x0 ^ 5 * x1)) + (((205061357613700000 / 3 : ℂ) * x0 ^ 4 * x1 ^ 2) + ((-46410220774350000 * x0 ^ 3 * x1 ^ 3) + ((240759813270500000 / 3 : ℂ) * x0 ^ 2 * x1 ^ 4)))))) + (((((119882816169350000 * x0 ^ 5) + ((537565085609637500 / 3 : ℂ) * x0 ^ 4 * x1)) + ((56282228747825000 * x0 ^ 3 * x1 ^ 2) + (((-215988711904175000 / 3 : ℂ) * x0 ^ 2 * x1 ^ 3) + ((-844477932320750000 / 3 : ℂ) * x0 * x1 ^ 4)))) + (((-50241811205432500 * x0 ^ 4) + ((-144875661420162500 / 3 : ℂ) * x0 ^ 3 * x1)) + (((-300974047962550000 / 3 : ℂ) * x0 ^ 2 * x1 ^ 2) + (((1761693092332850000 / 3 : ℂ) * x0 * x1 ^ 3) + (369749833664225000 * x1 ^ 4))))) + (((((-810621975322064750 / 3 : ℂ) * x0 ^ 3) + (-60342678958191250 * x0 ^ 2 * x1)) + ((-96904580344867500 * x0 * x1 ^ 2) + ((-631674366649602500 * x1 ^ 3) + ((-3194061085016042780 / 3 : ℂ) * x0 ^ 2)))) + ((((-265242974492075500 / 3 : ℂ) * x0 * x1) + (219129567272100750 * x1 ^ 2)) + (((2170697208124022245 / 3 : ℂ) * x0) + ((51809301189297025 * x1) + (127310587005336630)))))))) * h0) + ((((((80885357662500 * x0 ^ 4 * x1) + (44936309812500 * x0 ^ 4)) + ((49077808307500 * x0 ^ 3 * x1) + ((10117239343750 * x0 ^ 3) + (-272125606474250 * x0 ^ 2 * x1)))) + (((-178431035446250 * x0 ^ 2) + (-246069260113800 * x0 * x1)) + ((-141555018880875 * x0) + ((-965365039008705 * x1) + ((-1441484743455675 / 2 : ℂ))))))) * h8 + (((-11058957517348200)) * h9 + (((221682284911947 / 2 : ℂ))) * h10)))
  have h13 : ((((((25777218197636225455829742085308) + (-45358149484119887409847862900036 * x1)) + ((-79369871652694692510874626299691 * x1 ^ 2) + (103883396608691982333764116205760 * x1 ^ 3))) + (((-29871318865559717881918285614760 * x1 ^ 4) + (3059518782163088956061851145968 * x1 ^ 5)) + ((541577191984580438975734807280 * x1 ^ 6) + ((-64281137817497502299871033483788 * x0) + (20388805904138076440387792655830 * x0 * x1))))) + ((((154340019947958652637368158377920 * x0 * x1 ^ 2) + (-146087582093181908359982244883344 * x0 * x1 ^ 3)) + ((50939739863057328702999994766368 * x0 * x1 ^ 4) + (9260140427391451891135784503765 * x0 ^ 2))) + (((79663883583029816181488602756396 * x0 ^ 2 * x1) + (47047094193171599889956261553428 * x0 ^ 3)) + ((17210250489330617583352864606520 * x0 ^ 3 * x1) + ((-8507475608850255834584460210308 * x0 ^ 4) + (14165618635030242847350360418976 * x0 ^ 4 * x1)))))) : ℂ) = 0 := by
    linear_combination ((((((388934475083290205578 / 1997169325 : ℂ) * x1) + (((-44593944203465327753329923 / 948655429375 : ℂ)) + ((-322133173851781033871476 / 9985846625 : ℂ) * x0)))) * h12 + ((((-142369336558702541484916814437295774824 / 49929233125 : ℂ))) * h9 + (((5871211983476531997084368609437658 / 1224264796225 : ℂ))) * h11)) + ((((441456455203126432476587178757324096899737 / 581525778206875 : ℂ))) * h10 + ((((((-105855908350605329387845256282197884772 / 1997169325 : ℂ) * x0 ^ 2) + (((204897746850054454507468059121692011372 / 1997169325 : ℂ) * x0) + ((432317022189568747140613304457657025041531 / 9985846625 : ℂ)))) + (((33113951213397651902921003875819475241184 / 1997169325 : ℂ) * x1 ^ 3) + (((-109347369787218716585994520397733492880008 / 9985846625 : ℂ) * x1 ^ 2) + ((-444769812865214063583187639017392828084824 / 9985846625 : ℂ) * x1))))) * h0 + (((1823526660665371664069296773145934968786 / 189731085875 : ℂ))) * h8)))
  have h14 : ((((((137143428087002226204875742888) + (-19866361915865178539501273012 * x1)) + ((-266623472221092294492003802142 * x1 ^ 2) + (246670430607775480934823608963 * x1 ^ 3))) + (((-71100076020747183783447184120 * x1 ^ 4) + (895554765282785326260777950 * x1 ^ 5)) + ((-221655374545634286695544954644 * x0) + ((-48017536420545198915639486300 * x0 * x1) + (448297875258287439880145546713 * x0 * x1 ^ 2))))) + ((((-366783727351996874338248635140 * x0 * x1 ^ 3) + (103211298586657285432447292030 * x0 * x1 ^ 4)) + ((-63533179374925819135927035334 * x0 ^ 2) + (76097864946800952238067892829 * x0 ^ 2 * x1))) + (((76259432926058101448789636711 * x0 ^ 3) + (-14422258576233871919522874284 * x0 ^ 3 * x1)) + ((-27966794732010647762032974128 * x0 ^ 4) + ((43357330076753666826872080118 * x0 ^ 4 * x1) + (13539429799614510974393370182 * x0 ^ 5)))))) : ℂ) = 0 := by
    linear_combination ((((((-888793025194609850079 / 39943386500 : ℂ) * x0) + (((-2904927245592773067861 / 1897310858750 : ℂ)) + ((-534705024177887220301 / 39943386500 : ℂ) * x1)))) * h12 + ((((((22841057103175232210264109259699638234 / 1997169325 : ℂ) * x1 ^ 3) + (((-150849380751721775796062362802053256091 / 19971693250 : ℂ) * x1 ^ 2) + ((-613579009521078081055948353166462302873 / 19971693250 : ℂ) * x1))) + (((812963689949137988470617253328903916651 / 19971693250 : ℂ)) + (((72765066688754451025427641649455563137 / 19971693250 : ℂ) * x0 ^ 2) + ((-140846160089036554132211184852483067987 / 19971693250 : ℂ) * x0))))) * h0 + (((2697288496269021130963190118117802277 / 39943386500 : ℂ))) * h9)) + ((((10062532572330035970509880574221257763 / 1517848687000 : ℂ))) * h8 + ((((-3839445547021643142006535321310267841253 / 4652206225655000 : ℂ))) * h10 + (((-8071710652304673646839194491636661 / 24485295924500 : ℂ))) * h11)))
  have h15 : ((((((140601936526081804492795697403864123457973433973726856362542596724673838418476706396) + (49891673469343987587298729412433738994947609390171674943247707441787441394740302064 * x1)) + ((-260074248202818288888721055922360151674379725256176864286116339049154019452691577367 * x1 ^ 2) + (97684204492764326599091898165104000309877803442083212035805698671008657666356759077 * x1 ^ 3))) + (((17026293550952807262994214001649058262683069895708235689851491521018469992797229582 * x1 ^ 4) + (3739221926194498781810485819151531412581754008823213740886985542913789908094769270 * x1 ^ 5)) + ((-363386653712031056578059496347470982866184287981963319613914714722949675790894695804 * x0) + (-344687191484787494640420265561901982234781498041393717749665716507395555149934492398 * x0 * x1)))) + ((((484244156552831504677636959312947539964742332468732797390858686628957498445367442832 * x0 * x1 ^ 2) + (-84617534046780102523716057169544867993741878381044332788877674582509567140201742908 * x0 * x1 ^ 3)) + ((38934028450371860115038754860946995871994852090418853838062483247863506581643548725 * x0 ^ 2) + (253159705933843540939370144794114679300466037899938461169612729883357057365674679813 * x0 ^ 2 * x1))) + (((279878081055151407026183309406175861506733406245423870371722164090145333772298993926 * x0 ^ 3) + (243636139787947896205813226048761377518544398324808392155849491685947256222665844808 * x0 ^ 3 * x1)) + ((18445340457873920552364990377078624829722825172420116375508464876314176810780408562 * x0 ^ 4) + (128335232203016936397956345133024943532603275415858068091190243172475650440586815806 * x0 ^ 4 * x1))))) : ℂ) = 0 := by
    linear_combination ((((((-94357458505798062264295090596660166447568542539279930403 / 20 : ℂ) * x1) + (((21607908936916811318362301668145782382022672899543853263251885477129685141650026697908041189589593732 / 1304809783173561754241248303469330343598031895 : ℂ)) + ((119229190530037445533117976581399471697876473611382604353 / 12 : ℂ) * x0)))) * h14 + ((((-68367838527710416774586912873215357090160705005916454369152787850277807092355154885863 / 9317600 : ℂ))) * h10 + (((((2045543736819737215869010492098658375874657385075666952539849500745536586109440013777 / 40 : ℂ) * x0 ^ 2) + ((-2725967569403176120447741893577103421965249059757340391724668321520879380530459242003 / 40 : ℂ) * x0)) + (((-11149665652805572780189990845873430901538221460924181555278985029073068658489000234573 / 20 : ℂ)) + (((-6152899792020573001368613835268912775842489453471628423770375637324161720851870103295 / 24 : ℂ) * x1 ^ 2) + ((15712763663863698057955990303460780954010118950008824981146477770976430885518566278915 / 24 : ℂ) * x1))))) * h0)) + ((((21732493932656094000618598516824922881634062882789137030673990304048620695476247889644981 / 179589477779103044137200 : ℂ))) * h12 + ((((-80011382971166958644039694618297094744145583205837464098677223211266040536521166351487826638159959 / 10438478265388494033929986427754642748784255160 : ℂ))) * h13 + (((-807147627623152620342841534399162969845604268473217566247174427086323221083986801123 / 9120 : ℂ))) * h8)))
  have h16 : ((((((169362721548654307085113257646007085222006014954610178737611235259931849603414038556) + (-151903385336554991297230343681047003960163679975874521829825179555908342605470297720 * x1)) + ((-383780885889178618234869684710459197996367609029254523327457338660503860277338151391 * x1 ^ 2) + (524767467782199550637131961090514421983405717764746236482717464716641661252165808015 * x1 ^ 3))) + (((-180083142318983024791932846224219015513857591569974194547264084866628350198895030960 * x1 ^ 4) + (1733168304664155974129440435268931592596249432219784052351501052442610545002947780 * x1 ^ 5)) + ((-235691532332493888645673609142280218931565408485598527175018664783263351476127691000 * x0) + (184944743798304547834062322556923081008061147417629710962184298561362605035379508742 * x0 * x1)))) + ((((658288609797278658442320838152575866467071450305568765504800485884619259171758164087 * x0 * x1 ^ 2) + (-804125094722494661253499371582863881329435307316419806526000879788455912989832885016 * x0 * x1 ^ 3)) + ((256670464406033872795912690266049887065206550831716136182380486344951300881173631612 * x0 * x1 ^ 4) + (-110511684063910574659747750040186717162797861306718648708027568623082764963037746087 * x0 ^ 2))) + (((111591087445221574576908347305715888201301697958274732071764400966352045007583475593 * x0 ^ 2 * x1) + (61858092426081364120162735704887658689037693927176208394874865025729455958648512801 * x0 ^ 3)) + ((-126576431449369619726808177332933781405602085996667218866091936545199795610346770144 * x0 ^ 3 * x1) + (-71381070101487515459694945384009651053953183989509947847159525622078128125529217980 * x0 ^ 4))))) : ℂ) = 0 := by
    linear_combination ((((((-10619300694265254745578012993220953330502819364766766621 / 3 : ℂ) * x0) + (((-12319966827502941449031621697377076576682785704780343792339935617742921947983697801423088305215123331 / 1304809783173561754241248303469330343598031895 : ℂ)) + ((1117321105783882596597133804006438929285792115096822589 / 5 : ℂ) * x1)))) * h14 + ((((71889638135501027664807123377252038543595709127757466644334113211566413113627147511 / 2280 : ℂ))) * h8 + (((7026523960295975910804969791411141138223403555098516201259513202756539183193018899669 / 2329400 : ℂ))) * h10)) + ((((((548015907368654108540161864326335508789832600654080579413466927339058501395221665315 / 6 : ℂ) * x1 ^ 2) + ((-1399477437888475048573290004744469359518275639147910394619713091027873182596858165655 / 6 : ℂ) * x1)) + (((5342685538210619146006547854231021612864179423634035653985866551774257273647670364981 / 20 : ℂ)) + (((-24222029992597599156943613648077281469240762714514252607289041485396919569420092751 / 10 : ℂ) * x0 ^ 2) + ((32279176942746956163485242906663820184836170625453635228533327094019957065869293389 / 10 : ℂ) * x0))))) * h0 + ((((705854595495994940867831207254720562948744817154446225773319434259819906120669031190111 / 22448684722387880517150 : ℂ))) * h12 + (((49210503004655260806174513367200984304885929478773404920532977431090257855057266266724651521074809 / 5219239132694247016964993213877321374392127580 : ℂ))) * h13)))
  have h17 : (((((477758828393764801584695755799666322459509741928402676156773181878241745741027446933222471983277594923132774005252) + ((405106070644751762238753058107039153924892444950915184049783565948245028836832886839801257075070633057524769682730 * x1) + (-954233347737488180383309726044773729897439038610974140065675842517416392840064020105733285823856621776893883550183 * x1 ^ 2))) + ((573484397946164017177313271746030123098751727416066828384315509441036099049079339230219330972577263373754144940566 * x1 ^ 3) + ((337330103802098389595319888936744490177507375773432801389779376836841917737306581806033228502879946213137327680852 * x1 ^ 4) + (70214362295833205994687933431460916141001183077484937383496902520699914001860432563594621740198824354997723162200 * x1 ^ 5)))) + (((-620625948438611046925326386923754407135128221983375105647259700328938376647082439590238308631683381143738501489974 * x0) + ((-613180539432168534650653287292304072304735103691707571704533231032210573558432437009161806010269969983774610248688 * x0 * x1) + (2052454925939606941807769680135834110984862671732699034083438763836226842865184202689268402457647797755860093024480 * x0 * x1 ^ 2))) + ((3722704503221256137336549815725167415196559145833766971363234648363901544325001290538251310706705579981945620643 * x0 ^ 2) + ((-72113450770755548483312403135048423371463617602298180429939099153266451221533152012001576491014856069593560800876 * x0 ^ 2 * x1) + (-525351959680835663949689366494058850197553894984640096432019087271273789553722689041011082269331376250436237712086 * x0 ^ 3))))) : ℂ) = 0 := by
    linear_combination ((((((11251425050695747621154664794402625166514548017200660117588090905900312250048134300851027243567045414968202750319350470477667817989607128752957320936224609807982584672770744321376899240268370267063168853110861637881 / 3328061125948752647193088097223057968969415545488880042430068410403934774755363552512240417255975365304920797017444000445814789798160811481157402315541581441033209574972307690088000 : ℂ) * x1) + (((-141857002492443558767723618508196603951244331337168927272041744185714393711240989841226818933537790105673276246927970121769064262519042185506058621951802515950267947607299402148956754193916398415266751594293958915104400635865895581976371604640349054971183345781538010699 / 25420307646674886227700852784927807399008921867997376561334949866299325108301320905724344302474570845626943857452752029052595837347933988077831443132477275416775262607154388645384449204637600859424830550713581644401125140886031429788000 : ℂ)) + ((332526636465235297305199677905064333580051656554175008009302764012483748584673019307037982553981304613209208884711319013853838729310062553143277304514752524874425511990344907323666057868673947287952905885655843507 / 221870741729916843146205873148203864597961036365925336162004560693595651650357570167482694483731691020328053134496266696387652653210720765410493487702772096068880638331487179339200 : ℂ) * x0)))) * h16 + ((((15471761251407978221827244193814757168666079456871472422484583708057020499723546681197159928977189792675622101744827220280737550779562760920024921126884095786952242838142941861631683378969292369228312640631085632341567769916167788134705103751 / 45116077547777951351811495263525573631740840033625721421649745765975230425385614035583655008937628811867173948920204107648584894167343175280000 : ℂ))) * h12 + (((4125166214787807372614824903174352640283674678745140201213957691286430885845188931546989766472017375274207564630894663310465934224528429084903809491376618752333733932801691533867532003497315509451701126920091036980815624278810840385869368832791382656980821 / 203615321597367988514193590552915778155265100881473076138323680535916667076791634293362512930622067259725639209149560620870156328950973208794881524738208015345450500320000 : ℂ))) * h13)) + (((((-22032591325175891713280343178934366810054373100083387524767856101963458850329508711737710137576124114083005638004849201738853017452350300242044521523917949195084172770781812170358514623482040316260951581571235279799982290961713160182806326336184934242840343 / 3817787279950649784641129822867170840411220641527620177593569010048437507689843143000547117449163761119855735171554261641315431167830747664904028588841400287727196881000 : ℂ)) + ((-17932735040604018834854781224011312066523923937010189990204442270613172497751986158570417306414550752662203415261528039518701838567912250125788236687262125636947184391567070293923924175253442088523976691076670239 / 1170373591364411022523437698319890302035671907865153933918180954283845123881303444637532813541945449420976746034198378715120 : ℂ) * x1))) * h14 + (((((-32080579547849077867466063124929701954938002022526879989005821585609615650635456429955274195069907947451852047685834127647350530710766863218640529046977782725441380121746702066703093167764336104840350836937078842229247891006332248547045897773083415684270318668942092591 / 12710153823337443113850426392463903699504460933998688280667474933149662554150660452862172151237285422813471928726376014526297918673966994038915721566238637708387631303577194322692224602318800429712415275356790822200562570443015714894000 : ℂ)) + (((1058928894316594411136349632419966877793302526886810400660042080060907466684346840867985305824357350904212298241165097563932948036405888642414205085715439800387687823647416213768877707521323436009162382034783758203 / 832015281487188161798272024305764492242353886372220010607517102600983693688840888128060104313993841326230199254361000111453697449540202870289350578885395360258302393743076922522000 : ℂ) * x1) + ((17932735040604018834854781224011312066523923937010189990204442270613172497751986158570417306414550752662203415261528039518701838567912250125788236687262125636947184391567070293923924175253442088523976691076670239 / 11093537086495842157310293657410193229898051818296266808100228034679782582517878508374134724186584551016402656724813334819382632660536038270524674385138604803444031916574358966960 : ℂ) * x0)))) * h15 + (((((-1325738822233983919560287982190618575032558069645494312124430066030782809986982729626440000614940383956358631853935783786567380016253555220959324488554945829891462902690956013820316915131153616876006080966603240188539758238169358612389145957 / 8777801935233082668925782737399177265267539308988654504386357157128838429109775834781496101564590870657325595256487840363400 : ℂ) * x0) + ((47275601791488071641859133345140579698914740815104792331997824148444447505776751221833113077731162108629482211438805011026135194148803067847677280341125018395838777135321298677755490922993601180621927635400836328219866614667430935930491250859 / 468149436545764409009375079327956120814268763146061573567272381713538049552521377855013125416778179768390698413679351486048000 : ℂ))) + (((-332526636465235297305199677905064333580051656554175008009302764012483748584673019307037982553981304613209208884711319013853838729310062553143277304514752524874425511990344907323666057868673947287952905885655843507 / 3457674684048314689423331873222757633466849771010986089046662973113587280570722757721167566926400 : ℂ) * x1 ^ 2) + (((827487976401785496901299459361288760353076455643602770725482651400538834769765454350187591162317129040557123748901135136052708165450589833276401115246278364577929786678220441841499739327132547980912736688756029639 / 3457674684048314689423331873222757633466849771010986089046662973113587280570722757721167566926400 : ℂ) * x1) + ((10994092499424920638565519135685811626519863864319650871798964283761876984276715504854036633886759334871484497307107984871240183769453257868850820304018118425049642684993839705553636513126884558065266864818855172540549759650289082178401878051 / 87778019352330826689257827373991772652675393089886545043863571571288384291097758347814961015645908706573255952564878403634000 : ℂ) * x0 ^ 2))))) * h0)))
  have h18 : (((((3510933424629085785380328210931217547669811564706975458526585962178051838832651935192010454020973706709219500972) + ((8728775929434401271447845240579788186658353684079883373324821734546646936336469609388824264900058495894253146250 * x1) + (1897727813077254979611137802482316103398881423538746700353355104652224469724166783305814443010421918633202882907 * x1 ^ 2))) + ((-553289544454139575945866764769214660834134202792155305981858400338161011482062597305904150283055767066885129434 * x1 ^ 3) + ((215309837425485645931539358171740619752410832728589351740836143056138739630307012279367011032488959333342862 * x1 ^ 4) + (1706909080176229700687188818717353091318730554665932456271649810190543258671165739004803356858111082475814144306 * x0)))) + (((-4932459063930189369641843478182469017381581193671475615211148180669973441929614814728077910835084702790514008988 * x0 * x1) + ((-6293960718889995060541028345592782665083399181940866080315865945575596929036806239305672353462222135991140923450 * x0 * x1 ^ 2) + (-10341120301636530134633309491596002668450274181917197774091089247500249750486433533225902807866480328132936392867 * x0 ^ 2))) + ((-19657689973201674607276027794890396496801759082916063973417941769255582314922415524131573989019465422513212976296 * x0 ^ 2 * x1) + ((-6895151949507647551920209792204393397212870974353402282030762299662042719702368011747784877798351640170518180336 * x0 ^ 3) + (3510718114791660299734396671573045807050059153874246869174845126034995700093021628179731087009941217749886158110 * x0 ^ 4))))) : ℂ) = 0 := by
    linear_combination ((((((1150147038679344984470682107294690495248821654315208211005659021074383362450773160408125963319909491004855308921670688702913159390048492607057684735557340503686781565558232401822769478226455515121223378795620141 / 315290001405671303418292556579026544428681472730525477703901217827741189187350231290633302687408192502571443927968378989603506401931024245583332850946044557571567222892113360113600 : ℂ) * x0) + (((-271781899263611171515026163137269151103624844364953119349030286671054724632277342756604994325996091505201873981671418684232745215316241840183460096672792482113430701539425135511077374773036153997496363631010012531099863486353272753904416617764895594056566234995148481 / 18061797538426892845997974347185547362453707643050767556737990694475836261161464854067297267547721390313881161874323810116318094957742570476353920120444379901392949747188644563825792855926716400117642759717544852600799442208496015902000 : ℂ)) + ((4387259876367366443428791127017364534551950163363556270187670523674002885835242189093220097047417639584152306462605599264618260344918917210519237951484097909281626231143543444129304847159441332181766785172980467 / 525483335676118839030487594298377574047802454550875796173168696379568648645583718817722171145680320837619073213280631649339177336551707075972221418243407595952612038153522266856000 : ℂ) * x1)))) * h16 + ((((((-1150147038679344984470682107294690495248821654315208211005659021074383362450773160408125963319909491004855308921670688702913159390048492607057684735557340503686781565558232401822769478226455515121223378795620141 / 4913537708910762979706840030369181900189733885120874968645257909161413503968921813603764437211200 : ℂ) * x1 ^ 2) + ((2883482190754134949534080771026074649929357989577125191520260346427563318268627175218123456358013906486020846061112443926591297613562653217441438348148539450414611208127765096185802601706949912401408604592951257 / 4913537708910762979706840030369181900189733885120874968645257909161413503968921813603764437211200 : ℂ) * x1)) + (((209095428909318099205475201162129265299488599787977633958735886196240145952926375200561476169653491990179707406511299450453358724775249908256739125370564363214901606373493081944697381047083717276058153808223888696643634962337378714414938417 / 665264988775559949644901428518674487472908242365455920332439700329764596732530379057123915065947939670870992482596973164384000 : ℂ)) + (((-811101719034119681121673562495906953689198179482939277912472598496702257398902752805549354466021615977747864174333126784187869290419548442464393178441453314241339079840317699320567783514752410801472986735512037924367746631695991071734511 / 2078953089923624842640316964120857773352838257392049751038874063530514364789157434553512234581087311471471851508115541138700 : ℂ) * x0) + ((13636038100587759243995806082827774957239432624850503028942025499863808547915702293243482381553829727278111541001709112423332263912479341033719486226663239494286697773756042785828934794437632841408024923274747983620805695092511199958414721 / 41579061798472496852806339282417155467056765147840995020777481270610287295783148691070244691621746229429437030162310822774000 : ℂ) * x0 ^ 2))))) * h0 + (((9799285961166775847441747129687951850279647765071595690988288689921490862038357176188568269279924315913862881134586098527060183717000848538705180576816345800955964973747183945444681260477289623961352282862205655752877173259944045224989773 / 10685386787631620057007985720308688491728093692174512968285466102467817732328171745269813028432596297547488566849522025495717474934370752040000 : ℂ))) * h12)) + ((((16222583660164066087772638563544054233907464893616965999813786781029469263821318731940572359938543393599999141803663276015926878579540338593281471080735904723873786994223195813510688434950240741821479877777356675340906854720951142975729672578546384833673 / 289348088585733457362275102364669790010113564410514371354459967077355263740703901364251992059305042948031171507738849303341801099035593507234831640417453495490903342560000 : ℂ))) * h13 + (((((-41188804602282517249646033099187960795855952780630739511708368115877991965280141071291683200359688668967546458584673320404189094172080218844224787875055603050381306468091106943782231546908125139836857625922203769426504947485927084341246701949322395280829 / 2411234071547778811352292519705581583417613036754286427953833058977960531172532511368766600494208691233593095897823744194515009158629945893623597003478779129090861188000 : ℂ)) + ((-65265073239168548861382180805286429949651320802759231916032702699944661178895873838378664309997435134350574831430788135582963115836044585891809313532436191328385652179752259477511524569902562421517713042335377 / 1663162471938899874112253571296686218682270605913639800831099250824411491831325947642809787664869849177177481206492432910960 : ℂ) * x1))) * h14 + ((((-118863615109248824698380066009379369133603041255696797337392954090442307873329715332775618070832805296216855072872994837684718802184331817801752564451998567938893801871688253269993406504623086247104409195142193568537299428848274051483759407233877541597850522133354183 / 18061797538426892845997974347185547362453707643050767556737990694475836261161464854067297267547721390313881161874323810116318094957742570476353920120444379901392949747188644563825792855926716400117642759717544852600799442208496015902000 : ℂ)) + (((398806323709031036725030737785966063714918761590167056631865896669021239803168913505980982257154656095223398152297833871852699843230268920819872900137473714786328607489497312152553204129123533126891239034733321 / 131370833919029709757621898574594393511950613637718949043292174094892162161395929704430542786420080209404768303320157912334794334137926768993055354560851898988153009538380566714000 : ℂ) * x1) + ((65265073239168548861382180805286429949651320802759231916032702699944661178895873838378664309997435134350574831430788135582963115836044585891809313532436191328385652179752259477511524569902562421517713042335377 / 15764500070283565170914627828951327221434073636526273885195060891387059459367511564531665134370409625128572196398418949480175320096551212279166642547302227878578361144605668005680 : ℂ) * x0)))) * h15)))
  have h19 : (((((-204254699923110313401425209885875282856642221732518116800911648248253021513334014098618368255742919432209590334052) + ((-355801152850479211095388440541675955280433943095671546293334442211622304045273535300003915066345086129164021614405 * x1) + (32081208131077459393627954847346953850880838239106074936499269684691396659043033886844644296534329909417443706258 * x1 ^ 2))) + ((43436291547110583075983746030371083268133647231226977549768829872493429776887137772441041193037958049137787704309 * x1 ^ 3) + ((6388386964389304582638590408507465566361327499936695349579059313846720492247283592165496964853553632783579152548 * x1 ^ 4) + (52708246995741415707461979230074610432850500369364687308488854284883738981394492897232821445140752735255159053699 * x0)))) + (((234874030082691730229134911576016976824637380341175665414158511274292237326767439751571326298231487414140056150513 * x0 * x1) + ((139377711394937449885420644859869826604841845431837560982960959880260858752067716238766884252938602024672903363495 * x0 * x1 ^ 2) + (407047521874724584236932166614545305830398763834587707278570889837853862181058419963345050257440076936932202778307 * x0 ^ 2))) + ((689337240028964761291787930830655244843274931498373766362124342661376592255339717782336437354290674564955318104876 * x0 ^ 2 * x1) + ((184886420334917267679500612229405935793282289832726949327108916157103120253491111118773857782904191725001021777586 * x0 ^ 3) + (210643086887499617984063800294382748423003549232454812150490707562099742005581297690783865220596473064993169486600 * x0 ^ 3 * x1))))) : ℂ) = 0 := by
    linear_combination ((((((-184287637877191526842956400499386590328148598658282999662996558574664811182898450883877834141428470704197878818148544574434655400931922557080927743199096008198123622944173658195088738860040459865750861385217967913 / 4992091688923128970789632145834586953454123318233320063645102615605902162133045328768360625883963047957381195526166000668722184697241217221736103473312372161549814362458461535132000 : ℂ) * x1) + (((69929912514766076595891981223687505726063334953522246566211687175336817913602866583827394592394628291976444964446783985612044362356509845317432445037065243497446215754915972370135374053283375566788084570075969820512296615435670328799263294150087271027938893790829351399 / 686348306460221928147923025193050799773240890435929167156043646390081777924135664454557296166813412831927484151224304784420087608394217678101448964576886436252932090393168493425380128525215223204470424869266704398830378803922848604276000 : ℂ)) + ((-35072441926679967479112844174786249105058545306818463539624595411526489206731183566498866941935493744999192760929927244437281570369327297105520651283907111464440232634854268292394584292469261934453489290347917361 / 599051002670775476494755857500150434414494798187998407637412313872708259455965439452203275106075565754885743463139920080246662163668946066608332416797484659385977723495015384215840 : ℂ) * x0)))) * h15 + ((((((-7632684355598974352498560496712276702477729314131557901891295743872030856367996383069756602285283507625463342317881616925888331585355517322113800626576313849031345746744941974075612616267958021642725363279678373857561824172875707813014326113 / 1580004348341954880406640892731851907748157075617957810789544288283190917239759650260669298281626356718318607146167811265412000 : ℂ) * x0 ^ 2) + ((449520226265157798943989632568477988763330592968574252818205711536549027925751412305195515418291652694231095506917778745938236837025800240158027073958681615107589295715081709554890886763549021721625777409229249844726474838865357874775062983 / 79000217417097744020332044636592595387407853780897890539477214414159545861987982513033464914081317835915930357308390563270600 : ℂ) * x0)) + (((-144876921681043608428032058906120216002437583593932188686935350087531696671778857123544176115228137388065186373007459344763559961411275909064740023791382484890225920475907806271689964355663392151265664084376731913919775146205410012422258922401 / 25280069573471278086506254283709630523970513209887324972632708612531054675836154404170708772506021707493097714338684980246592000 : ℂ)) + (((597383507185555776810032118262567439542875667746787566693374413830150732369868052729746698186579877407036382498370853043643066972452604322017568749620419939345097469382254437835030796685625738764259525973879608573 / 186714432938608993228859921154028912207209887634593248808519800548133713150819028916943048614025600 : ℂ) * x1 ^ 2) + ((-1505413717757807437241786943927560447753303812482682942582879335530695644734949981823967527976112620717979084224352753068512039904253835822068036910363460765477793566568186785178204113799189889424741719862006263721 / 186714432938608993228859921154028912207209887634593248808519800548133713150819028916943048614025600 : ℂ) * x1))))) * h0 + (((-10196000494016665831882539969849996622919459390265035634681227259110128056121790057996526351567306704632713346938961340527931081879560995629412274349893262889316982623496270207415051534910121859199643068265411502784612680661588484040690989886329908196615369 / 10995227366257871379766453889857452020384315447599546111469478748939500022146748251841575698253591632025184517294076273526988441763352553274923602335863232828654327017280000 : ℂ))) * h13)) + (((((163651503803514567085749155525596294960711911762548647177951960734178949559617585667900241021262589663902281295563003909707810713640299233826484515147697316804603650569784948203809637129260436758389259489812411523955908680746778513284411265742974413588093906248468857893 / 686348306460221928147923025193050799773240890435929167156043646390081777924135664454557296166813412831927484151224304784420087608394217678101448964576886436252932090393168493425380128525215223204470424869266704398830378803922848604276000 : ℂ)) + (((-2139239673212331030489412325148123796822300580638084896833772529474629829063168263853573492267905325369555151375846686219597967279946785426719605871520011823514471074502488833110082904441283654982391769918446810051 / 19968366755692515883158528583338347813816493272933280254580410462423608648532181315073442503535852191829524782104664002674888738788964868886944413893249488646199257449833846140528000 : ℂ) * x1) + ((-597383507185555776810032118262567439542875667746787566693374413830150732369868052729746698186579877407036382498370853043643066972452604322017568749620419939345097469382254437835030796685625738764259525973879608573 / 11981020053415509529895117150003008688289895963759968152748246277454165189119308789044065502121511315097714869262798401604933243273378921332166648335949693187719554469900307684316800 : ℂ) * x0)))) * h16 + ((((-5821030789451180415184898674800600602423814418043665749140963197615502057248402742806407822189965475725248734380279406190272490724396833082324555749204938815825527536784206781727455195106737197571868445866785117983035826178281623820120496169 / 406044697930001562166303457371730162685667560302631492794847711893777073828470526320252895080438659306804565540281836968837264047506088577520000 : ℂ))) * h12 + ((((27157667785666348875778031498684548619990708672199261388990698050395362855627623720021731899723648084641679892510927413518136868824152133778439419274116666358908099261234004497472846034766145310591029713725333108122148285974084697897016163897780854316278037 / 91626894718815594831387115748812100169869295396662884262245656241162500184556235432013130818779930266876537644117302279391570348027937943957696686132193606905452725144000 : ℂ)) + ((35072441926679967479112844174786249105058545306818463539624595411526489206731183566498866941935493744999192760929927244437281570369327297105520651283907111464440232634854268292394584292469261934453489290347917361 / 63200173933678195216265635709274076309926283024718312431581771531327636689590386010426771931265054268732744285846712450616480 : ℂ) * x1))) * h14)))
  have h20 : (((((-212232102205279438354195276337064563624448171153705261278107613939008974537628982639784705203732369846939805547372) + ((-81402121079797880004869960664633608960911705422459548353015001972166922103065592109812708465079078594567358668355 * x1) + (411392513977374797978344888192981920932218222729921865665342581274155221177103564358561084485887198164646055872738 * x1 ^ 2))) + ((-160168187058593024927826764307237973529032703574567836938253610096391644938546597025904142856350520828201765011401 * x1 ^ 3) + ((-1589015317779820370131476042681815201444621921250449127616906376909232532047684949000839983135896781946636060772 * x1 ^ 4) + (343062083330760996703520592009495518287984636884950974203200225905851026972192373169756701942385661099312252426389 * x0)))) + (((265901827100929340528842431996721944750559015499937046721760416326541208312338087958579921842520468601093417710943 * x0 * x1) + ((-663601481396568935790269367656261319036217230641657099963625234347074622839398438595815722447190648266625867516955 * x0 * x1 ^ 2) + (210643086887499617984063800294382748423003549232454812150490707562099742005581297690783865220596473064993169486600 * x0 * x1 ^ 3))) + ((66741415328833980904692820140804587442788963923720442334525448991394961672863506239803542560365640283387167385577 * x0 ^ 2) + ((-127010958603942781359471176672299602449635509754784907797534888238871232615156861135751352265917649131313028628464 * x0 ^ 2 * x1) + (-48041868676525747205419125997405384191347324995106167328378491866206203789562984845409183082542261386768537217654 * x0 ^ 3))))) : ℂ) = 0 := by
    linear_combination ((((((-2408353036379495755904072406883405497661065616002816034226347914631805906981460836565990357643753436795889532174114736422780669268350777124147439007945898322147795251421567260166088721314806813609987228348490271 / 599051002670775476494755857500150434414494798187998407637412313872708259455965439452203275106075565754885743463139920080246662163668946066608332416797484659385977723495015384215840 : ℂ) * x0) + (((-582922818740285931022021573621756972847420306421145530383833111486152551302654821951274476929574934693956542154872468329898492320655309595622054198920215146079752674948778086296043197576679325820959907721448013433257866854726466001245913105288038930917745133421968111 / 686348306460221928147923025193050799773240890435929167156043646390081777924135664454557296166813412831927484151224304784420087608394217678101448964576886436252932090393168493425380128525215223204470424869266704398830378803922848604276000 : ℂ)) + ((-17237163973164167445507254650274118230503105664195544482419652810573305570301242686701716962513425013793453868682999474725793059045843826369138552415672361013958835621964538961508083936540007157387473746699287543 / 4992091688923128970789632145834586953454123318233320063645102615605902162133045328768360625883963047957381195526166000668722184697241217221736103473312372161549814362458461535132000 : ℂ) * x1)))) * h15 + (((((2408353036379495755904072406883405497661065616002816034226347914631805906981460836565990357643753436795889532174114736422780669268350777124147439007945898322147795251421567260166088721314806813609987228348490271 / 63200173933678195216265635709274076309926283024718312431581771531327636689590386010426771931265054268732744285846712450616480 : ℂ) * x1) + ((443631381965197082593335487029506389235310747814528869581584613570286639946581882533637023505689365141536523324372174931337448417075402738525222626143268329783161114418891365841261505065703302119166893705859764578235821545068857714854849051184540752390407 / 91626894718815594831387115748812100169869295396662884262245656241162500184556235432013130818779930266876537644117302279391570348027937943957696686132193606905452725144000 : ℂ)))) * h14 + (((((-477587455953535364393321138215902623676285014863027599638119855544512345326733858099563497757732825279541881012395312203196355036401151763816020167197753164698094891776379032092950008230057760855534542123758588330426389286396100525051892743 / 1580004348341954880406640892731851907748157075617957810789544288283190917239759650260669298281626356718318607146167811265412000 : ℂ) * x0 ^ 2) + ((18074600991346666183569322028543653335753164059860218495205831662221560337126585692841507220363310848534464236150613034452231542011955371461601132003410317170662478458656477963637430335715644988896243841516087340604734637717407890568547063 / 79000217417097744020332044636592595387407853780897890539477214414159545861987982513033464914081317835915930357308390563270600 : ℂ) * x0)) + (((-58294823836946767632339106310341112987572712747968945589274239315269058248211112351096805045555680184409933298285024580597855711809418477475775467149717334132673755680531063963300246892565109573198287217777547431 / 186714432938608993228859921154028912207209887634593248808519800548133713150819028916943048614025600 : ℂ) * x1) + (((-4069020278476243710133419154542889368462578060486189143890804123878121665882057515069134081153623792955896901969842433035869067008385517669192096256586831344721169138955869046229091879969886895486511041544806276664097529126513830946619414911 / 25280069573471278086506254283709630523970513209887324972632708612531054675836154404170708772506021707493097714338684980246592000 : ℂ)) + ((19886180521212688421589728161394360844148175349013316614446919088315383028729889608399207154317492320811753266042640695370948083170757395584324437456682357196607804426298150220839737823337709784820892097293286803 / 186714432938608993228859921154028912207209887634593248808519800548133713150819028916943048614025600 : ℂ) * x1 ^ 2))))) * h0)) + ((((-98518018919456018913574486417749347240334435156025475615496917573925233521765596746490399861787997408341178080999657634703727257496528093103323428271789270230100797005321021993899316638816254328909999836817959093303218602586774227631800609 / 406044697930001562166303457371730162685667560302631492794847711893777073828470526320252895080438659306804565540281836968837264047506088577520000 : ℂ))) * h12 + ((((-75403945753737117010157775065017112706941362404282407258390498714346204455706965078317011682339628496629637162590998541701794636502321851626270104101689365771878980056904307520875819758810687817077066040303963194372072713483694949811360675443882522480559 / 10995227366257871379766453889857452020384315447599546111469478748939500022146748251841575698253591632025184517294076273526988441763352553274923602335863232828654327017280000 : ℂ))) * h13 + ((((3600980368174658280164090511387587434893877651107133697958758637980027407133004976171786897206529585135818407472787762671485720019660354109834672230592169186651520336630190591551181548115153069806908670815857304419127497875346027501834332869964172971652349140741476073 / 686348306460221928147923025193050799773240890435929167156043646390081777924135664454557296166813412831927484151224304784420087608394217678101448964576886436252932090393168493425380128525215223204470424869266704398830378803922848604276000 : ℂ)) + (((-265781254456504398630848684222454483202915119634655135158166508911560165626661846509518676146683109731278680825111189896647209663054939091114272262585213329182427242877278779561311473888530122195750479198906644061 / 19968366755692515883158528583338347813816493272933280254580410462423608648532181315073442503535852191829524782104664002674888738788964868886944413893249488646199257449833846140528000 : ℂ) * x1) + ((-19886180521212688421589728161394360844148175349013316614446919088315383028729889608399207154317492320811753266042640695370948083170757395584324437456682357196607804426298150220839737823337709784820892097293286803 / 11981020053415509529895117150003008688289895963759968152748246277454165189119308789044065502121511315097714869262798401604933243273378921332166648335949693187719554469900307684316800 : ℂ) * x0)))) * h16)))
  have h21 : ((((1) + (2 * x1)) + ((-(x1 ^ 2)) + ((-2 * x1 ^ 3) + (x1 ^ 4)))) : ℂ) = 0 := by
    linear_combination ((((((10198696550986380622776216435256586563909816412084729911040157944171466582553389938416512316534101358734417253524772470606777565094902007510461459351429262053118453934517245370757086226222100319704578668459674372620834509469962359934086774959711070909466248031970101338674382660075511791962529655514403364537613 / 87599798343087495817013100608143391072285726519526540036807032709050553011914282382617560731334885769438327471600264259127231792542635547809964138672680352432088320438734034493108748573380882233392521923522240195527396291275683709667677350431481765706103759625221760298524377466232381657062294358551316532283885287435990532097364191543813376285500934513458649364396924552326117626626250907613468564437589403375000000 : ℂ) * x1) + (((14773915099505843955520463596838462709006284248801367220716257755271335964343730872011041174583349335815671983945975848757762918419687897766170340080916636623306758716850927169338326559782059691478136496324368518744165582457701904946393133770446526274287369313968174821788572854195756665731969191890999500784493156360400531925168943152042134224095550841492919320311744224514819696374555666399963 / 39347491614541572212337305520456737664580235372867122418360662159208498727857173419886240933495140683806129338017610391668774025205019841220148562461461226603914550146943983220337051115938770560518578786340689773108404552970463112544027952068344067217649441439114675223843532004877480446382978092444311886411702274089392954833890073120715271228495788456897773234271119336962218202381926350073691841078829803880706076106595394104565029059578502123267778945212806698384445224477671191034959108375000000 : ℂ)) + ((5806707797034128799922922944895752612262179805010974949309478884371038573346249473894965364280377554463863862555214664501424128022999022001815207870125652292817628964835595424062956813845030113024023189675555731161119644684343929835875613715915166973062713162764452082541494463383814801699 / 27596912712826327347784133909875925845822416753462494170065269429795920405607000776622793268030393971214081318532845355691481965673084820473043988605379501259834527492797708035961785239474972769191664814540179244963794961569370872879024704307820743292429362140545679756788856917306751182979404538216522137212404745546227249564028189387003460464831729875077850908067165480938430912582193455000000 : ℂ) * x0)))) * h20 + ((((-70093190771747762494212557992726220999520761863055283766069927582241980242671469729854542345303783408732002985840246737211310142663606655484547205320417015054866224051490683268844513870726037948199555927224787644732867269104661549359464469544049025889654008615360187699917014998034922030847802548557907375507191 / 747187903404706623104441843967495316358833743031166002908576070867417410331983536329790583408709514166350195886675934728416917723660627681265113670389906340907145616874660523142240260588802768990262177019731687535120315509550216167874272143057341238248014413158295309826433000125542353574666020888352659495902873326179576160752333911992159359688615490486709412513478714732315922747500000 : ℂ))) * h16 + (((-239840281379631603316530692913831725934932636721168067853361970518089782757689772708121872512231283298217902216842653904523008069239049947967644412867756648061346091652889757603739388844833899673887354159495150386489210124600891237794195383143586093274576545535261161589520437981714829847420021242604641133988872118260641387812217347763877586706838301331852274651463327263615280916429226643 / 1311583053818052407077910184015224588819341179095570747278688738640283290928572447329541364449838022793537644600587013055625800840167328040671618748715374220130485004898132774011235037197959018683952626211356325770280151765682103751467598402278135573921648047970489174128117733495916014879432603081477062880390075802979765161129669104023842374283192948563259107809037311232073940079397545002456394702627660129356869203553179803485500968652616737442259298173760223279481507482589039701165303612500000 : ℂ))) * h17)) + ((((((350501906167505476892547864945745008771974191443946955074747994124384170489436864504461708063385565707640065343782614207578488823918535525314135439223292562693607791447768866984920707793989943219098568911015523507838753333982247615977933451345441972014523516725424932843837057564377797823269354140591378362929166276503816868890687389921397369223902513875723316667400390975179688462848755609779 / 187369007688293201011130026287889226974191597013652963896955534091469041561224635332791623492834003256219663514369573293660828691452475434381659821245053460018640714985447539144462148171137002669136089458765189395754307395097443393066799771754019367703092578281498453446873961927988002125633229011639580411484296543282823594447095586289120339183313278366179872544148187318867705725628220714636627814661094304193838457650454257640785852664659533920322756881965746182783072497512719957309329087500000 : ℂ)) + ((9280731197036468447458319218430455376022413694803386962965061032742306032254714017324274420609535690537316327799205345331149593645546770212187640846834033395723325909212357087425292588213978204538595686267960739942677231244056791361453184448744120774897785120779186662432798059993269982604962242015719149372839 / 10219976473360207845318195070950062291766668093944763004294153816055897851389999611305382085322403339767804871686697496898177042463307480577829149511812707783743637384518970690862687333561102927229127557744261356144862900648829766127895690883672872665712105289609205368161177371060444526657267675164320262099786616867532228744692489013444893899975109026570175759179641197771380389773062605888237999184385430393750000 : ℂ) * x1))) * h18 + ((((3059656763372705297819752508525018510225437165782033927442166772768801640749006426739422555427565068999640321132491317360635586630633744302612833328935514455032644878991647824666422292829625385828632045054885267362924460346729379402266568300526992842181909579106710835976937924379421505876429622158654800132862010618987344330240120842680774621648061118972312934072746008406385796696119871096107 / 39347491614541572212337305520456737664580235372867122418360662159208498727857173419886240933495140683806129338017610391668774025205019841220148562461461226603914550146943983220337051115938770560518578786340689773108404552970463112544027952068344067217649441439114675223843532004877480446382978092444311886411702274089392954833890073120715271228495788456897773234271119336962218202381926350073691841078829803880706076106595394104565029059578502123267778945212806698384445224477671191034959108375000000 : ℂ)) + (((33218038290753119982971994037337798640491590417461383376437626548124477021009944821663313409604245842870884968246420596575983250534206720544771283860562302021378449354547261043590180026719882202084618054788341756662416087053718128672874563776054809652558006200261632149114194351489328316995669588351631933396939 / 613198588401612470719091704257003737506000085636685780257649228963353871083399976678322925119344200386068292301201849813890622547798448834669748970708762467024618243071138241451761240013666175633747653464655681368691774038929785967673741453020372359942726317376552322089670642263626671599436060509859215725987197012051933724681549340806693633998506541594210545550778471866282823386383756353294279951063125823625000000 : ℂ) * x1) + ((-3187755264944485284330785039119341272922764831512850810800280058716657654990379715362931403010316393881109743468082424085100158683655265886561015410382864796269581906540979007596947560161761973000170863859669294714229657662911668528402102870575056309766178277827516096361935363455227139 / 182761011343220710912477708012423349972333885784519828940829598872820664937794707129952273298214529610689280255184406329082662024325065036245324427850195372581685612535084159178554869135595846153587184202252842681879436831585237568735262942435898962201518954573150197064826867002031464787943076412029947928558971824809451983867736353556314307714117416391244045748789175370453184851537705000000 : ℂ) * x0)))) * h19) + (((((60809634920851391842603022296468215898669084417266421049649573738672848608992662511301564140115812374107421403422435252052622096360894163517216585239428870957712686875570290316794430403990210413083140618683460376478281884406526072498034380220333134684354744191429986474114060221219282909125043388114746040605697 / 2328862902504310254291659939266100860557478243559205129794820085043516307839279506826141549367182863695362732607912865415550149744679548881121241895198409137611853274976126903853859475654853181727107815663240287522334804885246031850540067162957537898313957625603505989340171339793226318677740953066500000 : ℂ)) + (((-5806707797034128799922922944895752612262179805010974949309478884371038573346249473894965364280377554463863862555214664501424128022999022001815207870125652292817628964835595424062956813845030113024023189675555731161119644684343929835875613715915166973062713162764452082541494463383814801699 / 524050670175856328869827833230824080758176022087785175459683148880849525180861020635960336533173633321617526342296472783252186462665700945027019071659034481489694630250529259266211115658530701877134526210891746681349825195234032246720952284406700329636690166990256301721412602700000 : ℂ) * x1) + ((-33218038290753119982971994037337798640491590417461383376437626548124477021009944821663313409604245842870884968246420596575983250534206720544771283860562302021378449354547261043590180026719882202084618054788341756662416087053718128672874563776054809652558006200261632149114194351489328316995669588351631933396939 / 11644314512521551271458299696330504302787391217796025648974100425217581539196397534130707746835914318476813663039564327077750748723397744405606209475992045688059266374880634519269297378274265908635539078316201437611674024426230159252700335814787689491569788128017529946700856698966131593388704765332500000 : ℂ) * x0)))) * h0 + (((353701272440996451737217969697035049567150645628999515266720675990295195481706292359864806401412915416363137522617269701826372389385654878120534071734098407892939321603463909521517649521701586916214973697213046179795805666399730558021022952828852310064167772075380190984874340782582518349200415723582688851359 / 93398487925588327888055230495936914544854217878895750363572008858427176291497942041223822926088689270793774485834491841052114715457578460158139208798738292613393202109332565392780032573600346123782772127466460941890039438693777020984284017882167654781001801644786913728304125015692794196833252611044082436987859165772447020094041738999019919961076936310838676564184839341539490343437500 : ℂ))) * h15)))
  have h25 : (((x1 ^ 2) + ((2 * x0 * x1) + (x0 ^ 2))) : ℂ) = 0 := by
    linear_combination ((((((-2152769578804881721800438353573254708623033157409842682665211874035871861958436023131386611730365860275439362185164114536486010703207533527069460194683124742167582797455414548453321249291000546826343137822966719478689551303541033632304234972750630176000454747747623122046330598940195289 / 84853326695066758637936078720053698201440732685669920579670885190952451578261828310334984031313888747820022975621331509931235939865208766828186341501876422984354034391289073904329046384383785714165478379617391245158309957521717442627086366130953089593562371766105448637241045393800322937259285477013904395402379775804388421081449021294003071438697371895934735526223545707710407252499648750000 : ℂ) * x0) + (((2967538741072240309923676370082091968845929382015534351516278037589511838615949118441701885951222518502672876666840906862662913908593075181130586771269658688978876643821787853628485382826115926068299464584759153693127882995832496101365892919063048769841303601750109582034754420653472775566628310336338051972476544218741569433137836787374700142501879191819879460342887504932053285934255817067897 / 18268478249608587098585177563069199629983680708831163979953164573918231552219401944947183290551315317481417192651033396131930797416616354852211832571392712351817469711081135066585059446685857760240768722229605966086044971022000730824012977746016888351051526382446099211070211287978830207249239828634859090119718912970075300458591819663189233070373044640702537573054448263589601308248751519677071211929456694658899249620919290119976620634804304557231468795991660252821349568507490195837659586031250000 : ℂ)) + ((14856976277459524001820093927524848230486075706785288817779090436375150661292249449916335453621487210878467345914551911427979149037550045819984474409266046219149823501190483108220162408829298270998527817799901958857925061633473728189728045951993628593381429252111635986901090463069157050501058937545361876248769 / 284699344615034361405292576976466020984928611188461255119622856304414297288721417743507072376838378750674564282700858842163503325763565530382383450686211145404287041425885612102603432863487867258525696251447280635464037946645972056419951388902315738544837218781970720970204226765255240385452456665291778729922627184166969229316433622517393472927878037168740610434290004795059882286535315449743772834422165560968750000 : ℂ) * x1)))) * h19 + ((((954540190522818222072481627290493404636487813412360077322406896890627755540616438688971907941662461424308891972338985241456996393747336231169057693079021409446027034401399396668498764443273182667983854009168511703649466362462511524497620897026286871444982539633016034611030630505211909545178939665457656961339 / 43363583679737437948025642730256424610110886872344455525944146969984046135338330233425346358541177161439966725566014069059910403605304285073421775513699921570503986693618691075219300837743017843184858487752285437306089739393539331171274722588149268291179407906508209945284058043000225877101152997984752560030077469822921830757947950249544962839071434715746528404800103980000477659453125 : ℂ))) * h15 + (((-16800909729535137898081159470486397179774222746076817077291962602299982740956265771284827842919544603658668463500406547204814805103948709025087236794365825290004888061845371966123923530483666266016196133064826527898643436121279627972708761627942790068842993802209394880672700058918943318872910587270401991567461 / 346908669437899503584205141842051396880887094978755644207553175759872369082706641867402770868329417291519733804528112552479283228842434280587374204109599372564031893548949528601754406701944142745478867902018283498448717915148314649370197780705194146329435263252065679562272464344001807016809223983878020480240619758583374646063583601996359702712571477725972227238400831840003821275625000 : ℂ))) * h16)) + (((((-2021136796858963679734591656432869924858906525712841604199200365919006748275745238583328785109323159009808882063050896123198162888456297962965314148473175672560337692157054739944016382929178377026786942523725365101954018413351848399654569156028817295413203690324020154555428458908168511256452199326236633540235035060973403997564207601685442105484309521381221918048958972442265986047794552353 / 608949274986952903286172585435639987666122690294372132665105485797274385073980064831572776351710510582713906421701113204397693247220545161740394419046423745060582323702704502219501981556195258674692290740986865536201499034066691027467099258200562945035050879414869973702340376265961006908307994287828636337323963765669176681953060655439641102345768154690084585768481608786320043608291717322569040397648556488629974987363976337332554021160143485241048959866388675094044985616916339861255319534375000 : ℂ))) * h17 + ((((2828634228829260672030241888880103933058560971601937728681160576011559014194789899765330475265387404546161536316309505180328216621889507238059061658356425363331446925585495172235588260956867458572893512769807053871467527772463944025967064451624703498911842165976342755126570376715478025957563172259514878587096365152181288795844115868069291504637902554217510983653735619286020605976508945146863 / 608949274986952903286172585435639987666122690294372132665105485797274385073980064831572776351710510582713906421701113204397693247220545161740394419046423745060582323702704502219501981556195258674692290740986865536201499034066691027467099258200562945035050879414869973702340376265961006908307994287828636337323963765669176681953060655439641102345768154690084585768481608786320043608291717322569040397648556488629974987363976337332554021160143485241048959866388675094044985616916339861255319534375000 : ℂ)) + ((3404798101919488315862137961567196359784241734682046882022260828678232688193888679787783253937398073623128791632081725273098182378696198444236115445860274887347942277429407451955344216595132155643877747986642766167368720950597299335646917989673268033376940345967861106512681236622012128456409663297421465966669 / 4744989076917239356754876282941100349748810186474354251993714271740238288145356962391784539613972979177909404711680980702725055429392758839706390844770185756738117357098093535043390547724797787642094937524121343924400632444099534273665856481705262309080620313032845349503403779420920673090874277754862978832043786402782820488607227041956557882131300619479010173904833413250998038108921924162396213907036092682812500 : ℂ) * x1))) * h18) + (((((39605097411268664614067954908972067795060850573952964444425483993783620487363561378691721066989496123563353131429505848891767048802103266709317422854412022742343954708590247396096358486628663491866855506028089332095991072963825915522966702593189062908893226030957737447132345277872962339718431458753337245597187 / 1081257776162715475206842114659261113830257755938202381690452182341632571496808342454994290777620615287132697282245258942933998095744076266234862308484975671034074734810344633932149042268324691516157200129361562063941159411007086216322174039944571167074337469030199209336508122046855076528951156780875000 : ℂ)) + (((-4128554535652451607945577749507774982125569398095880863154663961172567984355026806825158250268749832433246537960963249544606307609214737964416364024204148617364566759233345750498200220812081346706251568345011792402607233923637424000881898576531343782000284137172715562065237459836831353849 / 243309239724504724118134351142882608923438867397900260034852890551822993833971188152410156247544901185036708658923362363652800857666218295905401711841694580691643935473460013230740875127174968728669601455056882387769561697787229257406156417760253724474177577531190425799227279825000 : ℂ) * x1) + ((-14856976277459524001820093927524848230486075706785288817779090436375150661292249449916335453621487210878467345914551911427979149037550045819984474409266046219149823501190483108220162408829298270998527817799901958857925061633473728189728045951993628593381429252111635986901090463069157050501058937545361876248769 / 5406288880813577376034210573296305569151288779691011908452260911708162857484041712274971453888103076435663486411226294714669990478720381331174311542424878355170373674051723169660745211341623457580786000646807810319705797055035431081610870199722855835371687345150996046682540610234275382644755783904375000 : ℂ) * x0)))) * h0 + ((((10583385329730931857095266569104044332602275783813096444195207693300697453616437899013723157380957948305411725838955676138646046989027164225338881722988050592956970905614329260997780177363260478285222012607380702793507477476361964092864875744867772161380303170465974504066650936755283518703781350980391082028870056830554167732244695859584480240601146535523490633458575340130211480373880361356073 / 18268478249608587098585177563069199629983680708831163979953164573918231552219401944947183290551315317481417192651033396131930797416616354852211832571392712351817469711081135066585059446685857760240768722229605966086044971022000730824012977746016888351051526382446099211070211287978830207249239828634859090119718912970075300458591819663189233070373044640702537573054448263589601308248751519677071211929456694658899249620919290119976620634804304557231468795991660252821349568507490195837659586031250000 : ℂ)) + (((17711989176343961408862591095616981918381674926800050265341268429721059343666616066093929704928875705467035466071161627686937151525620078884293846258573534807774772546315653388264946839061506551583733036409493412122833896546633024516141771145696490689531229003539668384527837612110676156905513276142198852744561 / 284699344615034361405292576976466020984928611188461255119622856304414297288721417743507072376838378750674564282700858842163503325763565530382383450686211145404287041425885612102603432863487867258525696251447280635464037946645972056419951388902315738544837218781970720970204226765255240385452456665291778729922627184166969229316433622517393472927878037168740610434290004795059882286535315449743772834422165560968750000 : ℂ) * x1) + ((4128554535652451607945577749507774982125569398095880863154663961172567984355026806825158250268749832433246537960963249544606307609214737964416364024204148617364566759233345750498200220812081346706251568345011792402607233923637424000881898576531343782000284137172715562065237459836831353849 / 12812852330955080554328347886728108428417550635536158007530303663833820188317536074860582588728397200920823469318821057999616626919646523791056137566783339870637459193084650159553686004041951642838987235322226078018904803585779333836690041285773916528627918136681922744223397854463848763526152107029099563705759346146462651583298802215394463787243303156286145064459755401864271495127446961250000 : ℂ) * x0)))) * h20)))
  have hs : x0 + x1 = 0 := by
    have hz : (x0 + x1) * (x0 + x1) = 0 := by
      convert h25 using 1 <;> ring
    rcases mul_eq_zero.mp hz with h | h <;> exact h
  have hq : x1 ^ 2 - x1 - 1 = 0 := by
    have hz : (x1 ^ 2 - x1 - 1) * (x1 ^ 2 - x1 - 1) = 0 := by
      convert h21 using 1 <;> ring
    rcases mul_eq_zero.mp hz with h | h <;> exact h
  apply h_open
  linear_combination hq + (x0 - x1 + 1) * hs

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
theorem c4_open_1_v_zero (x0 x1 : ℂ)
    (h0 : (((((4) + (-4 * x1)) + ((-5 * x1 ^ 2) + (-4 * x0))) + (((6 * x0 * x1) + (4 * x0 * x1 ^ 2)) + ((-5 * x0 ^ 2) + ((4 * x0 ^ 2 * x1) + (4 * x0 ^ 2 * x1 ^ 2))))) : ℂ) = 0)
    (h1 : ((((((((32) + (-64 * x1)) + ((984 * x1 ^ 2) + (-1600 * x1 ^ 3))) + (((722 * x1 ^ 4) + (-128 * x0)) + ((432 * x0 * x1) + (-5712 * x0 * x1 ^ 2)))) + ((((8512 * x0 * x1 ^ 3) + (-3684 * x0 * x1 ^ 4)) + ((24 * x0 ^ 2) + (224 * x0 ^ 2 * x1))) + (((6524 * x0 ^ 2 * x1 ^ 2) + (-9040 * x0 ^ 2 * x1 ^ 3)) + ((2030 * x0 ^ 2 * x1 ^ 4) + ((3020 * x0 ^ 2 * x1 ^ 5) + (-1369 * x0 ^ 2 * x1 ^ 6)))))) + (((((304 * x0 ^ 3) + (-3424 * x0 ^ 3 * x1)) + ((12568 * x0 ^ 3 * x1 ^ 2) + (-17544 * x0 ^ 3 * x1 ^ 3))) + (((16852 * x0 ^ 3 * x1 ^ 4) + (-16790 * x0 ^ 3 * x1 ^ 5)) + ((7548 * x0 ^ 3 * x1 ^ 6) + (226 * x0 ^ 4)))) + ((((496 * x0 ^ 4 * x1) + (-17436 * x0 ^ 4 * x1 ^ 2)) + ((21856 * x0 ^ 4 * x1 ^ 3) + (-18980 * x0 ^ 4 * x1 ^ 4))) + (((20292 * x0 ^ 4 * x1 ^ 5) + (-8752 * x0 ^ 4 * x1 ^ 6)) + ((-724 * x0 ^ 5) + ((7992 * x0 ^ 5 * x1) + (-16736 * x0 ^ 5 * x1 ^ 2))))))) + ((((((27664 * x0 ^ 5 * x1 ^ 3) + (-32056 * x0 ^ 5 * x1 ^ 4)) + ((28608 * x0 ^ 5 * x1 ^ 5) + (-12752 * x0 ^ 5 * x1 ^ 6))) + (((-706 * x0 ^ 6) + (-588 * x0 ^ 6 * x1)) + ((11491 * x0 ^ 6 * x1 ^ 2) + (-14296 * x0 ^ 6 * x1 ^ 3)))) + ((((34248 * x0 ^ 6 * x1 ^ 4) + (-46768 * x0 ^ 6 * x1 ^ 5)) + ((18034 * x0 ^ 6 * x1 ^ 6) + (684 * x0 ^ 7))) + (((-6242 * x0 ^ 7 * x1) + (14012 * x0 ^ 7 * x1 ^ 2)) + ((-32784 * x0 ^ 7 * x1 ^ 3) + ((36176 * x0 ^ 7 * x1 ^ 4) + (-31336 * x0 ^ 7 * x1 ^ 5)))))) + (((((16160 * x0 ^ 7 * x1 ^ 6) + (722 * x0 ^ 8)) + ((-1580 * x0 ^ 8 * x1) + (3512 * x0 ^ 8 * x1 ^ 2))) + (((-2768 * x0 ^ 8 * x1 ^ 3) + (-15940 * x0 ^ 8 * x1 ^ 4)) + ((27904 * x0 ^ 8 * x1 ^ 5) + ((-9744 * x0 ^ 8 * x1 ^ 6) + (-1728 * x0 ^ 9 * x1 ^ 2))))) + ((((12952 * x0 ^ 9 * x1 ^ 3) + (-21216 * x0 ^ 9 * x1 ^ 4)) + ((24096 * x0 ^ 9 * x1 ^ 5) + (-12160 * x0 ^ 9 * x1 ^ 6))) + (((-1294 * x0 ^ 10 * x1 ^ 2) + (3520 * x0 ^ 10 * x1 ^ 3)) + ((-5712 * x0 ^ 10 * x1 ^ 4) + ((4096 * x0 ^ 10 * x1 ^ 5) + (-3040 * x0 ^ 10 * x1 ^ 6)))))))) : ℂ) = 0)
    (h2 : ((((((((-96 * x1) + (468 * x1 ^ 2)) + ((-720 * x1 ^ 3) + (336 * x1 ^ 4))) + (((456 * x0 * x1) + (-2664 * x0 * x1 ^ 2)) + ((4212 * x0 * x1 ^ 3) + (-1902 * x0 * x1 ^ 4)))) + ((((-44 * x0 ^ 2) + (2936 * x0 ^ 2 * x1 ^ 2)) + ((-5384 * x0 ^ 2 * x1 ^ 3) + (2271 * x0 ^ 2 * x1 ^ 4))) + (((-10 * x0 ^ 2 * x1 ^ 5) + (120 * x0 ^ 3)) + ((-2220 * x0 ^ 3 * x1) + (5860 * x0 ^ 3 * x1 ^ 2))))) + (((((-7068 * x0 ^ 3 * x1 ^ 3) + (3258 * x0 ^ 3 * x1 ^ 4)) + ((-17 * x0 ^ 3 * x1 ^ 5) + (144 * x0 ^ 4))) + (((696 * x0 ^ 4 * x1) + (-7914 * x0 ^ 4 * x1 ^ 2)) + ((12440 * x0 ^ 4 * x1 ^ 3) + (-4923 * x0 ^ 4 * x1 ^ 4)))) + ((((90 * x0 ^ 4 * x1 ^ 5) + (-4 * x0 ^ 4 * x1 ^ 6)) + ((-358 * x0 ^ 5) + (4380 * x0 ^ 5 * x1))) + (((-7280 * x0 ^ 5 * x1 ^ 2) + (7574 * x0 ^ 5 * x1 ^ 3)) + ((-4080 * x0 ^ 5 * x1 ^ 4) + (96 * x0 ^ 5 * x1 ^ 5)))))) + ((((((-4 * x0 ^ 5 * x1 ^ 6) + (-357 * x0 ^ 6)) + ((-558 * x0 ^ 6 * x1) + (4690 * x0 ^ 6 * x1 ^ 2))) + (((-7724 * x0 ^ 6 * x1 ^ 3) + (3072 * x0 ^ 6 * x1 ^ 4)) + ((-256 * x0 ^ 6 * x1 ^ 5) + (31 * x0 ^ 6 * x1 ^ 6)))) + ((((342 * x0 ^ 7) + (-3189 * x0 ^ 7 * x1)) + ((5360 * x0 ^ 7 * x1 ^ 2) + (-5904 * x0 ^ 7 * x1 ^ 3))) + (((3144 * x0 ^ 7 * x1 ^ 4) + (-172 * x0 ^ 7 * x1 ^ 5)) + ((32 * x0 ^ 7 * x1 ^ 6) + (361 * x0 ^ 8))))) + (((((-750 * x0 ^ 8 * x1) + (1604 * x0 ^ 8 * x1 ^ 2)) + ((-704 * x0 ^ 8 * x1 ^ 3) + (354 * x0 ^ 8 * x1 ^ 4))) + (((208 * x0 ^ 8 * x1 ^ 5) + (-56 * x0 ^ 8 * x1 ^ 6)) + ((60 * x0 ^ 9 * x1 ^ 2) + (-44 * x0 ^ 9 * x1 ^ 3)))) + ((((-192 * x0 ^ 9 * x1 ^ 4) + (240 * x0 ^ 9 * x1 ^ 5)) + ((-64 * x0 ^ 9 * x1 ^ 6) + (-25 * x0 ^ 10 * x1 ^ 2))) + (((-80 * x0 ^ 10 * x1 ^ 3) + (-24 * x0 ^ 10 * x1 ^ 4)) + ((64 * x0 ^ 10 * x1 ^ 5) + (-16 * x0 ^ 10 * x1 ^ 6))))))) : ℂ) = 0)
    (h3 : (((4) + ((-4 * x0 ^ 2 * x1 ^ 2) + (x0 ^ 4 * x1 ^ 4))) : ℂ) = 0)
    : False := by
  apply c4_open_0_v_zero x0 (-x1)
  · linear_combination h0
  · linear_combination h1
  · linear_combination h2
  · linear_combination h3

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
theorem c4_open_1_v_nonzero (x0 x1 : ℂ)
    (h0 : (((((4) + (-4 * x1)) + ((-5 * x1 ^ 2) + (-4 * x0))) + (((6 * x0 * x1) + (4 * x0 * x1 ^ 2)) + ((-5 * x0 ^ 2) + ((4 * x0 ^ 2 * x1) + (4 * x0 ^ 2 * x1 ^ 2))))) : ℂ) = 0)
    (h1 : ((((((6 * x1) + ((48 * x1 ^ 2) + (-39 * x1 ^ 3))) + (((-10 * x0) + (-10 * x0 * x1)) + ((-114 * x0 * x1 ^ 2) + (101 * x0 * x1 ^ 3)))) + ((((-37 * x0 * x1 ^ 4) + (14 * x0 ^ 2)) + ((-65 * x0 ^ 2 * x1) + (114 * x0 ^ 2 * x1 ^ 2))) + (((-184 * x0 ^ 2 * x1 ^ 3) + (130 * x0 ^ 2 * x1 ^ 4)) + ((30 * x0 ^ 3) + (117 * x0 ^ 3 * x1))))) + (((((-12 * x0 ^ 3 * x1 ^ 2) + (168 * x0 ^ 3 * x1 ^ 3)) + ((-75 * x0 ^ 3 * x1 ^ 4) + (-40 * x0 ^ 4))) + (((56 * x0 ^ 4 * x1) + (-330 * x0 ^ 4 * x1 ^ 2)) + ((265 * x0 ^ 4 * x1 ^ 3) + (-92 * x0 ^ 4 * x1 ^ 4)))) + ((((-19 * x0 ^ 5) + (-44 * x0 ^ 5 * x1)) + ((87 * x0 ^ 5 * x1 ^ 2) + (-152 * x0 ^ 5 * x1 ^ 3))) + (((20 * x0 ^ 5 * x1 ^ 4) + (3 * x0 ^ 6 * x1)) + ((156 * x0 ^ 6 * x1 ^ 2) + (-132 * x0 ^ 6 * x1 ^ 3)))))) : ℂ) = 0)
    (h3 : (((((((24 * x1) + ((-102 * x1 ^ 2) + (207 * x1 ^ 3))) + (((-156 * x1 ^ 4) + (-3 * x1 ^ 5)) + ((-16 * x0) + (48 * x0 * x1)))) + ((((57 * x0 * x1 ^ 2) + (-392 * x0 * x1 ^ 3)) + ((639 * x0 * x1 ^ 4) + (-183 * x0 * x1 ^ 5))) + (((-(x0 * x1 ^ 6)) + (-18 * x0 ^ 2)) + ((-103 * x0 ^ 2 * x1) + (188 * x0 ^ 2 * x1 ^ 2))))) + (((((-51 * x0 ^ 2 * x1 ^ 3) + (-514 * x0 ^ 2 * x1 ^ 4)) + ((566 * x0 ^ 2 * x1 ^ 5) + (84 * x0 ^ 2 * x1 ^ 6))) + (((143 * x0 ^ 3) + (-516 * x0 ^ 3 * x1)) + ((636 * x0 ^ 3 * x1 ^ 2) + (-713 * x0 ^ 3 * x1 ^ 3)))) + ((((242 * x0 ^ 3 * x1 ^ 4) + (-1202 * x0 ^ 3 * x1 ^ 5)) + ((205 * x0 ^ 3 * x1 ^ 6) + (60 * x0 ^ 4))) + (((672 * x0 ^ 4 * x1) + (-1444 * x0 ^ 4 * x1 ^ 2)) + ((2058 * x0 ^ 4 * x1 ^ 3) + (-1392 * x0 ^ 4 * x1 ^ 4)))))) + ((((((1560 * x0 ^ 4 * x1 ^ 5) + (-1328 * x0 ^ 4 * x1 ^ 6)) + ((-373 * x0 ^ 5) + (1022 * x0 ^ 5 * x1))) + (((-685 * x0 ^ 5 * x1 ^ 2) + (1726 * x0 ^ 5 * x1 ^ 3)) + ((-1020 * x0 ^ 5 * x1 ^ 4) + (1702 * x0 ^ 5 * x1 ^ 5)))) + ((((866 * x0 ^ 5 * x1 ^ 6) + (-120 * x0 ^ 6)) + ((-928 * x0 ^ 6 * x1) + (1040 * x0 ^ 6 * x1 ^ 2))) + (((-2184 * x0 ^ 6 * x1 ^ 3) + (2012 * x0 ^ 6 * x1 ^ 4)) + ((-3134 * x0 ^ 6 * x1 ^ 5) + (1360 * x0 ^ 6 * x1 ^ 6))))) + (((((324 * x0 ^ 7) + (-648 * x0 ^ 7 * x1)) + ((19 * x0 ^ 7 * x1 ^ 2) + (-1802 * x0 ^ 7 * x1 ^ 3))) + (((1698 * x0 ^ 7 * x1 ^ 4) + (-1496 * x0 ^ 7 * x1 ^ 5)) + ((-1204 * x0 ^ 7 * x1 ^ 6) + (604 * x0 ^ 8 * x1)))) + ((((504 * x0 ^ 8 * x1 ^ 2) + (446 * x0 ^ 8 * x1 ^ 3)) + ((-768 * x0 ^ 8 * x1 ^ 4) + (1932 * x0 ^ 8 * x1 ^ 5))) + (((-388 * x0 ^ 9 * x1 ^ 2) + (776 * x0 ^ 9 * x1 ^ 3)) + ((68 * x0 ^ 9 * x1 ^ 4) + (-540 * x0 ^ 10 * x1 ^ 3))))))) : ℂ) = 0)
    (h_open : x0 ^ 2 + x0 - 1 ≠ 0) : False := by
  apply c4_open_0_v_nonzero x0 (-x1)
  · linear_combination h0
  · linear_combination -h1
  · linear_combination -h3
  · exact h_open

end C4OpenCertificates

namespace TriangleAxis

set_option maxHeartbeats 600000 in
theorem reduced_system_inconsistent (p k s : ℂ)
    (h0 : s^2 + 2*s - 1 = 0)
    (h1 : 4*k^3*s + 4*k^3 - 6*k^2*p*s - 14*k^2*p + 4*k^2*s - 12*k^2 - 4*k*p^2*s + 24*k*p - 4*k*s - 20*k + p^3 + 4*p^2*s + 8*p^2 + 6*p*s - 2*p - 4*s - 4 = 0)
    (h2 : k^2*s - 2*k*p*s - 2*k*p + 2*k + 2*p*s + 2*p - s - 2 = 0)
    (h3 : 4*k^2 - 20*k*p - 24*k - 7*p^2 - 20*p + 4 = 0)
    : False := by
  have h : (4214784 : ℂ) = 0 := by
    linear_combination
      (-266724*k^5 + 1077732*k^4*p + 1398636*k^4 - 977517*k^3*p^2 - 4132800*k^3*p + 683400*k^3 - 222102*k^2*p^3 + 2873745*k^2*p^2 + 3980600*k^2*p + 1385128*k^2 - 139932*k*p^3 - 6837139*k*p^2 - 3932096*k*p - 416676*k + 362034*p^3 + 4940911*p^2 + 3006564*p - 2783764) * h0
      + (289152*k^2*s - 155052*k^2 + 1079688*k*s + 1458384*k - 576240*p - 1368840*s - 1676516) * h1
      + (-889884*k^3*s - 337212*k^3 - 1122588*k^2*p*s + 179460*k^2*p - 6873996*k^2*s - 3446364*k^2 - 111051*k*p^2*s + 33525*k*p^2 - 1357296*k*p*s + 5087616*k*p + 739932*k*s + 23956060*k - 181017*p^2*s + 1655883*p^2 + 176716*p*s + 6628668*p + 2691596*s + 1850428) * h2
      + (83565*k^3*s + 88371*k^3 - 406959*k^2*s - 875049*k^2 + 168463*k*s + 1663169*k - 82320*p^2 - 241472*p + 154931*s - 393547) * h3
  norm_num at h

end TriangleAxis

namespace C4Case2Endpoints

set_option maxHeartbeats 1000000 in
theorem case2_endpoint_one (U V : ℂ)
    (hq : 10*U^2 - 8*U*V - V^2 + 36 = 0)
    (hc : 8*U^3 + 8*U^2*V - 112*U^2 + 4*U*V^2 - 40*U*V - V^3 + 7*V^2 - 36 = 0)
    (hr : 5*U - 2*V + 12 = 0) : U = 0 ∧ V = 6 := by
  have hu : U = 0 := by
    linear_combination
      (115*U/62316 - 5843/405054) * hq + (25/31158 : ℂ) * hc +
      (-155*U^2/31158 - 5*U*V/15579 + 3967*U/67509 - 25*V^2/62316 +
        514*V/67509 + 1028/22503) * hr
  refine ⟨hu, ?_⟩
  linear_combination (-1/2 : ℂ) * hr + (5/2 : ℂ) * hu

set_option maxHeartbeats 1000000 in
theorem case2_endpoint_sixteen_thirds (U V : ℂ)
    (hq : 4*U^2 + 2*U*V - 3*V^2 - 48 = 0)
    (hr : U - 3*V - 4 = 0)
    (hl : U*(U - 3*V + 8) = 0) : False := by
  have hu : U = 0 := by
    linear_combination (1/12 : ℂ) * hl - (U/12) * hr
  have hv : V = -4/3 := by
    linear_combination (-1/3 : ℂ) * hr + (1/3 : ℂ) * hu
  rw [hu, hv] at hq
  norm_num at hq

end C4Case2Endpoints

section Case3EndpointsIntegration

theorem case3_beta_neg2_A_three32_impossible (U V : ℂ)
    (hq : -135 * U ^ 2 + 96 * U * V + 1024 * V ^ 2 + 864 = 0)
    (hr : -45 * U + 16 * V - 258 = 0)
    (hl : V * (45 * U - 16 * V + 348) = 0) : False := by
  have hV : V = 0 := by
    linear_combination (1 / 90 : ℂ) * hl + (V / 90) * hr
  have hU : U = -86 / 15 := by
    linear_combination (-1 / 45 : ℂ) * hr + (16 / 45 : ℂ) * hV
  rw [hU, hV] at hq
  norm_num at hq

theorem case3_beta_half_A_four_unique (U V : ℂ)
    (hq : 40 * U ^ 2 + 16 * U * V - V ^ 2 + 144 = 0)
    (hc : 64 * U ^ 3 - 32 * U ^ 2 * V - 896 * U ^ 2 +
      3 * U * V ^ 2 + 160 * U * V + 2 * V ^ 2 - 288 = 0)
    (hr : 5 * U + V + 12 = 0) : U = 0 ∧ V = -12 := by
  have hV : V = -5 * U - 12 := by linear_combination hr
  rw [hV] at hq hc
  have hf : U * (5 * U + 24) = 0 := by
    linear_combination (-1 / 13 : ℂ) * hq
  have hg : U * (299 * U ^ 2 - 902 * U - 1248) = 0 := by
    linear_combination hc
  have hU : U = 0 := by
    rcases mul_eq_zero.mp hf with h | h
    · exact h
    · have he : U = -24 / 5 := by linear_combination (1 / 5 : ℂ) * h
      rw [he] at hg
      norm_num at hg
  constructor
  · exact hU
  · rw [hU] at hV
    norm_num at hV
    exact hV

end Case3EndpointsIntegration


namespace Case2ProjectiveNorm

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
theorem case2_projective_norm_obstruction (P : ℂ)
    (h0 : ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((-2377543112 * P  + 55255131104) * P  - 329587112940) * P  - 1232757157252) * P  + 19218170764505) * P  - 22538807973688) * P  - 462099688803818) * P  + 1574789545806884) * P  + 6074246880211500) * P  - 38353979739332328) * P  - 33650771750857844) * P  + 587876644687139312) * P  - 359235734976368300) * P  - 6389983082016650512) * P  + 11224003517476704904) * P  + 50727347400701798544) * P  - 153638869498070064736) * P  - 282540523479624873152) * P  + 1463741464293858958416) * P  + 840284043997324598208) * P  - 10750522625045494652464) * P  + 2675532759031653972736) * P  + 63348525573372740930912) * P  - 57918226778369173196224) * P  - 304253527209808213942208) * P  + 477338057882355765068416) * P  + 1188847908610614132521024) * P  - 2806654233649162495626496) * P  - 3674994648499135559407936) * P  + 13188310073141406872656640) * P  + 8110262224914572828725632) * P  - 51669507335954427802823936) * P  - 6591109883085197265359360) * P  + 172005854573059746594529280) * P  - 45278371797460704738824448) * P  - 489550717875379314375424000) * P  + 303522088483593666502419456) * P  + 1184218888445265677803888640) * P  - 1185993156718992510979008512) * P  - 2371780853950554259942404096) * P  + 3587255674865375887625025536) * P  + 3622523905441237792255688704) * P  - 9047406131510815695659489280) * P  - 2830874522413669347599507456) * P  + 19667548476661663553576503296) * P  - 5678220500634195979842166784) * P  - 37708874349032204945398509568) * P  + 33121484022334950521936715776) * P  + 65490265980365648441761251328) * P  - 95907940807711351738421641216) * P  - 107165111913330509239272529920) * P  + 208281435352114071905523826688) * P  + 173529750818797022541540532224) * P  - 362442553601380255049389178880) * P  - 286333855523672292533279473664) * P  + 495754084264119978300064694272) * P  + 469345190965212073308274196480) * P  - 460604964089238283482781646848) * P  - 708784781344577398014446370816) * P  + 36274876365525386361914130432) * P  + 884878878248807660415018172416) * P  + 969427060289400913762991341568) * P  - 728228347379290656924813819904) * P  - 2528120377393284900752426926080) * P  - 99505025932570039720400388096) * P  + 4221875810838260464769880293376) * P  + 1750901680356498644283394490368) * P  - 5304570347314464637950874615808) * P  - 3901464106827175786344331804672) * P  + 5105433991793749768472061542400) * P  + 5732979031477602090159584968704) * P  - 3557396185441898968113512972288) * P  - 6377377108518394505965160628224) * P  + 1366391298581070449444921016320) * P  + 5547654574246951568147247529984) * P  + 443216163932258233341575168000) * P  - 3769632388826977616338026758144) * P  - 1251153534504917334952187527168) * P  + 1954532347107569413049610141696) * P  + 1163264204006004903435949834240) * P  - 733476656046566279224338939904) * P  - 704213504489471853072369057792) * P  + 176822238665679203913597714432) * P  + 307969912321864711575911268352) * P  - 18433032660829594935142383616) * P  - 103461466714110652487548534784) * P  - 1150551188060951094096822272) * P  + 30245269072755382541606715392) * P  - 849331224470998922838409216) * P  - 9287726416990892341877276672) * P  + 1061448758026543793593909248) * P  + 3166660014639886112311476224) * P  - 488346992018460420671012864) * P  - 1159748526299767495140048896) * P  + 107845852978668222340399104) * P  + 432486396114255015900610560) * P  + 49991611206934768027435008) * P  - 121197021104222354114871296) * P  - 49755649442854917650776064) * P  + 13136893452334076644032512) * P  + 14712951262937565311795200) * P  + 2678174853136674497495040) * P  - 1268525215085977606815744) * P  - 738226803846107715600384) * P  - 107572956951749626691584) * P  + 22648919260852498989056) * P  + 10699295950030910783488) * P  + 1073478908235179098112) * P  - 167582174250891476992) * P  - 46387858090777116672) * P  - 1772827788139560960) * P  + 417425827093807104) * P  + 37159077792448512) = 0)
    (h1 : ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((-13131007671600 * P  + 310060666500480) * P  - 1692806261063596) * P  - 12231650068994320) * P  + 148132650853409575) * P  - 10956566227936665) * P  - 5092900324494538036) * P  + 12789389689270070330) * P  + 101269481069961657846) * P  - 471390261990313289963) * P  - 1212381069473162052812) * P  + 10169186329977012957798) * P  + 5658779173107405710427) * P  - 156661960162945121057720) * P  + 103438858507247303688676) * P  + 1851106647575166947515530) * P  - 3032004725054762591674520) * P  - 17286265447750500271919424) * P  + 45644308926543763377620684) * P  + 127944586044457749877695804) * P  - 505814321290413452303186620) * P  - 723832289512093630591565392) * P  + 4525371617320174902359526976) * P  + 2650931485384784403598044736) * P  - 34057402223048745407489565824) * P  + 717947062629024634876386240) * P  + 220659578318297086477625360992) * P  - 111826888579906374093417701952) * P  - 1249348814666546100657864663008) * P  + 1162413264872484214948668761664) * P  + 6247403668291931689840291880384) * P  - 8291534641618249527321103860096) * P  - 27818480623155934267798986059072) * P  + 47876683569378624775640182230784) * P  + 111089327212151601639775738129408) * P  - 236506426991926217245758388230784) * P  - 400731759246113832838804209530752) * P  + 1026168789956940797376189479390720) * P  + 1317349742926598051904353682695936) * P  - 3969216081862585075408129399123456) * P  - 3995236366033845142837918227371520) * P  + 13810558013852990567854621800411392) * P  + 11377733524822682589364595163499008) * P  - 43450083039047834363911439401594368) * P  - 31146163180569768858341235652935424) * P  + 123841344536160023360387518679307264) * P  + 83998680388446376298570846856486912) * P  - 319160023796649824641445458105831936) * P  - 226620034606553238215937150759710720) * P  + 738132721279029208692170366508292096) * P  + 609427072624059695959632090931604480) * P  - 1504557347787809185143440550592683008) * P  - 1599245708864083972664066489704698880) * P  + 2589878263752169706100485407649611776) * P  + 3978317170904930936140942305322455040) * P  - 3316797678802314867566945887129993216) * P  - 9112959373495135520736227480252547072) * P  + 1269722300017706022918281202313920512) * P  + 18662770214650085015044393594923745280) * P  + 9523652080905041656682665340482224128) * P  - 32840730966468520697246496680016494592) * P  - 40602791086752787858202218153421668352) * P  + 45740841127206651278138804327837794304) * P  + 109200502318786908593441690681677070336) * P  - 36784820689245726731830035224310956032) * P  - 232321051770620527465205036975097937920) * P  - 39619181226587051112654820467721633792) * P  + 409880646928378595303561253514457055232) * P  + 257981146170306953920250835908437737472) * P  - 596347891467863490590792407636241874944) * P  - 704827482670959043904033739898832158720) * P  + 672584920176569885470364333477199478784) * P  + 1428900388223522666756408862946855616512) * P  - 445791163507279280160741631341394722816) * P  - 2366418473074936943474528260553405104128) * P  - 290107042615530784595377670672308633600) * P  + 3284438302067592411170028225821984751616) * P  + 1628879141638198815525755023345954324480) * P  - 3808654350249691418783739494167486398464) * P  - 3416733100022341928395411624083223871488) * P  + 3573537720493019283912145221187747184640) * P  + 5213918233702766020312345948640571817984) * P  - 2442786994189640720052188058996325482496) * P  - 6435285411584095590764639768525057818624) * P  + 656737943155449175917642350165722136576) * P  + 6631855064838411441785524898907766652928) * P  + 1229558162522294382101617058267862663168) * P  - 5742367473635532005043894285376478511104) * P  - 2614745969674147131732190586721965965312) * P  + 4131160576362838575453406680777282813952) * P  + 3155347778895767914735120038557799940096) * P  - 2377947282366539633803452139794700697600) * P  - 2898476052042513894621644265266914263040) * P  + 973115933393482057025542022051814965248) * P  + 2174755172231034438894334546583373217792) * P  - 125904859299432826943376382397629071360) * P  - 1365905399772318005142896055626560962560) * P  - 225492875201250534194321197403534786560) * P  + 722300225360545326038708654078748000256) * P  + 273260109444534549094615216525655670784) * P  - 318502767823408887561760357107030294528) * P  - 199757444038331973868952463700198948864) * P  + 112815588784363289719042505291140694016) * P  + 113309470360446868370046350667693424640) * P  - 28206085700379030757615824023511367680) * P  - 53209582660205929162863572422620086272) * P  + 1651723773893485214028488882111119360) * P  + 21094472245314380390010982437067161600) * P  + 3207605066395431491687976534083108864) * P  - 7030594770987332506670609679974924288) * P  - 2377974644023856664532468486746669056) * P  + 1910923404878270563744650544828907520) * P  + 1104311304627836589338023677539647488) * P  - 385605707906707946536970686818156544) * P  - 395294657107621166603070527464538112) * P  + 35700808494437008922681121563475968) * P  + 113650272975310010690874767906439168) * P  + 12603969980817674244102982123651072) * P  - 25664201682247828203176965550637056) * P  - 8213171865480436565614861521780736) * P  + 4029136721124843077873089332117504) * P  + 2628000027848444427478534157500416) * P  - 209870594257565076122162371231744) * P  - 541349472334460140871666951520256) * P  - 94300886592682223270325756362752) * P  + 63603620476087094309433177538560) * P  + 29951969332659092184856092737536) * P  - 811246948841501998679913922560) * P  - 3803780183371776582423469359104) * P  - 899169384053324382623001214976) * P  + 123215909021032981054263132160) * P  + 103422518027332501808699408384) * P  + 17276267743810333313685520384) * P  - 1546128465399113698655600640) * P  - 1045375796955989283493117952) * P  - 142252570981505420664766464) * P  + 3110008645430162734710784) * P  + 3122292884187909537660928) * P  + 354326206326633968697344) * P  + 13371152962099620085760) * P  - 66656648611391078400) = 0) :
    P + 2 = 0 ∨ P^4 - 2*P^3 + 4*P + 2 = 0 := by
  have hg : (6030342498950781788527296922778111382779766765786197449655859044995266461000496959751754088697741246022301058783239532301759645832011459463258478282063306487780223857231904508743700257166222809605009544208386321057063134880490083529717287536037883592526282802443708917424123200519946441531042514480211579666342201332560180692954816115924848653926304857193834447393995057051076009188679016048800547148789202116146019380880752578288647472897670287706088288670626808979979290828827611991675193243816963927114279959447664708541978019628149554956419150209255701330486410525075989543947090597047812269545784968394065004973572391799838297087175473799305037577840752441921204558639793019396931614859640380597914352198757917696768584548408677460602326149192510179417553389503157008433775928289732918439753262199928189263942289597131175788757435234807645752210300704715104982220348123254283914919107284381855028316422155053269059494200269036070309141177268248725768377088320572933506527000254750845904325102756772913278322408223183345947730433663147739919647854314523531082142129209718887618196515115086303163231981544873613989930796595672956524665622555875631648451115291634704099521388284161615331533647428024910390596738692190448094380121851172636550916667453347326009577085602731772315239695997325499544438468299809989603421150584115937204851321926539890456514863501498384384000000 : ℂ) * ((P+2)^2 * (P^4 - 2*P^3 + 4*P + 2)^14) = 0 := by
    linear_combination ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((-40081570862055062469536518046139272608695831871407268147440400711558413245866323977355366384504512612714339682001957497549064563369213707204007442710841686834712715575512541293492110883640816485491095747911119660066088036706078859334863990934601049294510246132701055073134281011570499954597043831917796469898621038511138796014782316757059454153989774304438301756423574193730175137232266491715579496684584959123199207006037519702390516098076180687840023763829140241621133265419939721090881121537870295393608080437359040513097085806006011859891134058961095250659371613273669886037641242569510826183096330348744345146500011496479116231850063997120996713872821741358456781118863394125320861264108892626499687212352884967103194620656808243061263423274663081376382982560469462810851647239738650277153778573434833670182713897090559157418243659700987759424199044313627545551243034504418040950117447023732844540341370892445620598659526682066168445495452467504153910427249570430757165485389710127270788360667261684792931163629748665524012992763665989917016140616815897815020412547258736686141545700087247462746639692741678682626499722668630777322051469216130711598672001141296477180528908518474177734125717734069028262542903053550924067006884465851174471239062428956487451515365167372107060308707550634333170251627627585445267553839699786982982925407697069250612941303884400 * P  - 40754130172160350033573483037079625926473594295586976205552434000135960873367908237300354464673167378558776877751469811721325444164096782617518774388914058931382954406870989912964345196322403132719240835334848382618625436160245065231822791719443358382241674647475913614336199116049894779045545981936725121354547272580675912053162681523368639579491687131593390835143169737465872180161566383475108815030539967483909366284602039067952738984879593908372114185557697112801107443884641407534339290225315934343167906430649782251853524398857438682059841704823517030578921403936673566385516172305793221734608938914703527372584323176504087261237578695915520185129033406200695368701586437524805025788695708987086317476422356171605393228060601968644198160688473313945831609674876284589356670246783575131329834870214584216230202516244114258296305808026681007131485015461151477305723317079173589060615976851800935719510345870386007836670299140573998326416441676021663604544233939104235194822189447024588162937903807591523469487500665412198289581999814752783459969815961051025840914045576622050413264192916675715507504465053673030294221851920200328078732438382590299429566162317676244667094622550746430392049820323499771098090090790844623678014426602153764956138104295563629582649357588555219463155339953000373520714014904341390172724257955987083935229199187723333616821326224080) * P  + 4695437885469957585656939106031051906468990009150905450220511993580776758867092881692614009811595047113943770830056671076686318793358681580546870620849200656886510690552068948197106005197803931370089484601873191305324707591277811797153812860280487280256358417823651832513263862814594796206635221234397768444887028984866545646246919809241105324223177858866790593731615815825742490545397957371563875119910983561354931875210803704997979639539819853232971300117309611335754430182524000297337679784493134572953585442252178988965759012432140561251534695928784774517864270062934641166424195010010387902957952212853506804054525610850389461030067426849007842095105552669705601066046621411815791269553644752480856659517176234890286971894532376464207635701408045012903174067739683370707247628729880995747467392528358065796774541167352482090611979254851318061353311170870753158753376317430148536475333329621675810860721386671003345978186144010822076404708944997727953514593573735809293602506474993425028676535090497900893192511501721564518649187009326416527639780570723043683723273280303005342179850567623051285758620828403995099447793021736421837426472865954648320461398088375652313413948873409169018783585107531474435092734128427202377370052365014418121566581214363676378681496400999048116806861964559997084648807755632101480588085301480901310409722725049147716965625580617556) * P  + 22299780696091220302677516457273287818601970541296524622303712195887054557882724994355968385787621921685586911666985281784240384766075821831935593799245792135216974614277870970120914898242022257200384330601131272406630468492500500977976241011332520696455405948272245441642584399961240845921083205507175950108616002256090530977663188504222069812757600983472348429953626634309776092170928413947418714283839852233633992359384642528689366986849869489192206681904188016807942279512319710382107153876181694916118974214608060107585304575252056956619590963122420050222816643257473675297124062918495903703108599773790748899281122993717496942288702993270070258456300373244997642133198964057490228322646650908380082676216238489852182336338780328956524902649468489225900219574104285111663576122398542424884570123494118502538479153336199046766849059351446869975383956305951263335812889376508058095471714697886527515998803347593600231008566614689715023277974833876216411942051032458134824677492926476541086512638275030305699605188530871788709521754094085142656842337861780751262145993306768116014068966171293594785841843494032413513882308012719382728045806404835729079943628242734846097791399175140373409690193763203569589876430745954163097656271336929147792828284226118984558076821804769547358116261346088455620771210473483736147784331118032299362863837177074293017042079084202236) * P  - 116459623247638000308341635595984758829352998227856443567144257944346682174149570825768163662550058913130066282101810778790475071243074958380305924143558523472589369826853102279769085946557479412129161229699077019626933009794402181180230686027399750807746006755640736266305570763134922212356156491815731977721884616386529035590186028011742711219192188027996871545587555457146722652735419407035140097247897778825477778895529883961404436173908147194072930998288574540011831081005971402101955267278220361190310352951885899317147841394749478233459243385285928702730990135795553959052254108733718310234392244008551656389364681716960766826670438073523159670319912626445238520013598296762758873549992140175992924642209275330705287665134669244992509198824169939194254733159821078414304694329153396050297004932307237757131462419783954592261470685867441591494272191250597913001917971318536305973389264410485762637595346533014999192287879716174889737394040843562744564273072660371016153869155337470634742933355477449767819220377980607023216669532718143966666926142110393122789964213172692365707946584179493164088852389438200768481418943452639284500991071370179299341082179147607587369070421296468445967990917495340543494842050335156275900949097349370779008431598817423783779338534039536377377471771699200685793237407719214482416374608074126638836686714576277229546093635882159953) * P  - 996598736964563908266555865457540295027332971564765956680594010169059708574608208184509324967480035239717257421325657867282280969693406798973330647847211897038046273700659105767972570166547692301360977705954697343939951105883274437690863424029449036165292088713411078005817591600816494487636152280522069421251309927812628715750573327044369027132218314161430435507080990653620066856478203249377392493743166201937218801454644707012662080326628313981210752434098610719209910206567575445956697700930284214209720266484452281714931584217275421625787557019380516757302646244552210446493869253431412799494674493776002396148563526164849653034902942316374496233665736179843185104876156566684370317371239483127421523682085944295022785823986330419659198772619368440515665000539952996792968249446014968039194307117509228095484945973196439690046827669175338400205063831927207537531458568298552456292550302966487943654124965371829207031429269647837759074309711539233091628258938402936444019997178506503686848124426158017826394186667374319008348240376759250991245204279689635479976752353156051854813954010512740735077222493656688307199175256340250096387100340037655619131667637438408540656292941680413904863824781163453310561659999609038898732873128665385323236153953127817859868920975048671906173291952991413448802991207792271813649252839070339075871299790877370157527560657430485108) * P  + 236377751142265042790784335667648066038318337795073844448276343214815916896310766159277040341234912322035417628895936221648406962521402001035180828987119590884962035656065245188377921448291702046775218109603676448054710998859548248389172449128707659148662719243794665112040583643941706694304354205833478454680084035521228438273132835344915052929447665172536031351035517774863378028810565845524128889139116265129334351614193367428196529934109291314908229502559599408273662466887491030640363506473815933582444589265379220414969985551680223565837013643441668288639439658484514999237827982023260709563317385901880845639616576253628063423764407706064918124356812917431709343880217760772142210692046940108992596723370470438323214362584476266073511632781266706468468334496228487575460398438909474436287869186756606527215565994299267780649354691225267843461584611033433097232090775671467852137152105810162108012111565701585489131020012663736203050880828946594766050444108283633836322579663856602423101323318380756481638187628179403822331550578087834200053999653968133949457117513145063340161063995554390712591418102090738305668203718967594110965966392500491860611958018652794750845696094808238812063860430980340852770015257534466239347744822222037425742930937273884717052562680523505285677141238093775774841210966827101211178545886133479094963175172129411761327976729279348140) * P  + 19046949968791691452618839847495382105169566961724311637652040157793839302460903746807161839820128199510631204485585202961480827917499482412223167862727375453188044041701460239983390016692730744498505143327280658783099225443923076878484001509815054477338376158101646272132137023902359819931152716981844676490898467581608454265116194359928941220939725589762016903555865991962628904519290317017875097960995257466331861709083727287758792305234296684699860134961499712568227799203862889286926469238285324118829757167210576782544316351557331537062588032459308037901890528432851336735850310384545311871715033547822184025370542408727074437627529312770227858601671436677777666642466567345865763204722947031074521419619665043974941052559832645520423962161232021339456032495017851671833363709809498960668582304753390749297602973277818605029777309566914442086501647303712328805038097676829729254513568714449720101451142969623905386578348652401804983019875412895498545097306110616464973678735544212235088536481259380263501130137439403882781138483048672317040552502832142606735222229666437988830411577091179639357299739783788875745110515583140834068560488608914836731337008987291773405427451086138180627144757339999507517125552764684129666026088336992453124414886454239767473775480586752337216475163634023687926390920905234664768183013808460071636595147294837909345347522360185512693) * P  + 32565461871393822146551357054599928823534799751113030199110279604666454479120126782221478510564980482370373374638445620389600450215508765394241726226345913977900364780615101784643767359490122476531012985060617020393446716757210976926071158418824384788187407306067651713370475089968657310382450053387071471421121619934212809298867529088258027015894299730229732186907540495484720523449994761684325623542204481819390067715830994717118573369153963622289410689323153796652434517853625237281173000974642317753033257201538650613535633170208576376702068202039034133245362659452843458188738248166103073827379372212479436636117923834228272467010190974001058884975800340529152095344212994157566843061453221486869605231448759648000315380577361990538979591706687476280025594100757481232672804554553513537866552044014667891410965689786545679836777924182471471128744714755102235335300388689061829247509674803058988178715023380672112149678769183591344587351838929203346716943095528741719610356245053530357879018257792152349602532121615796098246935988807684748432542076432448450701702757103621415466453862562023729661508765900701078240387602670358024491364557833331466243556870423931962615760575323548860437458583463179032732850639277716886557443454632015397664268749301875526899146384550445978081318059993119853907982008580497406069212266218322920724312433342329559955787680761713664452) * P  - 196719153803353167070886896341569554338246444216757239032645008896628475192633443973248964045099473224309368795440609361898689514308651755504205498474760112041093581535401024282748120407631797086081435234688889400244833267936539463825608755734275112908739389935272619093883940940737481618147558291487991228715684393309590315864053310989511986869687818848241949438455000231752115684698367787822169705043881555196650534600297316634322227139722005726888139667712793338240083284751230785925909464429188549227666347097035918506552279259374327502773896310390019635741246933430472241998230354395724969156783043470559981933660315334474185643230155787623455838552830977541566231324927524078543679485779260209753759739167282456775084307911236923670078878339580997816229610695269727261248054605266246129567283267327267625527177785184676569146111241941028013575696338961235185926369716272659450029375396194629665077292897740412616115552734358734438450752028049801698358643882843958254074452513499815254751617140318803508258534156155879988091112812921184372913136017871783636295084670376086905151094011345617922333495816861567809709636984464857091424577027470767622028294486338446282877236288213529469179787504164206038481782970274289417755650148961684371110665063852363428805262982854830973115820534061817449140065906149243665849642308964887041137486559166307546040499867834593856213) * P  - 689728237689246535659538253589849169500324421675692470139444461192443093069019324392295562557676973416859020894502602039926771380209137246016492242942764561625539659621078029691579949981114842869384956957973258290670405891366604072685405177173527505626980153415981139459784776917910955711449378566842507312159891124678456593622305730693419038318725806702108434408105243847334899468902054720265284380331902544836911658618045819076348405054811016147723996883135156413146568541474139820935776926206832547316931644780344795039031411580681852572948548530838579826413609191964429603210733177415338653377285412666471539863486606222621763874601625035535119432764591014766059666090741007591976443887892974310473188837147002416590061858258747664092418253469725260623443727083358149609261295448973883089899650728973083664042616965332292116909766030077607076739718048947163127109965223638464782189950407959555832588393073613668961874810511191764732726255201817227148589832564577538262499126803464939287413516551926763533175246474447583987453097291134687252229199292990879544876024197717257718857953781557765280814154323434339823012239456802652135246287835414101917908520057934879746874115811003040071117932422176993174828685808938879477514312858355687683792139420936347994063520451167385030186424420327118861032515116468633643904615785788046268571463044958140900531682023565877421515) * P  + 944898760382281205304829174817882459490596041680385683113153129395328018833071406871578885711128682756826255545448251319558814650439985959030705041845410847241829013045734638784412641459037257469777324735490055239954752723179595816634420853423379025511195229232320676470329981521955414480174686980146729215514651318446665440068253582361014550549515886150914338210951438431426281897213536028103396794930890896895106131384172523661151792467167372718461360234083067118284612725931875180395607625741441971212551779507974523864532881101061455523857344209881718800564628935511056462889702257940964064447627668684450495647219408964077298466158986564115283282228165176033876151732694796567863057712978679442338552456172196679431014861190464017355398062944580468936195943552605080558509278722104879783259603300995561652232898616804814870105070843567032383267479164037859143772625282137207447652206258858922467463512363357499880352529503038632619635612436922137223143888965844646600862511672525601812066310107028664686544806204748339093057060096625373095291053092872052912687724384916411061076468050356383347717697299159392365267643488135614817091893746534031241723969526180604961310195474605572644375812414154516454993550376599319322448017238069289728611571224584745693884203697608926504551779460522632634253486833359214092307504516817319001806138891284841344982234949886652783281) * P  + 7386466302719153992439271567058174989655873278170595172604820343871660230284631628735908573589236907133366486648714646639799643467372629385606868683915881878385131097488938106056750672293227168275964537572340726314942322040181370226905386778949011187332280510824227579518839691708137222162540615852167919985785518370367418849463649529261640050678249386731032496229975608303537912418347742647754544118889919214975881072003465051048664186422354233190017861834764418425757874375913227673875566505304907302688660033266263773305851609834036695187478272980111486291109123521960460657959158430794495506760362512069662878585984595054460492104025864740987324222534513751894090232248282917754956377186790908004712323227139957483030823533461179032275839599243330479472908310954300414787471341073474356828965936979888569315805089637668047482519849172003282105495492175029858842097791960167240048734987864980974809287515594911864086447997341816187868189051855450789594397897857028262037633357570388447104065368142638448382783925731390816990863364700879397013130793098064486897291917864420617135516857539900380519955118675734270898193178969822796796253538235207990503401128717250393733775626244198234802831877215310369245610235711309036500502404262788241109644980192586893360253821440088846008201253629309727245236268034621912736622853952113827149194937771587374114855585353585132933805) * P  + 2111152007262694268775268256427065783535874732165947728038129774177624614327749264362645621674549203589960408487726738181746139785209669185041804390786009418262812811535269122808439910280754513159438932011528089552555134553853945424026400197272400500819348169127428776153992698368701458305047158876730524491421926455847668268202249063105869410435322662834656983155228314945177434195108488687552594607908374387620125220119939358589772767325530275526720167115272738388229298671590621446821159590132806656170155802519515264488472070426994606113305072427781412169766070345644634105399995470678953207849898007911549805773673851637528984782821042700917616240426412246396923324434121655446573427069381579200889273247042962851700964992176655100167061863999713733514530120741270604188459470412951494364232445474577188294803956199754810327733292769446283695678715937262144629782595475917974796570478415504689379017054492542388038717062194166345566679534833713988843292991049959084931016418477137158468897262942024129211222772978775977885515781961157456890355964464610069546976236487179140880812116951456095689709417891851939685636509231498797902266148747258304551183659734874210674909021959978242749459272632869839522847922609110769247547792756028482680507691707559487005406386370982514413831841946309616359686238669436730952088954744311236841100619744750828291247747262013508589303) * P  - 49200132754990936795073507634204224930999401902471869790147683170766280321437777731469487095621292683759692048798818024291374045684627380135962914505583760941236548287859565489999180592282576689265071732414849755722763416783681383292802592383644026800437477719659298468438346562602780388125759458442124963972671770195370807939316423892912970473269727320704808704880531209853315629450346039815765732230506601193252552780440659038916627437579931282593880425711253572255928528335288553956463570341681738779702459098027027664339411713189857287235308387156061172531027650574036618750446270545319524372927996185163242040189759348572344821971691856157857004744515052868961025079082549398936634948989547758378172884460550356852987573642531852468472612683866632199928437993523343103907974829982952768872418009145424202722423856873352711307480721266739819110924961864492530855666560531563091474088138133861308264138989413250215668768590597974493371747530488837513408299321064305398963513747723850415564488551494195364884593591852256671281048931764626652181842505319821234233627000202292475253355820176068468378743594756701739802803719485314636772862434050643306513670975347686718095494161371261846016852946075323046964869645598485286369934115841442879924742184051875726904751796748255030016835973347334291945778593604977504248220147159954594629413951027812941202539749817632812771663) * P  - 69091509844459653709386799535759919365333548301034583545879318764246566444632288775530142372350012602675413012552470172425981053844760322125939589604940963133456830975070763404756663296612691604189044079110612145336456576613280162147342331831600760614469451939055591598318002927450233174617016471832712905626922258604147327324706860168872890231141306881541608405934653863128664058779125007137055557868367417397768304646025205752212330153586310843764507696785995001776374809797962721809394476386264242544796029057773530818836565656223334599690112853946718924578623251426338469601569024307763442884215411837643363385487508937769547486495617745783996332373880587735350279892197627428445417678491598772393076191241117039588527539147232946123469649167945258813747716971492066411790844728414118712867875504481697450873456710084256603273608970326615041020187973035126804010873430584730345790337040266324423480494780383486456681556748591827394521014744294571897721400823813685966593140514512805010228445888301649463628264570442294505828475269943627424599161090702623125694636501804600369865007432384018696352929347653954795420784322324175552929491955489251456678649743564400721434712728158966144858564584268905746600492797834136771205334201511301149152724875683296662937259663966938869968906210720979260910312062935640506418983358791301755655721472258106474164441849546861111015920) * P  + 207525623187787975104907582105043251716786610963014248402570555406063737909255442792440305554274261403075841496100980337172643453093050411822109978927343716734904733190224411842448918173333000369271228440778008861678857592341969700781919800211461710184689497529751272142676547937622569677717415791231369588222793968960422912685666754949707633222449357888383566657456400383239841583806154408405113576136606786232329871990596479666505663097781124106517365774482578459200373673186013902873060561295047991236885652704235081215837313464916156973534861269314672078997341679513194597094627015061199372317794470871868904119574749282804856472098636665942565355638256774528986529548790420427526311785678235146880481472931959931846917780293567013301511072787797534869314745850141943563365327678483217640030426301860209955394462642687908077748262001084751178068757774839065042057676996354025857392245339144265412668319691680879362694660054234206481285280854270065533030052747000964190320444124787327413784903065356623245227217241819178510302565979138775462499890429309082747056479229756873842891096345436805852033185141524999177304422091715300724778379799145453287296034591591595905455700197801870102073447706265183669669713681412832533538349994216788368705266272805755404227819763488963101550161742612149722547399823070434458171737486512000123936278445701221073475380477119495930608254) * P  + 574545782665062360005272342079252016862118475695039748138766786536780443750595831275544585638135338586901950471286362132898069302714543660825240701890797455912615334113017755912207849243238462904595450151541429254283890903756418461283257113363742516171923978689903977110712413604575593092184336336245949579291887550338487497960775993587082416034769878958547800307498798747344579863973242706711693654150614180698233729817877474436353480682138792972772413112905138417529223424212904640249437100270162279803964382200205872346170078779261223702893799236135179062892946766012753148207777536720119400373353457740172338610366407056317961330492977449015742546871590951750353498895559074819553987449271752817714957746526471656999656259080445688882317701226998771188473281100081281389714697122340364462624777152996640010237713198953234652055976946645495481814669254234576191121913841225068131556430388731981975162520001198271649392420747174616566021639592454163272552966751942564671353872801408047338875702890357154425141142400194965746844563520116887089485615805053974836420636424744748768448568254907126484614856176699219576045358561397363603189033225208972447562617088091944421642084450178747322379412448773089611473746656354837975347749662775251535932184026436928674710932149904949981970374253789965965868064633058367533852520802225905756168488786018529765392176214347298934504832) * P  - 415770888617706636981067712307506717426883389206598917777027234433229447000337961918334422712796355138414873735210658625766867902485695193174120564868758602999490161285753910337260528324178720606505983401487202242227924237231647741050128291845667746132818391467329937124069922606113091630298914207486290864623195071720765012184588745791062019774847607655452738077351235448147677418241626906472676243712579575955912613468261327170327461255949677285600087625463040822841246179684214515209042844435741656252681037568575567688107873919427855003385899141206900102574706335141525966811484964059656470785870296853279353858601931453807603610389213536024362314456856170757787222828985731369062043635277859174244430371854775097620439631408172032720514338192985271636082509157934302590788102657814840700823999496140503628882326543818507356225634494176198097478956855491655123384129602677735971562954692110486039077416246783416465845778769323372117847113939014013133832662765951242445850549965642540303569493364088920798787924954119910116406722917565151021806618036462127423811520665647938582445239262383749375950502831024206409950114700575882200189505849305313742384727819871511902436957025602572523616282351760311443551871612264328983353035218273474003726944136523238095580176826342061109789505222897212004387497068635494712502951400305027698395982896181755186108774746290535976261894) * P  - 2899708544017041336120000116116270475769016368458181201946587488706843271138372241705102347124758510100924154901991627840608612196228324377571205705317583304141104521161695794493508241524442844041588398514013477810671507782796821944036354585253111479731176780151579195663804695950059024600129081520919657922112687777256471184115973210630162345908969561157225731101889004525607792544318583870267916719844094901095823425230776246720348759943096398869134796049336368185986527656587953770187983300046031226002197924003724625246340480095160326457137252416170868099288554379173130277086012044839793924989285728656946491230223808805746691109137150424141583593052465678499668185599287215688269937237972303608163510358280793051398849090335278460175212805393520287248321492907929823847442620734854775610724353757820737957191226349058932456353743296302064767524071164850283144458389355086413500061827306517435040411142126692291508026497419261653799802118291114253650093344859772999850283395611468415559731151986104663288585762520345326545182911645877960960697959060409805660163147832656180071212950547317537639267131157967308694238343202862539098601297733900787230307638386314729105202304019981673504907071633320626759038998649209195168709082356547272085859286592591531086186115397444504791113457655855258039448522216279597718555686663582154185433442003882603872271204905400439558785876) * P  - 1064284306812536862060832647990728168252373848276795260245700611956358670922969506320729308622066370882483112154433375074024306577105866788622119872333323600986603450930886675721969170055085570041252583858499302445367722374697927882031046453667497846732855524391309304075385008569525574628413749876312144866558495041305916172308432634382602354285759606829843246239424845450637631105089223503629358286179374350146716668760127111148733764498550982589970107695599112293609137196068750208356673135591337858321535924518613854235133712715036724863255495722611931898753175796987560811489917899560867263240585896664764183109524681836794644120958347797302092209907481076718597151717519725532935582643196781592965284078935921918357352686693784838962077655329013246214915358253662166699828310232023336617982952228023968028019295010011457306007807474727324576726167651130604908178050688876869734710315894965790704899476064233730722118360132942575446566268679201709980732309799990564868370163079029188563954551897685623268128945668573620865145942333762575846838954925771091691414911912084733932906853888338791189354156368832460591515920342974261539738642712278680619623311601083023368331859115969939682735918860609701704007438714987338985346095764050883231589271885764846565473364149605694134249296097993087391769644421578933233533151641594931954607859649544850549605098254053799277289072) * P  + 9623188997572746538557086137980645317126552298931144387355654081603841336396919989870027906819540421707548542910654249597643369768733183370203179231741976528252284984420664855085416260550104808551950152221971337979951289596941184897081409396152724789043369820279999130901934399927325044233017508582688908425620612169649549674834504772173076490225476141528030212927348634583686631238550415424310003902363653755470586587984795460738511103420646493649604485117010828730353577922909722196904623400756569418494662127167448966666692050322165389686337253243290000581694258554335985125692483145011220486036905739396522765023424240282084698846541272708559838423068051864273474479869519424202788626512705699359370936650309185683976857120258219669147464975189748873840879234270421409393858432652809521472076423279129029242554444242209067113439442543879926127578155510433367455267361359327614142542112902402292422136416834214862189427898650950114256898485813462435158972510642994139076879913422081195239325970984799610473336315505945311493096812114940456859287765662604539138008749628483631224568882974807179430725230885817191681216161381380285716010720080969333319943733063999778709779562637839392406622973477332636277009539995883833629600448573015124834228094160385044582322694556902856612627196131779186688504830855936406596799010895550665403076840128762544636466190174576949780982188) * P  + 12261128452872131699727504556352038673869534427676869400292989789906703513854063184933855562339945601448801185208436024286582827296864099189170487774663269681286762759474172267185296165509366875321140523200867968868527653133500160499930430371727226630982405694004513955369782541070678969567920819422478969686802188230496253928365391356799252681243320777253273680329684030783717334740671510388071387084188080191503935708867367205619236065318342609479261951470818718274465559956199172835934164899463183833760648182935770497423229871721152556709310254590280314679310046846563745807727287249152523712295953116302918737721040386345721597264544649591658233280178039271170645704958031525912792707392581829084824067145870754378137949100264577291508264903188860915702921922259411658636004153142996472172296031361741220200668358582685349180869636481949088228556729842082892559376043558408829742254502518639593881313574418686874074270067815129834119305381317524354233009319541541744707179456538719609990067535351446793354732193148787984594312752562305388765134410523927979987769442481759109402814649528758954979170878623855213902208315923548911155425481054262537728370236881317482475840800439744049349199936670186732001646851694266988462996365562846163358645964326770185271581879926133058685579727789790780008227041198830361274589286960363913352629504387348640263081106350679727974933172) * P  - 18891987726335149102086459830936810707038384262591405350567526804511124526327158886567856435872720086742777834385153630652956488227356535464191419067888808833145482474293986579969082451638947434558942358818865826946940064469690054622550000420181232967615604815816249604939329323886174495843966646764645811798938626338032598416947053438928396203170677607210872412501188188751946311570741371076145615512675836500301942827174749219456197778237636482189457098218967534092158670772799317256923799184535248097356874936852405456303607255791049658710873855997640722125138853647144539365688737344506378632256442727105185402434402230113735236732567041239705542505525050620175600845261256097895642008786276880020155386144430973217041845509536388929128658973207498612406161184576873989788899860556277159112915294624677802919642491020720785044103329594300773966794666906300274918976114829267097048149754235158347434980400581342152996237847228618796686283923837762647448453293342580774465419396275167612670579534922839419489905617360451653071269583456457756016835118017184588025543754698386377487031424182731721094688896656373479873398059525140960824871106941665078444070051655173293992121011423758818002173748032878668552500698061708993332331678968290845521680936968925463740712236316284596639043037071965629371727543433772025793938717325909728476875461915960174170909990830900536507796216) * P  - 52048175719514199534259977531215492963501509889619728369501474899724633148554825628871855185909375214341208812293189078907834068503125287088416380420138802819269283869241360814928723414214546535437269133206841797188773819580150815308936609468827338059211215883014447599088021579613612092936074666542297327333494369374441003691555718465138351987440680491564295739742438548459781482009034860066943007812384034660527754648753527787502760098199984413329916053021256537567449782798946931059972911193948682671071750058086402194724273651344121399548122773319301030090168557385454979731689769226456388248230959869152201173750929074982514138865528002887740586466557452970624815735191724105286174639350536250236274405034417184783509010547291402302456171967233590344892376809349079421241817891247156688659119949163219544235774494294691794785649439001064763909394019372836981390607102083114885007175138665732871324094514857051370319718332473516996310470520642464302859304666938474088042364187245825037653726964301341187060064305915741751332149829379872238949951369005454417503406544862208424037631958567364912554735700277950159977119431688970951978333049880224065833759712850152911665189226759466840027874847744226228045280702901494196178433007382987487624278648201285901175978465108751230100771540619451811466570195842954618029676213718976930448291558520698843728493879492522902061420992) * P  + 3442921968255564339453201236165003826038555187118964169510830697691600178997218057450071950646296010901167879909526732002974843576830194171852245875411608127295526058740728831522097159144511542363787584420332272385033505002173736169535767496364795104183179299973937288552204734501217033852197270800284708948251988723398446963315473732014453303573777929952470161622816130551791251343031719469527274576965757106593716106256565860115798901802418592378442613290751967763693942110789543160530225851834451656088787349263570609170988410548467113825601937623050670557358258858329470607445973247326425088679936089250705265443612220327522354332574248227583003431429386800974459491773137114400813924501979018390557020224677577824257901198816461092633081047064131966941184544637935455029763088052701345193461655523607386272995821700073233106944657242625073249319585437606966696890406470278356043131635168767935920109596278304188239476898072061765055837574244722703014190741325205456360553600983211737216636490447740302161313286134559816784417394172072795147213179726295312900257586934235965346024436407982098646562713849080352646964646319767069036599148867861848896245910944937166845123907971138424153796785938610606685595104603954028734565948137110044176052058672043132903644771560550528516825111917757252641174984826977254834194177541694127877424355860428123329554963359172875438991760) * P  + 131638689336123095068273015694856283269417784751867863296272990736108103239389565960467709439050317725929684839315748036421181590237701379789963369971126523953017062982418929858444848540134396325247745858835819365902856670942594627808985824698316168232855870288024788922267069078463124593175887814122466691625462425068462566988779282341424813497366707298953043608954644443235736002397801753119991159193408287193896109052752204298566281392884662501634078225613611033738616831625720357415072002555993865777498720253682711280275468303327620879700529869800488464048720086333707530197647341941678026331200284173704609337151726972557686951974097658972691714880440317641621398687373805162960409301785869062628689233889910189837083812188014305470435038967856736282635125319592452290194545420838199256516296716409135196037803969603555140664978117667036731287615119594605605486640145120604951367015790036430584513390695545196948686352844501493255917083474738132100036260867264183759710224158899050324549745510616694054043103344423713132154762107968363537856450471838681773569964950266714843505206308894209287941518679389613671996079927284585706369573183434473078796957211908999218021758519239433430851779767280537766900139308545501295088757178395204758180736700618975621777117693393906272343306364406403313191071334765510085053870448750728767685710103158009035814432906279652388960559240) * P  + 112470989906882768624646734818317525244058488773356526887328388826246367959943341351319569090374370563798815452545612703731663403864910937304720120630297556415792388606686439014438299722661624281063776238171014946885425691842853117205135007459671003282256227250637548558246460636368003090371526512971350567689307939024035022306787367232740154782838866581154013080341004107652115082267261791359848660321578286965615403915279742196556043535116781318344747993862252929941510163438095276252389716263560802960612607089936826111773604384420391199282825462827340888617201364331777341415018341037294800445491844688512045379352412746349061883267624410132600840447115408339628661516574373230158360434257439569221871609124428864844771196488220937465676122855416729284907773481028883951734327401999294875001544094371215484399019453216779292645086025563822380164685584998607899991135353164804887820836709882379628963687924097883898581523724264354973806758686477713674286878981065149939937564254090395469533408919162162854169411130242220821478167122009547568743355308122915687915482095204368298539455352310754513268427485747314295371506347530553857193413893833914042288195976463580105248106527977299987213685740395358041028514336476085642420795021086677624699888450829076230652114236834312940930706666753810809968596559133006550042871505188406901506250023184901901380283828043776286038615920) * P  - 183153945736005088214412027909846263172994808697307258395172470546015497960440569914818416255448585221132797004385091573560139885413091162052250458005513944877529113111427215090515297944284525687984839583118328689425382340168529963052274536761846266053576673935003353177137126047748995751428021911898104404550208517544699298534435371201055227008023824934216776490475667937515617434874381321375570841808015337369733053940138118457053702984128591944205948139961473984644843103290646501260924103549296357031805913480329292677084331785228356091163749335154078091302891112436081549363397458225402759405105940489381673067851325838814030574365438013780741800994115646484779594966301738525930216508686610750437217456230091735084585557349945955778994970809204578724752439692361213613511393557324303741573755858360272329985912744861731721522853847661662392254744745581171076380588211440053977309071843749317588040225382471497190699727851988946204197577837240041996440150819757703491391874047487261169918087341418662458219144146752761884120761196892579610071749056918540602682222410155931555614786493146922320653686429050682125084682274248106988091296849677888875596816533973093679453926719340010219386656652752021468737507490661643821964290752009444034646007730260044672245224096992065209760376364710491237600372498324261099408736229224392669479950166333538674925037737162106044872663488) * P  - 405980705459173897147633906953413597045059311253527571417630728874731732870811239381992456158058090749655756563890565754690112060797164919743213166026487062220411178623955603161872017317391275682229014508332480195188270229334585604436628096009013125773072722807201579868234430689011066471341358913216386833449376841254690341373727038700244904833979655750747125421286192187869348360188010845898197863034841957480304952396538664378619908312493030558616803912938823146099487130494387304062459123003932716867412625717997202715529761687318951658994677764885849978458973330998362919902147425951363065379219891717805805175963459835693571674202240707023736773909533163925724171171538209780811105559915501720846574085973348465404510984351696465539400075044984319893218874379821746086888320719961872257243205047422424257160579345296498490233831644873920656607651493464945702575213894210245761275281694869585167682713718975290915892130972988765365188830301585003195951095987693223887643977472897595089521906778334862499049700533467922632082320407439089961095694873131161835507139565229581075512554670496385201370612426865056316777145952042624780792834960350290529443845752558634041436042749722897704619788967790904803914072686681289899092902092062021787530292789171337158791462707021909282077477504927407805276885598174614840409481050709754792609565232210638256377840889613734332234139872) * P  - 15078393016504928358628146308235152332167520634580978011503784376465037429081784824022676354334366006566039318697862098178674176212822593021049155866830086529088292704644049265537749523231490859381067705492325255587318838010625136656388468867772411906300034858501975422087596059241107073263702243558370612412862642206328137611164594412171787153357599726779024492929593145069667300783139709734579203053876298432201204765269019744559243028480773571768160436377284108817163883020834694555908221300044727676231307037335505632970387356688346771636285048012964876945024693767184829753109479422275719544986542079990757348023724730907695485232381873861354529791212476925294256749489573193212005275605171950552527165242338050643116709970830034462535999231298223486118210275578925454808421631251983833721780646317900433033934449834595596289768919864769289654629222637004020567073522274938356800155736375779466100205775688771299254665813741784093181269531729107946410797058353243298819133948387201485287049736482027864464908491716825514030573319636057482817477567258705721661660431947112988623636588756362521957794026474700192194241350191852488851225455113694738325819198998503857691881016373874703728955166980298775874408276207551496207976489959811195421807443026725047330138760672272741232768975145059810718250390065867137358356369941148106706446496776911243565115853675823104758902688) * P  + 776701958984918917451517607738339882665530982524663171044768426657462048198019200014200565111806121474419189212436610168957117422797885147842549738072459340495736964754097710244786554977070933950756218006889818209337573770626387226072437482226176543830585272135659151811321788624895755157283244005272965919662573864637853705193943329622560170179277770403705989580806613576379619120095660337882180451854426846817473681746181760114394831572931841849229343379957837550058506058861065864492555337324349965862525403070408697840135602460564416672722140143742591328324961054713547835493552539877159911336390458794695254666777710381496434566543647562208395876999159903022132684407843861750279977098562867770239900630972662784714907067581325293316017956761816775991918427281286485364463155481957044101665257877128359178456089349156241510712269862168881985336001447546962494859673244623877741273515219306266643209173377942710774042284135860918236142145660433992562205201306413218082845784603814482636082621491831899934010281204915700697141207778907739389355412068092432584874418057794408014182768098670244904165497380290114514110506925447314930678385595717878533968736690931012722667194521984421526180782517198443792362143397894508741780434241515072407173845116188896594236024102303058133173770875862051564592506084838915688940377113432951602322093955726356318394585439978802561788702144) * P  + 741658598679084007822914025273885697083076410884438265908336725741593742255615051644622847050048061951913208590400271363948006176994675491711797253114433760892766578043948735776710343002012574877922472217718745646735823778914939327527025216145282169553958771269979030418101210545693692609555032885584252557738334333814922385365639564401334346129190213734732127261863980652775986695135204477402223483896961103069912913050183613794082631395340389246957462696405284615097729238289914361913231228027243529340821502079629813991377630184361326050792926457522035599904316404225383558380062170006161005672009838548988434890013860435675596243166568410754454737459354952256868964176471493642298757742375003587693727457125131517816530709316968651187900704165035867350588976104227797219564844113514482030120252156416565108644466756450884330547571394933720368325404069581574342245182311000120333573834998717165074975087309739577705026974321084380189185868895514916788783803413328736077009792818180172770916530835273658646267202171216381421827692042836868705389900686279964341568617534129954520380220406253269227206924096936964867538740857629700266839359326453030313696594732850270490511604731811921156030495385538778890753782523278299889066641035021310918443563996901831468662026965726487008996213485307312403428165668461303554864187510841836711900960902162250433978696870863175548000860800) * P  - 771723962177708862491736447721262321787968892370181468832163908272020242546157156446831396497243261984454990383135121916652094431033928553395934962611800815784451219098082976107476005592240259300342107301659872063302155276412851274407190247607603804746466013668448160122068299534814910315071588741835620357515983465339832475989034300973563470962081085752616750767892791102190340478188198138494967518053628831270066079218931430685971953061588414795668642634464802737537811477334127610556286945820762112751158930363558060043636195175437875484693260807604598390312632103412329320814692344014047049148958647922093592343674189719983630343079255844788242234029447318957459970921940577325327250607421683248170525011447872105465730404361324905868492447967167204573275780315517227875523917583640010379792643585380794744234021797069444031158912177784524092858438873053555240839992530085508463656831362256221213010209547540605145046242564273923590497620463888110990075205872315694598758351541990331694128569419966652371415988975723800667098199842155546473254796851715388525662390199526715344947443924247849546464543035096681291028654477761286218368367186838893458764134948797685792069221448905935554283230493264951350874486923489505985240212085706616470323176465650033156718931273825786541118257281041452126579668001940694291737243959130014293936855307223551070478822321999839197716220544) * P  - 1966050303879963462593450969784210159607700785542499779768823361662118812291880468939915808586500022500400281959333650492678197629596759947160324621508396134092051919837378141012695739799521378591730584138831942842104343066282819386614542909284387550733454977238754366982458969649678155634880058117619121611195400711205203402311586337646643547487262301687910007602044849064538456747965288342106220683168336479861070147267542214632878138632204350112959102151194890996175759234169081229478135069742331296930422511771807313940152791855770258679240117550294826887979569976785284017785709748262591866351107745303137588580381251560138590003019777259350188307651924646139032866888523359745614723613232306178670097787943219590959717727172873595426016046933717385372437568818458140670462527411568532586513761654904942386803165343559607076809201882478392554739606827446223550282305516168032575505530287071539858099246948101776676488550140017837777127834175793725976574392463373869668794907526712754744150492296426493187089364899259781156798736193936647654239980311212721056099885957838753399785512864648032383424729662597278243380793862017770789332671782950660744150577886472860556840029314203921649455919235077966177722686251522270008926166039632231723669946380246412986139378484882951880128521671970118449501444961917595939013223659753450762757732737448236408960993914411357265763230720) * P  - 251892836199959731840038807035622747475365382380023645855769773612430444672520924590460376964035247353896376176291511645550217169817284937282907522486011987649601128934424177730916948846843904501234388795404279947994372066062682456001035643992752233034206845997939769148813958168567379599145663280057900411610627917330859295944035210771152985103610268466968999351437885727905407166097321419360313868150135427517241619514132291116878986601581181787968986432686647957371547808142311492889520798029066373303938618206043062387844871659256068901986942010034576103448662872743313834944587352850529159204051422000482148626197240212008546419688798103140453931558037982255105328844005192825868476959050462121058201157840070000523087522717774060167443502803931172266794194595872311887818044791842695385795879539926721507649995787165919942618391604970991686923722665164598666846886952798553145480202096128212691682839544802286119929242322488030793438166782312645728992959141385833039969253091437066068370239132709804700741118741476650284308956807284238337209946510781474448994629829538144542657464716125803452184936803840480617377508319100489434483923997465455184240419331154911195586757298801644596661933825978667259216426309705588285402194439574851208433868932483866481841179764750793750295131514763214511896004591047203434284504561202591528788260569450861951486649416183715443736533760) * P  + 3001655867457161472637393389231382767405502541537122133719879094974605664368979064344811970880950013522414435972575709793475741172260611774586095351259315804102652352974210825638885990085323908893760467557817998724869871027085097660267096524805673348514675651636184314064816460761862557329056480854418153157126322464950897896767535096475833798968706150018329061347935319525730005042109102050486329485144317419706674872343814704062629950845779624661754204762672872675899615576844208594643280763961163015840474543866916614297416673673019700317263796331044453368856586557227738287241288966222544625781820000343608278200748127433064385157140114652437765849915940144597826295047498489144523730851709544296111381234144577369680787758337129492893827337157463934463821101636702627566444308592652738102283085586799770925955042178094723944637338419420729437898775869503665840306549325135277265801651053686410798763786754609578384505789881893845404287043703428646933409027367700024357595141731781674765739299603036835697522628423162855626687274886606123629675871446593040648062996897838522646292563433370140642467904217332222181871357141465805714424406480529146452852734097215375621589773269818579606044640113140545178196562700128420869277460492654682145321089919223126437115196792954221381578524872907520365183533508844234992031670138725717835086578979149094629276038188969874060303639808) * P  + 2518020629186322504436987621551389910334966837214789636805345737842852827427976650037627302263707911488226168336792060617222940921552246074668445696556481784953736075411018871329884138235080344155801714679901153228792393700422598955517208265852635562137900569268957068704756072134257391887369854405560757604380532718486958527664502257410636356623388128987087951329375816359594818770187941618379079220447903023838300822152709434403510457024833527421214111819660662627131137912757203103255677069052812984278167990661414855992005933412888022563551512415497623275848434119124369268180627242663935198397435571080767789201254265392050803568972650932841215342565957571637994139994123333603221135840725269201983962253964226076755373106611362569692217392746680250181934800658329141794883590200147165538049485323589711636306684136618443075682659585849415949579898445481863559565171629333990281273342474713221824391056739663497168283105624698211767840037962232906992359710995595562032793871795945553016544258052689374306274957751358534881021027814172626652691555172629542042167779841684373653500561697470315523111764401101684382623969375180732477347936639781845712558337922700069678033715120728269630305464747152463308432998645014099009798387968844689390869825483765022127841316103311163006794628437619047437146332266751821021027390619941184123877885598518018855596719216421097558188106112) * P  - 2717755871556977920168289641990975839061828185376244721097925698485996330487566657916330918540606206847989621311077667096655057551711251457760460446949125868170158095468445161343470505195010250379957578638329855417121863261984703277752953553687779314643094776885815801284995895362294437329872686373605682064645049527241911669003767792177074237892671271972209868129292417407941396511393978445034430540814749411490305912085045831892357401159460915080814029373997671198100675614672931949406241032702667054746375880238854151050912128049764534969228388460377929402807995090488763223985476612357012721122871631054419270340202145506253783659206060283287403751699745426521247500210898359905960733261395990634766431173846107603605348034778595188347817355073914170496049892683578324496232721295036592392754596048229466045226487960485812578421640306405163633896906082986212678906988742595903725089703426408405992762044974522601848048810467851112126630724940108732086027305573612267765725293596573456045824659444872673508306376600369763078318138823626370569194763005781012840422639953432666268589644231576060180786256643306100144706155010258915988686191800831249537258795599550318069919608482430762033783934300010300934081688239006638475011158897625906711437955289148760661021013892296663754529962655332124822738674330153115976327058631761563827275028430063950911648468680504784097555508224) * P  - 5284384792149171446749592838678952148029610347847367632842477133734598420788876330184539381663320607133164028165397027585877693821859172468176823825997710296664454505885589624670494717182703720844561428458960546963616658259702006836886910655518043876085677459553300584840684490002672488667147289532598135825009531219620511671503994330629004628289151594967497067331094818681252785367160059377686915460286794946146650360648135345039246613356831985939601123245343212017418523862252613823339926985249393490430393841793877751370814057695273702286526318388118235101987701442638172536784943303338318015533751100373807692056962796341617578609629692568760260407685855892718174823095693878575322684984853091001143815671983275866696967476486745044959219207265853501933865721911870198594199123708365388349807562027187266246777225792425066597231025442533642451426051660201132046774159489338326706785881870141480753173336282807293674322715689388309324473683453965953609514514464206500447716078418419897991712227685999609642854471650742305708630571389794219440755208634534088760166422048971277673825849865749931307135564063663396402398639493863154753015987952729600968864951371830784619731734387371323567289246872857522473454290404652058555335425189915343096557422215996665228563117325228865668380109910382059122018909168432097238132711623424728331018812467142649324177702980996356680991322112) * P  + 405093563447544064638312166321060631131236074407069918770015954551795080997191511865860207680591780728615982947791265706253189537578483622509571353652764558686863498428491478503884966808196904210591832186342310388920328777013455764350441806155614158876041483825079409065785525778780222302024085659810111026903712534705588874622282993907223028248774424674295154868502303797506045981812042114513395181660282627559286830732089236337446310065762987302093523682149745218792434138515298198338267655173956936692314144501587266982355811879427642912442633549220906390869857461820437296148417677873714515537935613737996454311187516645304558928754942509908828933015684596459474134170651129648626452475964339364946372645198660724401115188841747805975979877269957347546796140859913108787018227607388057721897501258041290599904301308127841781114466670819306328374220995768910720734493975017979882823546112455805768031517437977649540074730366786968160711455633057304326886437709831267756509688268695423871628895187717588921995494089219656500350692878035138735897620508056492819898952912643265157008939980314478916902035890760710972401278705217122572723603158818146038747559530116863451291784485595959683095031890389051057092681709097418088714055762177829942378742500705489509761809262015535762475973571905370839424752046285385291958421144419417509576152905050942992378343673491106963233250048) * P  + 7090136539409121059171353052532572698320615393075051463840968147712161378737568041701233047351694687415240467902915432430262564970542338613850509290674596741082703119246261653573345616519938495381247597002074734232752714117086633163042794331649181283943956850699455466298886008710012192745152896902760424030389591247120995050962851250158494357090144749914551848716047893255697595735974385690983313661357045562404699972106500920749506426569679880912042389598912844035830880334107427094439867918975733453398179493471364417141126550333765093807422992690905549490451157074888772911559438197770076167168521088697711098842005904200929879506295985070971305058351163587366552862494375556900196894438082725411265562021214604850504612253052627458227752029162812055011099780822358193552739977942417646318288738252085843866560017391961410933347000942578427708098470779887965847468673780663756551050551560016245177994928797344049042623095288575100156016366334326662396079458607222392514325352910594736913410884608643240087772817158380228301785514119237345663258330427819100161404515055400349636926407861886568269944887998128099578246628166899172576842224278462603440062435788493980180758647480045950385874367644568631892813287832374052084733152955502568191962815353487281904641666805274688632032725381285392331848113661893402042719702101526590634338449908198355403175658994336756669524229376) * P  + 3438713143926050284513699734254667671962829258046924507732068932403485492012421577133598759387577218269110423582381493660464584333436638429953095818838826908038924990193254290571202610453607920753241319432847777530345416822654437371662125726666153492952157282774572612808366271057354559264276036201985704522636484579831368714665115875877638648513356949929816782789344299569302436068056573987853154046337473397115273940140440092218078176542077043627308203369025412000868682986033623742685439006806139251792239641034441281111895085381857401235883237801021857982489076370799703796151672938982737546705516752700445960762523713863467225131293242154662611654590918146028034439295840926363756817145818260888714888101502414035784454696633093810385233936775925834474714178255180393192706401050223290326127287881582789888968427006192082194973732577564752900082050491998163908525684125909011203247398096264669338841853676494209297371285427538968875659897731087902620177501936683588989153600253437396679737522060325608451768588436390851486926502757736129619513599204634452877231909238930141460925732915387321317866276150730940202182340655115088203853563148794997704997818601809454025246398498469004976501076973300359241042668805194870625314103360639629178849808465749803603735002608537881975558077413215933698653369847384820392041240788369404364947714656632610982281248169404073148062835200) * P  - 6805114141770789230319434666094835411967458545132413271451888382115231149148226877857249071038086234794042001587895249028407749331075322798153014818477816334576148822316854936068947067822084463412357715517551001531016574599295833273886670737910328049336415997563957351880615681219146694306037538512178829936723803431629328930114968904229601419574912505683200982783354579673244816121985628439291202010560369550606416631053546374672469293386217820699179582600800158950612176531831823340638759256941539440399744677055787405765063107634808970679624061903263069665417308721502855140506011567819855724602972693323522702456892878074663013408256280188308276281698401170762228086710410021735741553170058770628804181975234591639844357163588680843360924449208152351832883878491067355376300569210104776855208435159733735749705953497601806904047919492316242773271574396854380476127709903010264931493002039879734357731469266767395539749602128448520731753266212284202572135043178117533068524161880179112530344712775664565798136292416997457557008614671436632553282397453100455667488004688170663565658970636117843801301194342581682287262972830742252731095552086089782331823532649162064782354171506487672970395092590574783582141354136310862897697918936359583625550430977635244019402306455764023261265874037781539939449953711445743464127928772002212665935991465006883479367489072910196113352007936) * P  - 7267216763139585336398777502009983352056047750504052329727132223507173216058302632529701789757780970901939007566347932598778587493488444734641279360827683825127430591348728897267820199392318965158998333293134706246737408661782827854524850358986495425419528847329033373856851221915469250302421967535616462645861746193133097289808093063458599369800465188322773206084523935222760455626873057436536437575078481049181189659979912829826277977321557079392770803938423374469230303581151096089817214961239974008604766144059853222869914528642455863918311507353534537803504090757123424265564096487952036300269027564976201914275738943204199862014123123489894515573625250833515383608567222929985082652930250157573697429712014237485978774635443318336710869499255696413826628582554210546673010817106424382117455838013449659175438301629464746934010500180868110063611222709677440826681451207734488732418129703492427439800382779929140647408028087546279259705017412878382121544547574367571188916432958343200517588143183867616259961360235836301166778884390190005695551259333872137867330962887011169055740038522747161487835420665062428801536072841449459479162518748468887444591395793355460817277660047322035831862623514442206946616108287069241499238571261729473676679267144031777137259408096112963333875033298835477402074062726786876766092150874352810340390709631119818697176085737006850486282708224) * P  + 4538310255045867877388114692453868053492649640689038576453256597978512481317916314583670290575709424956889160457405626787716370925578627560688985844670566817943519956452409934982857457525627265320185479305268227881919701327576595161610880820017540251685204472984183992199005133474723243395587984290017944557080116748582868609135879660677710956032000445668964128807359713495105316241968437685330944572913668417993639053819702876275700775723898824081233101125519312803660130806226251930165282065761434387950044861033721614009330775646049699507170370452420908062605124177664851064191235970865234859558631829528697328490955192081965183725187253721140386032579430544087089093287401408678528068894824466219390975236224598065883805133565428180656936438009873353741325418623095629740715954782013747918753011291452505350152180249445665528966108835407628750752776606111434285506349122792859622139380543743970409358091485532271219568224584611473370624650218204241896962090961368364595443544194167242728354994804240423801598659741802323592415644752591815942043486061985326729351467226501426472089888647127055309786983279440428175118019099520963422755159397441755240885210594508105458308982905500165078196744937274996244748344935675507327716665401702667709166559255313693654049395848833035145382376307418083208833598849074307732614572586040486438458610786662047307353108455339738026367834880) * P  + 9529204798968475790716888655592445487856216657428929491609912885924541592335710589748459091054734001553475144810652140114401332364587525858562744247858976139407904059471492321331136994129071988165176713485979887044466988463798220639354765176784069450569781319159333055344112616160732274164146419710886862987544293937635582612823044598467464768186460625956177619937920950154203812376272004117814443896389588161379563007538686409054504872784098041500440355828019358682512302961592045922270062411063496313750530612900029908765739148932094646606972900159433096864682486372063067282588243745903781114912038099652744523316335286723358178647908807251463633045635731273761345139738116112423181395769620999444992109792112030302348128558915265905974641733450198197894311875644821897288655928077160946943234950452599788685353446309209147240078745884585538612622782383512464701744490229266635295896438271163163906521864536395175005082128669840611959907397454049971983525832027798546502985245726457545619285281767256668857883757053491585582376875389666184348116791051121967874380127889829735250377535637335750962539720563996992379407837204735506157987470862633995768439670740880818722292452871512946911057037891135028934602964105687236982038462166739459110664573185140828168029121351549669036992868372157891974475458832268181599232727256791442876351485791346188595019423804299930975203492096) * P  - 1519866164191739436624680588602993474706308567862405909923218041067425192246081177138147567226001873615196468292964592991117311023698671968372589779344869528874341052781696254703206982643612318834008348167185648374170578434674174599243247029432900248381585975456958107424368630333006191197098453896082200799050727184028885049107289042133292661619899708799954300594060656637845948607332156369262045823528419156988591051949645900759871046340224181859504438416142978136778487596039617787404571228999645656867949080889637117013994855276428637639674449172207105412899577475511603826732829085280000646640738412020472980187585184953310233007253546048172829027688296904160995363634978467722064332789148835885632740653700905013465223623886188777670737038664918259164553300538134597086847553566720539401178344262341253360910417086275450080464804835999100628745061163789986359391301624767038798839388549515616818401947893129477370887557241795259376306826035930813208041550544791479246085854955375531018779702290177935154656544212890415109941263300161951080691700537205254040557544467348603440145378491808276863470789370772252521872246135127823036675990080717523264685983135942287220951852218036257174532239928339197132542516482076502908060399357635321333773389506525451966522189860642790466403782085954548127638232836100795126537534900482853739174019363518727337789063567029980415158380544) * P  - 9636170400676322400900384740345502129351044208259549378001434999089530013259455944635515611716027391312699987457306074364173713241337966829467998607438021585399176700095410694146005467010697864388543540181300304377534710365737146260845108539225885776886700635664461294611790158713406526840698849080633600462222174408514915390268925595589586328587762617295793315846322165662027954136722143839438945815723159689408567918865696769552586799209751471154890750391269252311063423085185461955570758936627898092997388347210855244674500545460140638232990594717181170743084428094305750073800293996290755282274812830297946607711854379190997791206473693881038306130199759770250728458877970594513571875130389712779175123437368896050762501599298099974021559291215998853165945885248409838386612304670324740601312555687807117803587038431499369156019726553050052593813552494206942379966120498300219896090007364159483429896705881064382939608423833016143780288130208220023116182779460137722519951122160997406362805563360811858461319560358261377389523304401378432209988294679186012119440418276467894124884988962291256893233213868811985296513723947952260651537567341176452488589632482587063365889806005027074024803307004875478394682200429094615908935246929692772183455650345573765393220839353736583385242436191648823235909128944588778782363309290059738696926579257531569904714167613060601533058582016) * P  - 869517916867284877137724633143596642119428769880140497378812037143790182727988731161202281365404308582165828601524921895025031241937508985512134982134959986012257585486624956863853575339411747848051114490479058240458746801333459837500273345876161271474995536610065743143405705922009940900591604324902909302702568465772505902117616868671663287833602044559027837299135642769708856011388519549256406114599892710403671480592969359289640862194340828483121655071103753725577968899067044769141743695555793768917571954571187592056099894180509258368114647742699788849494684843411026323695721503234698410608133157365752144764776376510096416714781514571103893669371360133052753587600904729763261464748189611566237144555814408664233842548805736078059400120114451133993588218372848818682494934754836679956680772955194866534001275863263048630153211272753456758999753647235264299966037098174904460543733442645501152890728224908258361874189438322717232947161747208415370840694765090056806654235850888136983105224881995070274538640411590052691267697021490921542824653976125331973265808788138483778082800104321503387466415735866558987460853281300683583575839386859984233548276616374876448493707210672521915953219084838396326003421181370695802540566163001680945940546494193602334152779143281952433270464209895495099685989165793835798155023543065668688671079024452145672217597938228967534047932416) * P  + 8076261337229362212758830191336068656704568645048913425386225000516723441443280188330915406014307064930622295308762465733139228987347174580004376055726927403702528996340560514146206262605032952647782411854430986974821499828939797850940871257303752098845030908239629616233400403966177604052454094852736509806308325284878018281973797130486538022505385620976961469265367828879292446696037650732551351551368096289203372633352655499985562482058353537833366138217266620853076557650771942850317445070832591346906970149480582883106964174254860901783798003627449740425833505071144523626547741797075530512250618033561711740101394303853135560029858921250691243109347302975485835286833835341597484298071903291292645846964647899502405340533303645578825476503312634877239024175176796427442758309064072152661135279302703963390539487824451975709681378317762724289849995935069505096110125057499411962818549129603830097926790532294089403734613610601606852916986260631295299216211142674498634762681460126627631347239831443950064889375671899703038987051867953886292184758368388896961160650564400732456031513972037884536368090977184706065872501577293837363567843580943535060065299105433140834806639994556089192685679872632154585954665757162125693508337471055876207620999799354767792886255280590574784922731765135545030143203626606712294107502718917136327468150986903705819422910226737338081867913728) * P  + 1967932054101846402518215273939084084618143380924943620295704496675053095815936600534610000652888454059347530307088022548215655290697709865396795936967444470866091835244499423238818998983375336866196010707834396711000434565884192461359660214849463334059859259357000808640949506200285794973806657282359110802385978583729133588999784686991065717131405072049697921412637037633911783730555279984344122936325214684090728467147687328933225554071092734592653035586101524400722644388070605385605283660052325378799382720597380822745529238829209550354387011710770357237743835487722585754095624946799146432122168032301890522664416803485521817030630691150578245937840185278064696687614113612658090166801190901880134023565943797413846101619449060759219747661647316836873788526059674515161321716913577173920753934750190188176896124992508336961280573194200013490634239532581715106945384105677770586841806887367277116764643463939791620401120946678459607404855123119903829459744040966881422424158724535504198100414043474664561552938220026333528397953940873610741709840403558769171855611271226936945702694831389378224266198374488483643659948638295030977528220143117876732616039192147430100878859998952879654823459517163584293946221890562591868701892149730868248023661504540866984874519134869045260457186951081377370809617767115807943620612105753353525902377353539255557122191597692604162326473728) * P  - 5819564110268427280204212629649657669015757510136707522136420038099112391879932402278104729866585008495304889235649383726615201745292217233958968768994017951861350797026239754993893107615165524354598219940616637279815113698337073034189295415974948374605081982665223736234908834949353503207172070340385443605886873595396236240424810662649729496186112313598782047664147684379570084272254382054289534999792381220181084656125934596848547357492285125718283076023030624837830965195020608275050065958519079959827806488402203368551865275157075359445002500393056625810814676389602881475056992109462447080251155848151788422234872586255754504410066065905598304748575225206626249201401389331023776807208902771673249814930793150892637539010147319178399625387114548975830155968197609871782581007721570616528842570264119727331506359684965369720544690051285346868762317077076508160921175341833307231441976113994626300732132901635137227240332144565743014849857964837474296029585792081172855607096488741721595787605419253760613873750375350868331443253337590513391434922857324485063533398668819610140236300237716997111444112277593096450286197232057569315612745598442269214279243727463514865918580505457004596413896838282531007030698991934976547176707246164976810707461514903262879984718544711627448106348717023722983734525546552056809159899877616439750643100279445286082004125126943435554254411776) * P  - 1955496547483533760773430429572676052626376719689710826067395502056179826798852716728551287371901907357253245969236263051301915388280793860720608756200445160869906677781926241383467338845903865655109513157443998178425864400735289261118948686413521837777629112525863545621932313195924987012696969216819381801678988262387266883239330293284649944089306942607521728775161643120587883527444175629493012910766341173801001963133430041169602154302324926748059049050245542827079285296935347594227277246195701730890495033240354292573526473533788188826517512895698797728954803540352191839142213284981836870276977197170180289379410782406379416003158756214670802866703815339965889408365654257109110494806903842488309015912623973332902510868713094202194404929371653947339083511042754658243000631449275499803966289443111620861868264529282876037043013786856933858669863259705544571041177455213434263405394370725487905074363325112073272397272474816812107999816481476473559665533384807347590942604212225669891776668346455054931084153393101261435441418111532589620875595456787014816680918247545098666188403708775864207558092036476937958794245296420508393032424265904587250023573117814108559956738803983985963683214855239135364538080736916159457455754160052793791496260750696788673286319908939236095132025033500930203881816346407526240399584861703901630785013342593052155270195122709948060256715776) * P  + 3682510394701391317268487150914892644704276201421874675943718898558600294168043290697289363693358890925651130053312258212270837330212994077237378261826815534072888738864207473987194396718856315932325413375997642619496113291930076117866674406276381619273957778955900902655377554217213286793203605195941126875982293053084260511741516475506703494967896279780225852602593334694700612982349912888604589241264634199802063687842173129781437596163549250176545850532831190714847409425274105291491151126236342462835950382478510319348222831389003970741247261479354365095628102708869265321219565131475646951618821828612830875255850937847587763080288639302588364719821963640042092512140765031921954394456471699980068950692277064355637183956667465596889602662080336514670806688370022485122432454905426816549997007159142380263128237772333860644242184508830042224188858760236167011268677031050640654574686132362239199258388190235677405906369206657771109742932094102897064557292860799159556486520433800466783552906018012434930135914393648164198016122918345927816838386225111516276158476189465614698096904594679351562808572778145812734862989548703688597043087859817085783625273544318637516277055943622622641221672280679518460871526193988364616765379494154575301371470692393062626514713381050254240835321583421398865252924185652760635803461903010151855522918138083210744987915420568111758367540224) * P  + 1404793901937835979653964854570356674476307511029218192030726965072687986546772454283644706010351006904402889340612114763922892186142542367222640682678974197658268096666557783150228982535643163890148645857740420921462301875070184934522752910820167871982297922371052730343777553460270376835604391956753220646651824843122053609012443114550691082701300167716738017211738591322882249907798096138262823582406494038354473524949172485882930090312055371480624487814908395768539788830239163094645267327735397297048364230735519660461703106458931658084090977134768267378513011005843008599283372591673048905064819486271944416581662812196184160165666710265491208021232211921650131522081144538673598843947058305018232257237762331250788083201393419977272227738349238511011216119956235422577949639958203564086633776520417919357675969895313135991857048765415998026939013439439309545384020802536954225858752032278199413238487558548214557180990900466307624143861781615660089262993969234436430239639285905830893784514889232031379645609204795094256508268563226261106060812480479509996564745853107816757241345198536622185005762728653498403074727489854420794908557350786125222217683898311776479838907612414962022567865919265316551881582411226910889295384771659999252659998418280718162043051804166325992984119265602609477537815245500854173560771254869415643979256729786022866818503766853034683768850432) * P  - 2068229016414353447345359149476729382605670115724125502438936773493775347227750860702366181692556822364699712768316912687443087175268109860850953600426508414722020090484588465943949889349384939506733726120905567785546144060705811304834708182096402223014291805252557163307056912640331233965865625835019893388379676540630232664730115730174839265041245915273680098797447348838365948484506572712968227556172351311925061492739865907586117052224322635574741866221145872837018832504664839127730013467518469732025434974812275157782107863614917526516658897852988545721089846471931186508574196171962700994439069603993286913523113645359527605717727420246132452014178873455206042604550813858138499587285937399199799500873101351577110147136718485816646240079321889205226263023756664684086671074260244591762347354457161790613513567312616454240725395965143590384164035177502883084292763847963174026449253845896586642269443214674503320037401382128902774706392935901901154982879122409252580571382562911725722202832393938967884670784571531950118930810377126373522272661560700149533896711123819681527428707325134404146633931459690679653405700817979187404146778849588444568897818315812945211649475068444492836941960159392158613972035074769933241055915249268144308314413952821519472849313238564402904389362868259186616084102809148975337364056967695484280543907794152889609796476605919103669064167424) * P  - 806295113392109532459708258210567325714293654783943173539519103812441433926875552446326821097671054862976588749564120790557575879877591317371725874074890774793636974246760929186256459723396674634052551964348935737778940288022072294209207623035316289756909786225434243029742899311855579801015557897223436947850739779604180582241223093428751425827409687520350015060407405190714459364456382848314815645560900213789077289268727215180479917628563659583618565333805937551291887886793111414658373652709551855765403045242705695077532196778488378419553425218043825966641753988191629808596705561619425640946740123502942177828775203972499909241236636690397745405898740506640449942777096566066820089574965200024342454440482323596600022543664278287252977873602036444801757198804721101417325306272469738812476019721395904516824090608485487481713387604889212619234423953082874214076403545585670148377158722043778757052722315467746577130951510091288151726638863604142647086511916504918911490899466612872162354168799591451067615321444936105538677775442916387577572195443322682333748840884031861203914212598371036338879585857576778910779619853978870763625306065448638235845017592129313615202096100469707078139198101424466822887166763049786068522740155187303803770734713254866617761739706696914179154084528119110734367712677668300035639147809798831775080273107690529828346649444320639839934124032) * P  + 1033310748061391469638899240923364190658200209059415299573195380724023907238913988631188802754638446422284484486611928544866716903902692204307228141864156747693452524960425873025950959513029864260209842087927111207366375878594187710527330930675680386736594315377633913252851609429554462156146754078655731575689463751168422295540466476305127337417661593231254710482546698726431279024263098315391280804671584369845552869928790187492756537504135306547762556235346826830692054147544454469247001864005260092813043482712235348079792048093477873553202298620837849300148816186487593346596750373755194826605382555554632947233296923003112052725931374005816194766840342526706125524195667909118362301419804140163919468373527342103937847647892037181942964878187874696454009974095357721017463011074338864159523670435750203655999303052318869462887940044502590268778360908750304734215201771835709849188456496840376021355756786432589909681535243871556288112154029501151443162058441639771589859469204314594518518184981364283622466786813130215327881749794830306985100796955524269932310508935518919234014933502930213509515310069699031782466709900343513266338274282347175259132052205144240261684751516548117014986052892133275823269819565754057599213347670250104863968350232790228293356541052610835113909071410037485465453708265539565339805042238300521684007682685667853308780866320568330427894024192) * P  + 383842439582681112586501491874030114122908821753670898976065579064649787141563693688500731072352143660261141062450431754675546518959310916036248247557198233818568293870774971216003845923704832767856128278288512156729986829077197548969710201390444963191945084856468491500879720528301892999412243011711899467616735757750202872695850345876624715542332759333696037635648675486710538477341742329582752584780657657868582059712652774957452111428671122779967549402105496975481913573943099013817406458204167869789697541858746557008449773939275274742831464221424162583341992406479129244773700735285030877175412783958002661390092530064609672834230958000176146513083446448226365553564135573195752240880789314852555895376451711429502267452503268974126500970418977637377720674308094296730428081906479758310814279279534870937906451931167313433795075159362030357797471892056533464253437763960216250266738654000166989965198421255020062484603373024240466559907231630958152153527414220958709691823898464205837875148551525295821837780482335218863481464327785796240515059357537706743091692612532590594093229320142448940639350183918048269628926484142287692790215195820063279706469082515324775110109490060267356256365436893717741401083819745732547174523571035119532770766309559034206880157409356204019592238398682776715183698125359607062244920128721018306871658674312743858986323223130649311548641280) * P  - 457583668215645387691489506034522599342195498876706842120368444875517033048261372496404481363871679307650385237195722296852878582555802017072645900960511615217262096569457496929273684863855001647490398369380102457872498340939438185629800800138960116146104784985031801883601125526120404874705491809707593106668726299498916196712780319530104646652843446667641113427998472463084577417775376062280367225577634873759192632765518041274516744401221475228626733994140100158385775708379809651737960527284723323106335180519371663712882575566771358531845987844132360710642557556809767465400176258869337203100647948138641513059831217029022027115075302422605327818779436971265678648583956804451059601638692671878959001106069146510082288361650182156808604918271941694961634633281398924309563920178312818889920213171411688853781048619875883940350403578775502513888040972929569648923512196436655218699559469042281952210136111372441419719771976387048503617285360012177342337766900384447767137451160957880745603027101183623756174403636369598521952450938648476604999800623495490108851424718036018463512913200504531349656483235520824992896274108369875047449700609473852722635836123807694952415968210126278561876472514518716006185005634337970101692950156069587366434924798160991556347158780339182123098964613576003168905629549300491314174642752113075853969970433889026612642588003315113581012762624) * P  - 154180186299014645674832833137202582075644203907867418149005713596746137775965826035569352056305137353474466307660645530200005825485096198871152395418507851312088428417351745367445940787382533478311434458515182046277149847157160029825611189558703454140348241327548399479434616032712340955276821973327949978528262025608768641445953188516794915547999175001363694772653053657008281977548267364254133121814035919378846024849520574248202156922538084387389540979355167560468077352512066251606321294610983361810077810309724345843467172284874622418733995810682178427909148324031243850973227755719014920992578615660098859990216767794640728658200659444448194174631479816795069323444538381168614160580390087849189662361840006764498320380754946010951411359681100905472522682247322982125973157521578409639636336568710093852044392360759643260734287252979272733589793311003484501921393955014218178932364055762681664928520069415024499696801691698517964501531536763747480853405556354258632120711474647730233045000388888408611207917182760634207243788768072524338476012811741380828338583014498182903128655244952048047457737621249698312619409164023295125588091199905324006960633828241867438514469943646265432395852943696282930782176535609883604896018681396317385392852430040146125956002627898782641459751111715629216621137928448747357781806970405569067703483198162285197801200230184373300315242496) * P  + 178430641945267682925092601545468042039741225859892622738895524234653080588893992440543921664714597752308314553578488607520314700533773130710926211356206698629021680923302337215677974705149770530872107253050126073506996113167144237514352512852472588755058615855454894467122482038649326413681269429480934273219772957450203696036635177128690732955052184944651905205832089030960749367027013854927032334358394803547830841719856520453526198373109101398772739768690261756847709757866624543759161547790034404799816899199014870840876416148673112759295190507092224273379562900837369921921995046015122949741955999372180946111747090592388023144930973279970617608959586454121695283596859918957112523330906318376013234628056244390402543880430789557172778429561418609874691228557107899285176401483183155672678219374436703247085356772293521536700547718921562029184846953449963119222821904214144203040615544301337781284988716557058933517578902922884750712101224770191921438780361908355629878618012931797957310075872016775069901569759071880995286495818611209776025547093334602300257383454094678687068622508058612821488105556197841577880837975211784919208637443069433032153730805603239496383821265796393808208843760504069735761355631760678719045991626281140351695203521974538976548051697793909244130262817883376992722984453846650422753811040914279874826701574036446638459575521421836621490749440) * P  + 52698812801854270317823480003258790845610926375578449549836446507845477210311663823763262296544443332812636669245590822176773546936686925002587380837079881356623881744577559418493487871537647453523435461575917545824006554620821017722893666330593890361506989811175746634934901906403949233860996597816249660773611933253452466258857325200123711281386290755588622599031871841475268942814994244564525081182500256200780392001441332224054945374069502501409509047940180353210149445682922367504619999845629009667226475988419569475317518391952100689764149210188690475530714475535728209773349338902958736311000585995456510318376406240715241683677432946741879934681881972990729610155872827186873377349292639460376136833125644052185943433465801165225440427156398754955266977168645561369741737773136661114752978643993963588746163057842186373134647595784348209029729641020569472758409212447093000982843622488571948553400165987069261182739577517872451767526814045526907705535944033153353751435585952544747229374148678064201228653835812917180252874474376776462504839410141643278724883033447546911666747101738840551380947691588547931753776670707591692807764744820255468065105792810346343973327997564966783087708177288487032753011453245304718676749869740470178496907627773753861036174351953141766234695966040474958610543932910475402067598497400354432583807031357115412674961695607585847849566208) * P  - 60801676936439879744832689927086539377875996725844669148452572306303313909551124895535514496717280201075683122380074607630889800499582920479221495549875992996056678722105721960524336322365467472130949430950062607591402805477586861028332846539175286848406049170975092720901489650750445227769162125962243456718349110095809551964441904114711956992807246227976504684961792332742597729642210652050456224848115656765713261177653939726614085515801436395131049262804465262477730923247304604236416103368388271104246855615406467958563879223790899924448100739318322382842587849942230480182189201902417290810813705762333023809251698208653403634278023316113191136013707879810677108198009638852620903549551536268593208890354841602350844994871580778576389221647623411153156947711904104760191344730417985713362621306242085674481794380810569899958417877293504769857978730510639626547771090750634902673423910245496194041679469129036305994013661519854133686451596952117675076020143988317287219138322026960721088074763314359585668513394973927774499209013626485700541563648477960454399170099660734839729042460649988278116865415086592793154040774060242816732769538304835261950816814171956763246035729657902724930264350361653333925428693619159206798865245146687787912157948998532082550843234360124785018099045724919143190793482516782393428164702477751195096954082649102390155053505873949970997444608) * P  - 15393765515939999811210687596470606438587346413099300584947875823542801593684392592118872851193361329827142374922176884996629666093109877991126806889012546360829808536732994853530602084022653868878962618226121462221557464084065013204619340683868345351820883067453483787572466862063077403381300862504513321658124723181129750836983668467236775512950769800486001758191531335157894655614649529076570964394618681278335568318721349143653500962548893630319902526408703198530748068329478455885321724060281507326364474340799102961075265950774224937166688676556491563470457964953336876810043650597265885626403838563257468723255952660645665423820234704667872789505897723226912017641097616957768648559316026535197480787054076935119806753774614209748747507909915017014551095996218587086679715819177154347725283857425901435856021110650620368808751749111660555011302628018761406829289600711824538720823781575923343862076841885346724607158177131969841348103027362469635334869915974018537394427495185306281261095429311995019688690322506453718364611764315069882141123881651258622983647543885436592205100208026426191027260321637526909366572533555449602000608675608624313282737481329265573658665064027798828556202762364477893101545310481859718141035757231840432241015392739587933152870453799883454313188153520596032644105373862439156460838241913604330103979018822906883825496023672415144873721856) * P  + 17938250456145569793716112037810117917335705566418732120596891835897709272073755930540439708708377207185447771177072051049968282601713681905845367761735521720271712403498815868315327600479464386720021958610394548296909891391170975783433840646480121182045141809565161730277669684359727326386011511997207578761892562506668729159875753302927844180625613206313090073013913848154894161805319384346017694378124402554885863219533230838461867750132814664049004351699244972845836071674841697450825953137354957706365416431203439413572637221863487394623780484735414984377460784258918984537396378420045169625067382811364079192908006110182126884078669315328583726259546635386444205841638336213430035857875992852523262291701315712771564511048973230806343508978077333190517250368071607979750526389709923705753766471768102684120196295758072999771939211899242638319567089794058202105971694527642923933432282774846616049234873244838151851176094051804118263233744556029206118130770155494451888192224826026950982616374536183861261395044290020938579411200406874105412632670230527972952031376201729228012485529418892814134371659946053544831096216129871616253027991988251274032963832060944511997498820742114118701460113570591458773540784392593299069488738347365464387835655707387088534613085033946218556599881310267071710973528082012282848370650324950049764029883662541626686383508787125238312386560) * P  + 3846889440392686277146486153383145560653379193905080062713229346644838982154044957521160517048717951614770955996824098757897380787356544201847788417534238383132012385113638848698347389687557133950800695589061245636765912956858077372826542089404302306702717546755487589999774628471974725579200540168286994444690275909604528476353462376002565047424697357956705732346243311030173393673694194937429994547231523237648255040334084259195862052837219292951142162937763439220518048791448510777151352676440926682636479050432740678154433306099813251097679042403558124458031155036082224402958860113939082954532432792540269175026305229176884629289686373302039642058523643831860024084888485377869763639774334826803607011596758627844001798834338094314020872136539723098326793198064002794802482526537387181989437518078203504803478444897921950999274285534502457968127040716278800123351021384914331269376570454839137553949921926775372245153873878360469728671920209392741406885469610057077268686387603803391903794767746901361927321294746554966546959914129456514329058532156408927812178485251240242514541903740789571065198781784670541026355828742571849584044733826179154670688253800151047029813119164935466299082909040767043266550996300211300548102741212509767925691211085052734879940490760946588704196840466122132969219641182665778388834477391768772516155643564639337191798286971298956538511360) * P  - 4515596677864769269790393610519737418852655969878513810840838945533231823867051332415075670507024690643707996303073075056443324752890126009044867322115848325098516095415339522232543332590030030357557868807373824896263685409598365856052150391360318337081339846047031411664352804452754444557005305668027606149682641020491242349491161898707602636761516176276505284238057241432792954600454298946413894941516032567257563542209017422475345237515682667703440619756418067184857391487655058417014644532695403373769625947566249428806387145193245810081834601735957145818371197126305287030086714232059925859462558243650798679365561882433222303121384869230103712776697890363155541690940254493489511144011815803037091562059016076146750114950489171860944967011927317495267133027869320418055105670557178199666212951937929101482959394564855676771533957325930716751920764307591037170198545906768674111128171625047180486643001712197993255088942481146403843340896447052368199405634170438457166271033040168906324390968131773771776804187609640664276363131856306503814851905121856732281707160839235236428633197105966147220955162227968966622219645986915736632232382452107390452807990112079030247926403448426264763192740412720691948845615728108758315392523162594321617935837059813311242044000075032720228360405141330654656131787069599964827385060974860570713619388555934376328261685861713965079822336) * P  - 817485642083144145314014820825731875627376863315693556095100381865162745635765504656759101497249837523481625629440636176603402590188232058998812135838556607840101985871746979077865454049991738140133174456040516860383797285154283257406157135821532126735893347467306947519214292662254102542305659698604346317411036762054824293128712444117467435250570410685540939069145236486842253449874955727556623877855430750043513655403088700401454358838797877865682189739683736701731382823640042873074984056253387746851418628312619852296696784136194191409091071821547615992462377248733886210294993716426038538069499490117891201442519494195398240022397262967453313406016411994591970013527190244520470039895173776796990237638549991637604508867980181643471767880145564429906545910806702010522161182320714275161582417634872436680375469027850112399550137572871988633468882193664058939321470697772985437861297433159556027156679466180475876670464252089373385927472338979469804594575958711942332044461684536990465299212359137497185943420186048873995214620171092433424832037695403884435075909375056676678951238524555604836681794819073869917649928303505351769521180805074638083463558967946164290771717468027546259118840189405744038888349245208642025756874911997418560987442443895192091328646244740585093980488189930642691779722402216522006285159061777172532275586084439466295291388297997403572928512) * P  + 944787049552183946913083634809774767355128447189149364161465324688674921781198641061469896087608494239494017594325772251429337636766729491942012755101606382130637441371895520285268276825240644947803377395447286795380566578106784886100036319011409486254004671094090255560346047611229819269487394837403123147066211725383420787409915975766426506536818800018953842069245800345037967969288136226791920766598684383032876134935531346184749914307365048079766278508899296111429107620848186257338383127297398604138816968397716892315719664410470578430780159715586134663162749998947675968398183159234829466019658415824198076271740449195623443866335276407947059132670409350296037798181947068760793901635245589145288723905179553424005746881916525314899382078542941174539560464585298078192292099716793610992196887598071310211245037847105345431996291451454810577981612730551680304674868473806942580270863741825232743355772477583939961077941293586434175938875809867206693953497422833588644038159069499774037628695301982623581525421804053664061222416612926268990592246568373903222322796753914358252943356208482901519635415252590094934324249090222177872296790564934817330403336494014875535884674749640423839171162384174427893849798945739265294311662799785505200509194885691343642699894562667345360442437563301318413018318933605365582023023647940355615722536233949001472246666353689947397980160) * P  + 144406152419564789784086676351391536514470012957312628666727855906725140291646975593411380802966896971328853554302434333076564907217656356624953319535274221075614380921311624431473055199312226188734208789840740366150815996999734939123591558315698972438603987421214971936305524323599459808420753939198318544622446831960188736550956554179425262665293686264757359425822130415714153307514187488788828236551019661030607598400348207052359312383254630042771144320614856081934728655676297783145427912055388188621356969934619010811650758646602499196968931682886933342538529350607164057302727203167885477054020772057011813013673677763483267430536902414882709434864491951390491329689285357054087214844419617576599205024477768669803996585182787768217926824789436611262138168129462245504270701032395625874538634067479066362650849963276292223607913489988313010502281686207846197006266735495315997379558611643738891487712144714124458793990229983353957596421060150971930573312506190066050422707504192106404999998144514510541582802381771766203494593428390588104645030201911530056704655422190043978267660072269758829466813729544036066313410796736588604059906009072797819746763189095179385030612810098084000949170060941679007295910447762913555072784070754312267866092466597788814478931537407590541582136022008328690516397513763383426354060898973319458886160091761486282850981822375417733578752) * P  - 157039555707101750643953398222553513597403807173168508597516391126961372908409596927433624978516748411969798827253875776518343749272690723108311178974080148164268235997135868446126333237380325308711506358004159335827922982407280218131557222926592918694342821243976922275162218638356514428511889953093987283859673180431857366223424328903490894378231467265307278654355155805008079172233767471827173734426127529849770786521530153293295576376000888336861528799553925922655606033899244516106500106019433134272166813649961102780026817943420357792667554076032770153464906339818885264014883278687053499424551347288448345614282831283388441539197699216169079853057593116955147887786496637650443364854912998901591191807573518333932014230391162919069598458279596107053317609713343964398244109308907406567646861875456146361504693540135267995844631112959525634224614516034417802151391680598873869018115792099783211047544064778105315920739831406211782006004287336169719979115022231684184569015449485944464544011203667493831481327109220583189877432508633459717385039087118148533637187001428587748045964191039433692382173213761644179499654293566876589124806099110359287757971673353719499624414934488706317321630681036472620990335396440257562198048665321908323159305296309574634625127647062429132973615421192171397420757204737653090522217806798537673133725253206780307354180542650197652799488) * P  - 20112911688159790898725806867107662580164577638095426343080210691839466332145405833243721103270407984288086079568594031441804764350029377827040466657576210184940044087820306235639358270515660626709565098775069241676549050159671572668340521202434720274835388805291620983624135372838681929968274426379513947943862527339490076019471996609195180836696158428269847644422950806162383039134357329196011147069382486914778834993328403201193226271066716828670386259139146342838192582706381085048357269091336794088663023629597829757548708862600619165420746399969110103164066756641079288135346393004118123594602264512743503345565019318151702360744879205619288559525423237449432131058699465183255823573333629754534751368989627056257249815074894546363722221087808408105399974953552610930828251919171992323265058235877882625679148346953102731240703861408922069576667839317285146966016314116705272041731821601291991735164124166604524138135926447287893649226272898228814698254661469052647862441351124706837918124642828077663558418501200782871812356740025287069512001278461105146686377387659971955973518164959215896735504791646012891148181067828659141714727385279839712677289096764603730165155237729720317129269188673212295370735628334702620247759723310227485116855688365179623547510801520923261002808721381621026324152179583916864206792403196961800470941105432844691122999011778994527272960) * P  + 19280717989848580582496546053850147711676844168783434868281016231789562777601709779501416178157383601785446404326384444619727519496006672778217289048541284556101371702690568505610853069031458641932206310703756320619501989777203672828087431006747874928559246683585211244713411624442727330297600326266519441485801737436048527529371409603344133999336206271913284993597306663351593335360653729917801332078497886546361972924709562007195270765785389002570441307879392357667111670932300047745843473322582088614372865404851550412096451257370532194654678925202916211674509663394610126401542948256423817375391976473280291082233914967530372239387579281586326395921998116217854134616171382258015162488659953291174213272710614944476044972398737488367352193535855890838300596825625189702129093994291435663880945360679841245341304463330220559966599341274981573437978604137206722294964499810088281950157125301674432778154152879621244837014478498554508744670386286834946158583496506132432139361059976442820129850339499986627019924551708492023610835716569494713142460722313788306920670131554406864499592387325180173765945125739308235667941726463515993632937073530310939974496389040339448744829511842861097740317769259377609878764182669033909461100400710098723983834845716449625191213091306521680832592919390260414143198834064699929918020527430746228124683510441989503596529828106074592116736) * P  + 2002414916645238035594407313675326263090299200541108708646212849379722408556771192026630642048990245209986380241486561716793401993198870863788602406261055716747485332567820058086622485964643512115490425086573336983884635860228608030038955540227774272567073123689302773924386880447661758153433728795894053415703867157258941654355132028328333757864588272645477384591116755940962706631377541317012991267126081539199303131089957302545297352336140043888166919131918652326226368078870685245253566265779175488161017050867629308453976081577950848477993778093861356354123086671472772133854679028297222000247930489184376243632261138342122576741753811322168903287698717666991595721606685225267982968755959150045573687172077373786463956236773709140864675576873033738443675202156066256943684888572375379938451371197919576899228865611103487058602758783854456394305242879799189911141258603293098525693349347995220372808483310624133299368444452651834580262960873454368678344764467822209963930835670411144039302723090317191807392917512657578098717221417457663147775999477508019948025157973689376715198495863334653592680225565952792269028498762254961876848156164239697326483992616164810112784346652976625800111182389064197127736337220073545112700315477177904622962374345248188737400418810432866382654024223004240126671223287127330271957070319031815345314929645159726089505285805542975471616) * P  - 1556323359808374691644881301065528820326732389985072457512322625709561792737881399118778261986155637767225394794887156149493187759336207398066334850723825801251022495806886289588951900730343733952867703118242105522785621332906681155795989306829213545357221585441536435650766119158833809769271925043342691713029023318041587618440696335049570724319170176595953040924426332395058991313172281563015621259101866907878376965350902152512638035076676635731435530251648014431395725530863647389743985149009212966967659101751104537751653145640287039724752466606682372268445425998252829486573287730856492894287229142554731302716293402805134986024667222869180525395624615786255936302103561838415494960787247609002363740310225803345652639732467012785891964535734632949244191994226780517794954705782512516854643215016146637754681430090758557096460592591087388998392992606904334100886180304473825862339544569867805578404678159961343030118409754487144472451907415377549875668296783694174887111750755114598254544811333692186570820778545735345145137454750929809869148570563797548580532792419265489681747726904188017593424154961581357533321289580483028351348668603822096068646438674688842584989359849922693335713550438000320343380379169842017177446216462150034552625288298350485561948606441665584464377891530421835751746888692987382122347090348658426575603094929523104008047992960041525182464) * P  - 119434953225049303910010300321974359088540460836713420743891516500373756907625432527961728603043179732434007393475832710123874311463464621260007030940060910616392092197531771313787375715918612283701117609962278633388173951199509062467129878630077063696357244397206770895527401610453216103416464962510314691244942427639911265000654315575620511096996463258209849561997709726180190749640628073990287285286038854833197276826340741310959979993702713505489412127045532643577186834951511664677371127350251724919582562197112100167699329018055564189649088792686686015008624004901562460290072829548873079770188356257147997854164258772413615356206466425360356969010031348049081438154159391772339122210274736429969073688268597848537853919075032849518785273550072525487422083192897880537995015336318787140718286226808056391394706506067255256989256048788954524898708989106127013939421367470041416196732443687352964180939869356102663979996888468672449230225147032987063740406578032831274356626438173400914099490930237821969905391414456194449589906070526564774717322831264118038005346361748790546739047564774385164433990658357863744749180012961151307101599467241316223105751494702685820225244287992707707208096395432223462696321257840961672643587395743852373399057726394922370289198723201988950031053776615511260915830224022966350080586023233668553199527444265908336728613192777180643328) * P  + 67700245018397555607269837107753372346033661928133354674778264658093123235764686050459935686003495773979068230538613457216530832773072851216722230543892686693965519771747852691732895537044080108321618893005786073598387649469395032126600498349608093859045358031729267759552222997548695759219569128647799544909489002469664481078809435278380978673426996294540439820928853436144389373795332120653248709387382812509551405655632225647854778595231733888249080758235845064246526412599809929308498115509742153290014506353448919764000516435455816759053245573790981578022150444240022498184240137991347290957144003317754762831849615939705145638727696166914931502959579027209924793275482878653427736896635815810166764222193546351603351468653071479443365053476796473182931677637975273258925117783431243238690323019661357929677229979358982234417902086178735974222584631339369439876578267912804308073302575171316163352887105021659816909015011234030956797523058973032047855550666600643192705516532540639484861664892457662012939383021163567681505580938549057913079399566747448051330038245595334484084144914707459109612374873559086767201688121377479961972835808094589142561621571284054127499104095973737267991081184780276006051042194691019771311816354310831001141312251997838756812833606947662400415192272771630960337932740157567043308655624695449855106535956490058705319035253434466435072) * P  + 2796022442659493735648283136664980478595350505305613319401538686004082010235583427122430149664043872925680235148171715653166739496453799964222802605027352811824253732611264139536455973999724474066880522314333523560395255957483442632546309821688578764754283431500295701279658711679346255138022702698040646601292270046301671221582188553016338856907318039034588458279738672711482183274172804793464685204044462302626831089319728253215308258171270803319993020936678280789296136637525649787655761363254274070272494733408504354391857127693269007956560413800661176922184868324990037033641514377494719263317147713368202489266281950803765718529922575952461434403374983352804950853211239363199958453669157535206023663646894486606784401656455350180210367464675324151764143318274358159399328172377698800434606740468450185587289556691510325495119263032683727247060552345704859561189519506731252240476905601421305774169405934176577201445837290855399064700535267164893393224702017491836966616114379203663273667042967698624412101790377436113120932372575001115097033930582939295978454501258520610858084430184127554443338466402709406636609387464194704218388777733866113217344216100488588666166602475097875772294198239516595906658865265670231087468293913445847330050269291065300122944434515638054049983359402855898028910197236554150200016686186221636091641804173217829389323094999393370112) * P  - 1165000019036242309612018999679105122304107854060708640459693927020571994232222261377690823842923175912649965823334248861584427689466162635724285267401347101886061530991600588901093809897938993225597247009984808715923011447112523238343088074990036870915544285371408031543852015053845171615103238870362109198736004349483108776792781060647197088405749825723966222063758182689773526376458988352231669913898617905409820482332264128237937175493134233417814057924279910326371139407688847944060913671100207940089412684936203233136131223837628426687440983594859401811659626074747340412159392194157252458585813669349410953487218472252714893073218334371443238660217790515979923921248755995103546212236916105859301107006165832523902071011333166082146602860370083456270957470242768065511420647038235381933937269615968831364323926330209020433452480238978435394610023296593501374755062969780421480114532756414275483987118495418486750710521892451228131091047041345137516257352406753995195859788919136208632735134157671535102979784426496649701170650464496678752447362579759221602619572980167671186715766899847196698194440246815983807133354556758711946779384390331487868595702001738724160404435709873000672048621492657771333650928598356816871696796015536362723172367298440714706449015822162146121251349780956157132008034184319442945398465772785638418896552027035109067302028946828165120) * P  + 5125134160008050252205398347767253920023808314893809052672671179037764468783188162868853541437221588602261200058589972567389890894764373813283633143009774799311299563284237797378014209192476067039114450082517965963536309924633767889258753121481628194396679338261583321120040329447862796155378959820029103693837535986157798355452131390526387273502310933700791735970211694515036870495281898033321570813793829059454741273127809539007659732201156670994056994088137711607432016209603111167879222525522707087345179711107270913970729667164980239926501754164489991099773458055001386182873095042890234312895883604430490950265044665241662208780974047663432268566627952315903508133014587603808059625520570491319745657933154077717527305095503959599901637471412975714114804220103807217747372768402253032637609626148493898030757007607975199030018232779458899239937142813832952176704494503809319484539820197388026673808028799663266539823503888430461330210147569965709374739429336522139593646960535486171668402681913369227888091569976557338425319108023399562186689108628525320532411775250881205638901632141138288409951614816895270490780280198521314790393305546385105188835006188936722148490474091188615601679784938633424036031359248573813607040879200911400967596434934141209478787059618693216429755779313309117116528316786156628379281022212762690108946732767666709364197966531788800)) * h0 + ((((((((((((((((((((((((((((((((((((((((((((((((((((((7257300056820942809506617995742251896065448215161213365312578768586270894213940217306977704021391617147831225593632941489609428298992569025015622717542077553920503903650690059806859785502621754262611578076885885413155931832236258956419052093442321770316015684249646497195567602209688322108261549950417801203273023941901934890414670785161867881388510879281990242193742179971946052189391209001080048948683138483329422382992147895774964911726854241254015189498542332596982892225975894489235654017436220226850287728788180189737246101369687796845447610404056500907870693211966458273455001017506346820452338989488225108075850592238164011467784959017220468443714603790243698550398866554843745057430136920344491804666876421023181436455665177131532690865739429414401655939145273935374074338050852856271501411894977037537335316127692069129981827636217084229101679380732952663765475925727845176738147429588691206492420437645171628224020334531432055782903152640170525229759412128573565317147875631492392937984354329587104849131406081906397913976203111595162003143059230593938329718516724949893413466907691742825738751099411439566755670091989542714665553767118218934502531926823672854309878748100723638117653290480776987724732901560645727217842029850532547396175796116156317368059256343529762938131663579482121947287627899086923820758806187451961820047702481214304083216808 * P  + 10081902665966099248833513038130486223547285173504282681780904497370677082703819722190821339852683839114569087275263074329845251534540220692308361444866172291834873059988752141097459561972010451960953515345726535383643144027396729948962956193963727004499563213582140767348247680016678424600068915303740296354478084115226372991535469404342208863079846514832155152791296331287450774033285890393882480350184106437370833773762510374420432749975984692213109304443678264189088734343357600674115152807500682010855229013049126567704914068044689892762226442958040820371069896693450310327164179596313424010129617057133635846385914959522847921687750633587104953960005035200060559182287421023236132278063015954939323273171479348731606418427972985171761107036543430973658900448819441237548117228072040648987706387664144235271119107854742727594529505710761830537673123583586852402338722238116874953695648896035602106074935965944928746071331011773078565700215352692020364638748692534784184683753000057105325648988064121638014909345265840422152368967436626221703890766244268513380248215606425801674243914177959101238702929083082382640514080737075377261477286404121486651126521246295688952780049626105396377692879640307773339521830366104315373048938261167573581784535271500756556651648991640329657335133867670776829101215999185200741319475773924898422084032190295234962979955992) * P  - 713145048284830203462672181987561930197098505621004430958159948259853725544665447083651999038525256106048293640199199880152867241662288911683817530166494688550821233216746162968781494357201023759434043828833843316987387656495872694801836235987526141664912265185032318723767155679615661547913183018507912817373522458708136403551170488549091057089874985271963187252461327249892816423730012073906172560150537205746698827464693818738128225368522711763344021074588063548221560109954466509193163142482052490376258654867112736319498522942408238316041713552550804239836278236977232649541263153757459079219144398926360722233735115637832215887098621587440410256230480259302044622565757743217633654586631655447738009398519743692154367583440001321115258576871324509762698955838635424072386233183822056462184200003402762422899048340708581331918531648335654332476605000935698630834569517872949437538101174114152005828687996682593442272733770924732715190909720509626738096511029636693324528770773578113603989477170087373935074131263060792557513699413832045773607093779245826278849958006237773387125970302650852788596924337281784416064407249424261850990804036716462557206731740817155480526516315328685214524318113321094529531821860491869869941436144836891601666386793513668948510308949197498233682932188827771469653836865746335000219718046180256575087416460221857156204885013980) * P  - 4392843847576304796943922063181567098882349947722171888071749644948230989608385411179263962610802651084795510377985150243753582225309587196729974808313919039357209824398498533578251113819199109541713678876527327808800269589417212732317178376116746920749425966123432790578068532782984353419033851085932126086217112985760012871572479516610947925525390290128090773443024396178844487154902857994674995801966353187726488459622407495843958056509719871811562497140722669103345906119822016180333866749332669318120149957535793874546600183299977079582623746279723002144936100742068343765305691637883782933397791744144773185305408453584110844086322506603148338865371413803675830673456563940535104637372609138664285801124057707942204908410050758504046234032540261247022780972776401791283846979800532213916669887805457905155363399462269770232780216113357118106141660571157714338145768230515645619055959714764929396192112396553410847210263014612862183979900685569443064146965602959452496289974774438299357685686820495221617033358491640462988257481674861938297058136036619764102547297998738279929500841446764345788442644527658653320945289560812813765140579689841824326084511023376935071637709309641093595345266159361295725278427002075565604749010096570633780861692466768523780633664616320984681200291361403087631087547845236809119166817112400286095138511111856989223378499896888) * P  + 2920403310766358291489722929987567543702013943225935783733735823460799063887539427195711860768970080011986642826093705442763084837530762370641694235549961079358327972767202049196435075248961730372587727343300609318580898637022107536365850649862766986896460003405766912061974450751836523088220441922420113795088076058088093923406193321511863458102286365164857406159053992445216086363936757041532500046064264699018454359319182534965450863123224564908352541740562453890781616440681575845562065114684842347117221542136830336153710540283486765196618911807775711696674581891699866284156990742649954760962966210612572116397828504249925537173824328202427966837587713116272201241636982669461755416150758336225882226889706374940494407615547720845850257124232077221370387458723813919266128118685096036622282333201303962296524258361142082097722141265779838700325547544629822664447687707463720995559390035360916994096678100667671652499268621255381297987253790127965568581702433489681419289345628230098011736868134602106620692060545773163172046539759986856259704536982541132866568326743790735504948029943163443730757025362909763448369660674510468503438174750856128353215662307782080357429069738878263242748170178646486137141506111477403473944078865787003091427498386825872031274250657878868918484631102984135572607902296425741181510149622302290009929145372252925464573374320563) * P  + 106252396452206145919187766415717618553941397435741859622549667928835725272247350824207636459587258316549905894537884842094639076118269354177439159776951510359467950895202169102767696801528731934394386432007746596823793706834303007751008563811705075668598702459428881994534280415701268819208927835313850890902567726233010245208882112509841674127117012006904468768175481077454160337141004301322005397699148065521290963854639257565307699907362892575043228857324257070311793744872330120182199081225675061862374895690244817336042957945795749562426109352054631358451110918021084454556583862874556181565022805440910994643441092054075799335096090738776433376781080357755737873252332373002431619573385188949502331077978384192755444371052230287442430457934512068023641862294572564789951128499697441643595254542699856683146655059461705567697246801935181753871479606638657927919710127775224030269498001247338720145531293936169335579292885497649965841349100590084716186555891935074570074504518519099120942757572408617714666449720101260330685372179954964380406943930907447109467598067066466117340354579395922523830686772802180136179334191107297371814924829667619771445989288879112250395919980888535642948601868550022496220487478375088315928903210267622790231987123009395144775937679762736606230913911617353276299531631770458889900610534186299966464167183888544229354620366938685) * P  + 301854055723881175279556259938347794206713176968883516603863136284450902757532971492290341465880241039942962114744892269010737469732361663287715798207158343052918456181541555138650854565147701305018988138580066751176406003596547175486886173186556391083898757240526673364044286566181443741656311189361543010840972740488899715294235356127341806120989293158067554738575344094347248852040277791141900427562092267636922244864975545318618787526368262772160611046771749663144366329933290512854209324146933302209203004097936687838075319505965505154385081601754834515321238574888578063911520610611860707885909140267947859395009926371664099434175075293293418765935619847364747170547464094162865085833437115665965803735355569317324825525000770829709522658726582661904585086460302774628899364830082249393528785411952848204794918366901754661044623719518308420456531975725251866109569206519925029039351248068154192416982959063269381068761873012678969252035272273025153708979790739851843766795363268980969362806821907228843796286403996502034894871107231779039699930860188802709348917182076985430122876128746901012570806552040107152312557927583472037245177298262388320217543244263699300443373906551731968218063042125880505445106103411923917946426018618635627489511425841341218868211332055198913813322292436596307536840085659835300904089771659575565399599743386137304917432266521561) * P  - 394497315208411154770542521437408515289142926626534610554792370150940801965303541620336722938079168896209627636878483311138668535688498949400028618521008292042763628412982384307689317098850604532567182329056379052506919948782500459196880184734142794701568322612789535257089041867657291860352371794855639800240728182883232951961834356640590710776050463497142589106230994863287109013581669938039196980285204839965134259230215399234110913705992272661992690007682065434122221760169963895968575183640199952859907426224278398377873689867328811536972233218670782770781023622997577728889054419145018721086193477025999343747505417226171774127417127183741797279678477671163047185333988170610168886852161223387100160974373973096118195235355043965852034287334952138743452092419984028006734592677186846123080677681738747291282229989593094845302539449475921740473226138563306843043332891661424968806541109728863464432827603467562187322147451156735075863992065955802786507380090560930631277134690979541278888544624059596554852685015146738259899432372592041370680401396823989510176139505482829889460990009734430918006949713717051929702530512365445809823445525393624713217928253718211094578029857138379793599695866619215539701142961978531865104933980046097327867301845146765341853074868824245373527787331985874089445322549383633045691298445402218990689801143806918175061108230939030) * P  - 3718319974618186696309674935395902719673001988863802401044156154243644822205394892079039413767268510303482731012979205540899239708087779178435091568217199410035452328213906032812576688783479688319331700712738729245433399612921361242464472573657333873323597131331755419428852280136370761009599938037130697787485438468095740398321706553861805527269678192694517262591856296702562948499566325436632524575279400833471043423289605517893933796848778948813475571207227833823437731453879592264532867317585402387946903669727624950309308246021728455282489623331111065378384197441437070947039874985014799752469574591102327890453518637995083958665591650318581470710162969150353035147599780272453028519234166622907007956739786116724437509920392431416376220362989302821694296393012414201012426460148956499607352249905834987327409593654190907284884177934652430287023992998962933604899390754008268086803020374055391450190588062428824719828836870858948835325783238237971718191701421216353419487711472620820023315414663400372043278059334592984023770891983944231961122995964916758968011200563922960619326436187311716787581009672970094109168470930526192304292013073917917595371715185017279762843247607085291529153890396321860368428722461159383468374526492860135438580070517538458981263253971405351493982227350140144261942079058389685052337604087637596737860777670907978461135571897587226) * P  - 5234532743652094005125820194421706289815583842597813337452040910886233572082792405892977779230971412134888752031390849957923535945228693144011129718572509497803321883382606107697153305653030077420150671966382551922048954742101135813849079234072878653234485079382312669849896806107269949712705244431682309861435330018230698102891163239041789050192024441281743812949652038072010629775403782275226048855831478997730627189288356181776122068424210121321743079648975232501444980143765053334336575487221048868771194106547339129849857751219483979011959770652694716534626284413481940644916972581652967598426786182201447633906812726007652566829084181625024954101671703671991436420192968017012455407055497706015139870634320436591901279147925885287400109787572788414228300803678147006119592862694083940590249789052392435168863288963792143149674919711070970011691021220773935895181956565614950694541909537519895788218958788844103309460537629011622500115399879323510641640823080147753813949280948882802490893903015138108443747509995513698357635401212060473125617913667041979230402103143285496018162880919323074122384048345010188231266864994990177172587171100502823811870148428571218538063647655863455681791131771967306747369654531388618917608165425357906227024759807610382926300933439878561798088766463104236919755304526068710969994186560384385605062950467855130703183629010947270) * P  + 11351308813696502569013492479072734320097515684752986007087072312529048493695213687610338992212395380302753696488516571701732668128826383156607583785810228502535677785020726276345847948798496531097890654809663366773772538826459592168629892795817150510134796882001220643858801794685557213286428100640946654516259402124120654796287569190215980609201999920873718187846098320598683780956804780198680046501997129487025478129727686950738192363161572191651649922037814119444095901592493045805403608013749634981951781688887979694760292565890056481472163616850601514937392956227533911966559018983625792033079798532081278088252020602064426543765210323436248962899590609159219888778543348892980397854829937347156201989983294484523883796271560022040351691739871926596324421028467596795790906209419285166103446020456345235658921100019500778768373066545446980109668083612522371869358525777370660450358415876116669494642049254542041477115272923265271726808673612010591314067294742635849098731727654870458539442432454068770735073471735582063688384751412248523166283339046475575643405331693138278132517825104142199120726788686342658915099072729083406307064180549889481167713596211816322097666482217243610039261469687248274297472113377880135974944112822142033269690572652721320463489794072909666260879585128495472921389609354095201157290029432535721903114309969475261338756331713129790) * P  + 43863055274978007632432098103577063029913381534575980576645624755613851947460726041453776769761704241836179222877289425157754427646315676160928927714997228521357268247237374573239741406245225340078400074353886508824830615380000119075894166424285150072506292452228959422755662227870871703017478747555659674694639007154180888047465655516946126376400071421787796854006685415930283301708244605583254152482721629587860422324260264958035410014890799444010680033239626757995960209623344050953444493067702242632943638122503703920182756982086959032186656121991206514226847746094114456867838228494563933947604046718989241821827174572904994502013677553188860752979025415623360230913705564564366854227502183637329586824722431803851552883838051416913160866038391269039140725220303486263467527260711130120220481688148779513110513562125353577431070803506865754722112062580154188500331380637175524891982239032146492906241403542962351844173879805679019538160184454348277071386467782826431984806083753042804411168987065049075510322690561752339279465079811975550990341685953741606215574543367482403168206190564432645709610039659098273835757850975066149522614915195856149316225072702034797761375673052607008865163760789275512890705476625591983798348141521372278300040830632367655021138911826030969480777686393753983336122466015930872357938687800605700296939078160654574564413311245284052) * P  + 24657140002463444921317038705284658952950397912898818803885577920135353113074879263139981746348927405166963243845021857913767528123124854470000783965988028220571844981955422501599465008436255735634401890390716936988997812259366690188634570884720449592933048283046679619178637916297836473656510708272227514790823091094076320340754138395562030017399389908945611876394102014346390603803595514641941341299982051778148437117464890091748209762918723833034899395215427523050379684675363559303355732880350460811080312315034598507962928205493719917822013764168156124206626168281072497135684945010707691710510103953030880128217754527236827469696227566103396695484580031634375521163317998387564791818539325013440905758868190383567809719204054915887764244106335502575500942568583268244143067295245206021923666482804386321659978739364139329116404824387368011280994906981960978448983241956502212305350531624184617795336963098752672255346567015812159732895002626311937734240250254959590914934915428485903982023602682800549806745489122506860539957179161092657742535728957609213791267489333632977738118209744201233831480904984120773730039698555426697078348535501949991154914581494896712463374921748902306595224575414058020449024188584746675765758710842646422929979777143428602831971505445429948672970303341178840549123934381442346340736001839243711838728068477642813199893668832034324) * P  - 101031561583257111053770186342856006461092408048074683362144528687786357863982630909289493925441960273891795603250767570919208369231465635061082486576694992803003294716015696803145372337726383131195527459594693525251942836659991313086956259383245251575019404833717496641905421861214177993271177158409219916103525884342400003993872945291873416282879809133553037927730882877095207501333527770209938404869183498658846822409182460698824917363036215171817928639386728441710778308308801849913355014332682868948344475893888377108465168413642179991457334008350180873373344989263753621813445993043953025781132015701346141911680055466168419759110418608365023064403339143295239505638249671539197669175143819321854776663200752868216966626062431374033608861493643613012655603387668326010036330568425017747922916596747861293326861064600869535554234125300827275255612924158932607257383975038616816749261063497910861992557025017166698778774544088449814654219830527484838019222208256961776181967581644322867953110778497779238207385772796615410983895424618294974769364209668158350084358993206044676758261037597916849561448631824322301443753204389596653164030018668333793659933604203680951742708889104690805578494998711032104897759560528036788908411412597850465199690322969703436591388167915641569672763233108856899650823328718749767478670394474948695956475588479856735421113438105775204) * P  - 194033316472597857470641123463384090686518512622892198382497892110053563596217192315665236955056046653497363022356445511349412471087293948099584874076497189201446386018764109927111440362675302134443812127385351616227427155679955137094347132546051903658441372589752552729479716452071839927068167316058364626009276221822623573264664920531991202490423699679378511541851181478818189475838577138376514661978280136831515216886753439120316946310094466038204415691162190803995169578292370832758753114076165907916032727704655633921283644181392193971556165173718838990345801572560656653459130525491944851589368336344940086555901112419495647374188279912294415373804234853346842011348132824095213525017584215253904753435198192016625316094987786762263205222883182290363025152291560571532245900712786690580301434834961817930559584312065167439235537246899012314392935412504321055399090386519203141170971321638899500225832893990366903180984231386648496248080283068067224662921124536200284779755790691658650772275694752546828354230814520029556178531034215129262186665272611567472734265224706411893139727988548435327716542744970662326825086884523204069440757713050740621224077950650038504939364358430664957051257351232626882529120911715476492135224910899522026882681156198842615510226504207755118205995281337367328503613911434918732258647077720932222447930905527209055689071931869059164) * P  - 31263676128485148330102724630302871622400718726198192970897268426022293038184815983280912131899644219394765896811074887377412975902915240551166403804131795148481863196527076257337509671880058089566147532627264089720806756582860349097233272414647031196816694005982393510034513748462851922748691600264630761817911655761633809726171117105117293415977705206148294181668743837601468370310703479674361398988529681621887929243292532782494459103022440401541545940714879797160118709140343014345651704949772529428514864665626040304855790888012409962007530100686449853203175428750400305770446551153354003832139248834417471106204888350880734575835076137019865230299126880996376714193159678765494976634881758206454784110860294857033264499314362970099944948380665989002090021366898282277489291288450977202635639113573578648255341695282941859676054496100840297866715912537731036562731386931035233296625261458673229444921841913213469039922848625593766977420937192459282021781552361973779179429641315163988280540276838167438056353327641641567444485948734101942743213821638158344600520252529469415478253969726085401382812320978253473702306676532856292315791781580540323566361019143356646231491589381101572216857933607396186987631097973077028589205233096871427235272634351893668790217616369901676754679724740542207436704680520750516622479504147619000554248671540786957450158752843997600) * P  + 315510026979686424880877313141655367630937580118423282355517155643136314507139713170659098031750631792247775849906193264010285796309441699359825697058551825272026230414932702931855292809167627004046664857994837996173662530229543122726551690667814214338915103865820672625704602053439674015663115378352428119136295487644272969398168057884562149658264667158931007797838781715213309152967090487879045615066640603709157493774506288605847610721478757259617298994054914806857571948472732309922856050058505256083822524642401887269246391162526875471285397029292361681549329217826690747743384427063251890404803304271519154225360764765240923948668117730160714937834654343173934767610026614513890375597860292536435507585923167704330047844991283677061349192404424521113328093630193779539912632825134158422441223991892485887748982573227614725447127404260752057394893650423382488503597377690024836364826251555644724825267091985077649776337590488650254238657013241308173456597993153401089905504457768905739226333140872699898575103245064787780115895741778237676241895832253720112056279105538608949407631648652097585688504241754185413410997705153518741791998723454902996204707282843571766371197421622247222835779600414004397761995907796091776305185517315058482511979937898886339667314495509038506541189247756279344272108153521069694674472488369305719881905404977137626312371125991285472) * P  + 537553259376302186534190181491429599482671685629373083576426577501522415785288846951568377093423772681303432349192163805457887675089773338088583228606003775209781719167752492871846261613483458138625903257630084708504668974143746415571084534630426893101116926543934633650705376217658213849961478502920713314482088919226087180927225000042730792912522760499452081492115919548540791017963484283924359533971725384748627384290286785273115393743699187604526420692756738776449969518491702588841211203359888960996915040146332874930065238757026785884040452783004951526631222791087096790712953585539411799450238523614252748245423346807341379882020081111577698457696868212266064546108157732332442008382762654565731151784161073605459125872790570180885662330982546740792892640774094153579450552498254112975269696638099361700805303896453517346223723504529215387010577869485366623421223508061705773693453803963152561292606393985967259072291456351923595530660279506013135509198666996382193889226572259981682022939946232559077696690962331776572473868799381974765267963634847452998451820739276602339804449512254215843465234646926011502483091265119626948989232376760174722988815082111679833465746994919924814501049917578428325574790507594286011479643292208572224170231343553132969306738151870177579021537772786728282811031099847681525850326440236102272431510183559483856218985288083284040) * P  + 318518911267352862760713369529906813945034132563604184556273512289762093784478797094978452848551270040014526406111227649090264918008406388828748133534517711115036614183555360804895343908835873378146775291158837374308593557697087133829068297851012800109076646807237895294000129054917056925922381632733712081048121993419775739860671873909101395593674799452776937896180554803954868652745086367987864005657961094666545622741288740664232527448256902763960376015670138568900647333920737468818194607226945928443362668658485511680265080715821499804187122882268347827027367640332302204657137008720789030371182623482567806093562379990538244542073052677549543934061631669074952397740297389461843434657682893499972101380595149412096555357322973358408810403898809844649574737895619062592848255148228585682983135449416493466009576327436768941967886318124850481694743109210106882405103633583875661193481152424320270198643461381301043305432626600153012111311782491187986409454917257869081843095061510039687400673176330813597073247322104085679529942791305007792123623474355117805440304288723472424913463115620004851000587148821153524178135947683800320391621646548180615908589599548986658990001033634156134729439692103641423533250854940395318059720009364150136758763404977209861244632954179529237634031858321591207502405234489680419432761804470986523855901639640079439398654413283144088) * P  - 775946773469250415888804793835561563773757545499428964737015184132651505198113287501670003728293535885117350765786873864676156506967164611733911678168465352023208446500966317187483599127838976898765126027562356875095527096223051740430627240729001172908131208426882828122841016023676706439156739510929074888391600235598722576898705645734640254895719212805365066205097404328572547859149492940599292395101001290463184578001164929635943060617364135996579960095182416372361994053994895757791266780300017318696673608268667751602980276545758278067739503772940272191401994722713795819607548498077077022113258471048355918458781488244584674721496974294669395352737282827484757233797617922884660072110697183654606813498260898024128676288195743540322691360979101941972794470323917851027181852361327348580449667631396716578996523021684130902739991774279641067350011507108755826194315458626054601228511079837709063151369908718090412636638867065216989444538255991790622871479370581705486451387441390785819055666258252586576850826637784453936673495443407412700156831072407324434071890982904717080838283327876078362878188013382392237786242685183082259977908889686541230713231897312961218587383312876769423780378237528836810566842191550186326278307358323944228907652765079012915808144561028853871411942541913685052971178872561519413911379285516615085007407616727061752883208953473997648) * P  - 2075697005726191160790489246433261345887624176847358985779341781197895167933000553189770267471663229498157300189389514794465436904327258563989866898659064129782011922160303135117740955682011572178033167828673330026106518511480934439005504197067473473818730032037198114705111169702120281801138346532952905245914435185335042638637471478503515973684621938351226512961973457386849323492593931828731179312991393423417477442946505933309531053550010760456278526153297863103988042036579215617265686044701285579384961165451734114363090236238653094308833528940423436875957058227049106818555997934357055505370589446102688505747546862963637437796534184480372463876831708442564055796042205817832373821264197841478173780464231504471243814422051775252596722856075883070854865951036870962199517342162122615782064564001004082084934148757504910919174620085744611392684890225233983828128994493145082856549180553087094351824216512034180680670195152811921923861665545397955150676365830132139808771340807325100007785764688658761345161279531103749424244222131701487102460238029544031914878968731851011482750418461051972555912482229930665840622275256475027143126661739030092904421503374281476138232101429083316066466000292425909199796408818463823227447593672575692192834320180809038518487275827876821326857112973183407411323207516612280469631933468284819604306489586261683858254825852776983280) * P  - 706530470820642676793296095822561972146452727488497171848430545670503938142874092914430543750371819825754026710025582314991231170553471474059813691950096831601701843219832835243156627683163445460013163856071792356023712664206595910257354863414405466767872482556425212290255300861615653977092591372521765284733561580505453333511390198400556809552861124252112143082272142949198613693682595031863807953438337147010552339926033797796531948270008674075241418876458949534214019596613740311364043441331098184583083801047478473692348044242747461022933196170578649268668431060430568689457602587516912630250831783418356933155984295571401919568653805573543258333941104261970126751906610563782597742436301471434624668628615799972092746561262586844389000236846590694913388164378227972690527339855020722257504041464555379090152575377330105455780479740324746728463751340592905353340550236198509016510894962342699192306570939114552112650311678066403122867454602486300808992782192641443500744779903903871024326065852287347934534512744814496382636139999120727875357619440787769786781581806544306149143984764585231993687666636881319853439132752702683021876475981596900901310684235386501876676057641022978372428695310115683706404107452441714618857877462524253481287472200510065894492402872052392791631977109237856543442552138932118142246519962031000226670691625041594000023605069799771440) * P  + 3534871185698882591223935184673258910722030976619473237722946942553317631691436792636802209039859754215127549796229807473838655040145279457009318252540328166109704961670746986533496886897400735625386044704347996148570683826202933300005025109377204536782924426516190629400093580927122739162777125335206328236326259396379847632653408860600845874098765653262698796489033112984141478739930241814088356485173807821029489166563947834451873766830529169849506953055352828607652164527869725569249834322032862617010805901769860452625156324764663663204926011875859334045373163785139059322145183188290546741917428893131927931409474054992154492083905948843729499918024243592082568803249655504685714742980479837162340126879354405696362161720589110244088148697958260832690917587550831805750123076317169011705226617362680134991874739921454454787043645455877234986649292117694162970318609045656247037252461160217536307327966874010049392840061317145017751685075400214344466179238169586314890528779134441359335771188663530195243880534295231482749867832540028274300411805238700207706045537864034356454758337189717842064934179370359826184559895687951611815954425246896840802056995401156332386732097468408481578433685248796207290644551503506582364813772543851287461528813038954337344640385581977486765680001890100282881343863479311717087198389349941706592499054565165726964775511527673215312) * P  + 4089264417126465875382209105741895035002936178958596024643888482209696126354172484698193699276269919757733274873230820655985886540675874707727425980764131383557259733041023617950834298204412523817996996375627088463534393233753152230517271203255372205954105887819626585845888063407487610452163433618892599324450467064114569420532378778288662180144999118033898836892806409398733345404798854160467866717805663947655963637506927932989152330114231425352195267867898783952537404533792300306126215476029538233085569368114163330648521401111589099629032752413309856530756465168373000820579827150405960254460541476762320037845628780063389306239955231520783071376836654475639944474359752228774738513957569773306873966242411252529837772401800538343677217582275669174248281242407751948697717378252624288297284188947433456443545698134697139120761486555974334476538897037476023625307561605080666218267763475290594786653479341465867735862403318360591134772404307130547320834568787867175866476592025180975945037280532524229474130788471016706147244774253918075417295210244337986769348417792148475925922239703193823833576550898656289601991831202909443427416158397531734711011311268884542633822165284103702836548517168182774811342410410492787331684127450485445806788832133070125378222720395696621954773011653766569123502885070566426743029625878933719110161989857288931371829043833793240896) * P  - 2191083657214364946440612968211411646532409157150872855278295238435092238355717879783904443615981320081561917348844063076905706459485340555075501896327393870628556657376657583674542205377090774326619800921215292513193697099721503098763711258389989882341321188314634679123280670023184667865814946764042512552855663070964425858097407556572028785071599031067038453108557959076208344929999112494258163329880995772571870841984866540722183957238813588176044229452031891523888815226783002708881363384586097819566233924841254267792454000471333757537234699905128891526637282654541760410259686736156710378307472878004814568473867827004760062043434780958882582037226229974486514930007901537114307646539325648859650841401582057795705113165228461342685276366457558369905420308420965445981162366234481790164193722884778007060114391580361677299128334835528552437008605797002825521835348498636337540499707118146064092734390697462611134347647621992610272325377483491421193726992029448979505298609768670131709468030270119324311998808583076976016152197539506480406908858513212922052897832073478376248622236307100867792176048273173566416757140263445069138143995038679009905404910574291676308568916521385800307819055390485412999927179847809796295702870224952475522870395413561330650579922360151110265207677499071218699177312630046132743897779205008142474293783189459350778190910840465862656) * P  - 6516631935457255167818836271053458370605300129193177140359249367072547802597747462240321168347142435626852752974497543137829691275108345601249583166413878138819098519513783860071511144512773485113769089210901450939634013006134391553472571625176748317510713516405519341170467889594690207004076145078713500043512274724180528745392848615567539101356619782000942674168897602909495901894333970669458135974684385149049012255638199210681669716327857900971920821030501933895559152850572010694297135581227969250170882228367105502100411678418088146904122485058439530008417996052262660817961149518382392698231585496477672420650592747338043774447086582794450024870763736703396188831780290407144651713293262174831830128005185828714580923608816502288605365874563830254838835147166519231120852241904871358003738127184054974470092306038988682652910557655769201883857550764520299979210581180140005376952466407352933732223539865504699449332188698940023045555484774398289396119527717610655431774945017904664517158307188740871637851817316026334711087639190206837486162771016803540268102812751845353878183748207343938384497852074546748963109142269163833391768687332579646299884003912964370637270267523594405184772342739045539115068187362803499984411149324782483750274203671900805874344514935937180077714258444325184232629253852164667491404625107168478464575630851196023895940914383470681248) * P  - 2306022818112915731370815622878140562922008225966074740401332465866999648475352774216283884057005152780724034559557188759954663209067032418409962338634123386477069236501766115484956154726522088648279221113691471764491319739641086536726648104999217951047527805410258885665822852672883891007176815403680909741070187453378860124411878942690964179854527907824958453850463185853659694096323537029428444332978747345243430335106090682423556498580446960762420586380154866714303246550075186586294265955308206023644692783630389794419046636186369538052184185725959930421100612459437359119759833206204860251283197627514652556678999091518989286443568826935284779027153082962442814454878171166712101777666961738006659033905002133745171232732724235336241177916481377288810506551855885848226891061724239725494376172047765459901754659536772524456119548913610915150082705584431661349430054540915204852329190087736867286046508745394497542120501784216661326703050084517694703911468833514147844618384075362649653666532476366826536372278665929173940351153581213413487555028096508877562675622572487575249056522023548374050128063910263324967360223146698628948782091215588817730933513896593737675553150818092536178287688149250154038466563953633574938733395330171570840755277421376432565576504171819938777498494008080269019125751307595012092106190094687546549310844856145800184572899447983408928) * P  + 4357666485659809530640966205041290749301594090957123036528433638130484584118606287736732691497379688187651075517363475756074540344712479275623230385225183971844856572688634749311259449514131174967266493721375259567483975972369412931639610138427353591767513975828088970675185003697958258105522121589753712634468885506330444743993276140401058070313408676274248018214240839085065049597086748829999346543066315942463941161552715493833338101489796248115705138750015314492956245809024486735913245728849326101066636190952922029788451755065964606535916078588416153783738566820954089833052089739347152008072613897104536124247725202987505582160915491183837149275189624033332172506706540945998209489555125681825146994921666364226996709370244694290940487862679201077544653644819272792477054110810974377090784224084548125154896015648787526893259875329124305960158847006625145179520850166027158701425521746576208583220254885866596957391878171676767616366338175576784935917209032114305775242010970119221226146469234866619744117322696222854904221140949928743471677249025722041216908249668269072396591459733071396028620019731538039078408329043177168698571757129193543805479935893561664653408522785468626065541894350757630684802393053770557844164860574120805037473840595024947294721218252386580944383132292045738907423182937590885395781037336077939284259581753889252840333321685242668992) * P  + 6857682461613550444437274354474245480392773750860346571149087282605971902626849233798985042363746243217634083845910805503963325534889282728551882615736512762702629948010182594217631296780353115558456536121208472138340072592381939642379121458913790011424183391219471502633734294722811947358373155722052832725409841674745394427732796363705658224630598371127105057048456981751235428618084199777009108848171535246338615009480496571381422929456073539648401323275638276244851444996537707460317046483623191678104698735171171885849393929702437176788028794828778004992642458513373190426199460008086067289016861035020308140645732543510745181212499699463410417387531569423633680160928182961828634132438321238887039598685687003563011409761988167951273580753591183913752874900761572594975962735705911101621408276946635301093707256163229348042064403590396306113612691331971098876051075854196290958415076886766402543388355063098417479006104899905426834371407992702435459675394362739299384047249823274445278337309916576599703133341514686967928262654700940153004721773695079008178282581671266283011565337984752806789033277326487018186451515700649462433785739805473661959458087321158532079477235722377018121608924093341593721105258091439032999631418240872569194799871568829757697583773299544539754338203947244756230014627097987247746312894931071427300776293908889647303927097078192872000) * P  + 2337776818012536463492861122703346248850238906655262792765848650789813680346844257202752972999918226443674563358422805864864481131184527158079753934511401005485162413575644219792951824374597178655836192527998276709030625835716110311950725662224310787101695093569329267194910463186320860609796138706519619067021722508654307893195589111976026434750046509355782989032648814110259058313110511837552024589316022241679704772002025169626945593475946449118162124254340283170689416789345770980088742149984437168850260448120119704806230959515825996400159445412168494994482150436568176954023174609530407765182962410064955488758661178906788507465055511212400625879512855238045207563353581889210921949308495753269376725647799140777615046104715870537828111520563938572171299352600602837082287789099550182402133549616930966080994093107686670487515493325176115640007723206676798250280232724151844415412836174329433150463462814771984792213321256118096817686643278816066017763197602568443625850778777117769181436055846410379256666721308544218799164965313342211321793764409236856208443010304343354749132395417952040917870108684769720302192821629624447256054580945316794740173898317078366972933242935063284469213122655253405593441378598927166145659238859444880767329326982861684520265789090891245883949007807828597367786860268471371490351322782024260999674931571302067020442412171566429760) * P  - 8283860567317315688372262410440875504585240358643640590689083424825789324483028132204415935461330211601879369297892065922589084383901283818951910079539301296762325848311000706622584610838638561663228323428515266580793625212244792905840575800184969577515951254194291770264343182688128662229201989036293219276384576722641255546888846158884559941231984554842670740369889268560220404552380753247163547489976447403322036063570392559199812138443772613214815601006985988192104465110898340339768958254346927234740257518881224100198452577837352080636015044715140608840226893852113987612824971012577521043180119798885643682966225255363083648639239832052810319808537255807932808582736256945939175765808825327443258248125102886154960189864913923510674141314459134321824661825312386168388328087701608566864283293096149829504026648682565942028212397363664924683377921905221818210873102938511222476995366914035628699283181248989083231255870773428840741745168304335725204976208901143772619369236295246044093689389857216373711188454252061664926142130132981445932069156307106741403946564074118927494110492057523997096092684060159178833503176754650625869202814508023582455066110785890849184338306698293589340476449117759152441474229735609774057369447803054770489304418404806463074997116052305826584631539770922602700274827944841240985260676249567129549418640373890402516380867199511064896) * P  - 9253527422058917344837760690590200782021533751899028200107871678399835438450781739630929875723137943209168117850708510850033996581679214416168326837479453444691629777707052701519652313017934420299153691370932515279785679359409590734615946283663350988236865407646035927913727798441305710384492573799295723301590707217472144018996675618483194857883404157875670880998488794625492331696962387279352316551396356682640057623170212666985592926205592432493569094706306238940551600375250728643163309491471899132268320748603270988946778138173456254275774251618495382229243903326190209135967667685265186665387654386333572114542072613636008973264045765886657118447105845343755114234714463727328077532900767050502479628425851119763069327960583840366031021309639828239500734994506665041343139221370984312813631041891560387387087277406785937172564796523835511117560646337712986875927134422514805353519278618751923869994679885925062404870316272680425720180645498828913694257732676217601754059299807455608598256223667289291238254445160068900845391197659765525163854102356664151515064393366327238459558903725543181406320113458025854462874016538420894889142586567416357096472148800558555204411729802339033214914689011573453741235738488256441624916142008047194686526018321418320814887406847684119900421163387814956102919669996722005039565600624312067974601247272663782227486505179395915776) * P  + 6868426710753142269956233996663780602619942390957519087163107442657057020991031467183273036431239333687664779277316635028371812151109867458927075719305257305359018919409761901331211322058952616411421338123333963708251213104968398043445979046563703701336309291311643360857940975465118424067349849349848463345677090401403089571426946284906723110751221835913731710716164096109976132940605899435617631134733251140798744082827147217246363179539159747502858128452629000784855881699440563412312066757881896572863986716835055240144692548614071931459436855944143775759950604957826089377513104198337622448499715499875824897307359708384977179951131898646441596557156784609236915365919111884419135899392055971847469641771723151197421356337189941673275416185591777609419537436928539901855729048654685372529850930014081883703358375391719608591666091469118687638410705857378839854016506040413165155372090610491478173965731660007401873953446899092988250909207414026936570226238424323937177681776992836603026379447058682368005189234649169836562231575899679521772951890298830388809311588908584848653717303078799540806902421050135280960644852870736836091994447577375652737043604485123925955932667373644222122923952606302943493320543165886059858679079207919132029189787733480014979683262911386709757129017168029573064577111164862398233717762433715543892155155858732068217696711634806069248) * P  + 12110507561031543825142954064235727213399402092911670762203080782975563454776117719935651504221025218316265179946998988055831623131789664964584129972319028093298366093984111328018251319946058159659198600759128880813611124117740562456824939004460705841973547335858805213476221399119373499122336008159509746013022640470837748116594612447840102114807825624508300411830311105967662567167918917301647576932324761554133450536776804706151431341689527562105946482590007449057853656157456079293931646566669132379103832496723327967043118911323002843978610400638006471707081635033950897699104792250286412506362622503626289119866128130808166711678413627956976104842478385679479644589161248085235460614477281948433633082856529940177145751202296861156722409641525835714231001949255836135524076456311826042089085722419395142908785238556469893173984242601566588678287397525066301444863803322129306354317634518506887917481725032444536078370122795182051138287123969102915783569755048863602975919138872685002556870487463305932823574877015145076279521340954173103137852365516845542988579143571376906398764879824876006348580448922106906787848948849340471822274472533243392170299485275372461059987937235074134814629261909219502384243651095680453418933350887725500015543908659810807540828312795828415617753468220348749612571048824860475715010156518362143005648841203364540381703796512115210112) * P  - 5126235454975739326493775994920517265917489682591852800134500049309506045930592577889605081012197443233433597850879150762776471735775165652128113917591545649219768475245406914330095720081351613594158585792866180243701873871159769400583635369202930169695148234535573396438780912103799755849637472765207656208963620883208111248607072291836266682390414007167020028011122965020428362851947833834421164320899644507368703332860882585180309573849437256023796192111778914584706070242812963728349361325846864192290982815645721908147306804707742690209505949935529083457462368452984456395973448223222350515753801799272116237920982441769769289758590161539829939104456530804547345863351718127672582191806727619332081045822323616782887341906564313431994324907284528722747269159626706052326611514211319670049755017483343955180225875061256799991386453127832086349962965436847033172854793835221505234105190259274133943602066076730598526826007772654273045062473873957586560376340188715449498089379868844431225372012487733845401056614354608404605747253042624649790163102641650035154542083814851520238153379806672924093826685029005828263256106138424123277581244397940012240346913340192976886880704343751330707783253522348960036469288934445005181031916253994030609505519904705516348288291721467709961233394498590760123873904524434398610342360676706148261728038584397183434454490177217572736) * P  - 10288097398796938454439326410192984155581580342147338242223333778805389658299159378067276381329942235681000816845918611772089549695554616904755225060236281436701746451244402568425629216792674827167120609255843342149939465668693817511982100954025793853993787217863986013899529273052503101154064441925925691011382801261575241596000727196028840896794853917769156303490541697503106113818427441411388632391057809177965443159709511059994218531860104758616158613365484716694155220466622086433679182336638972308216024231113628342504804453350508589928187399695578812447867575430162268206600899381834988263093236284629591438895197074643339750266976110208616863968065981805811281215857496720256776388147074533960974405127505540014267980843740375497888008845443271167497387456821576130107297910626590867631081568203659939060481664558644279468673706049485887226704677171844786028659239005589598246266167921698169379152556925887022343956456315321982294136083543736854569662373998992046063988301684069510149095556766021721353148216635558186093135280936439514055041841073066236550796634347839466829746041655583624829666778571709758079770051311207846407076034409082543815137395720391120731139239251739397802162951053115440677669681656070719850598435763789369775078657509553628549067469216817756054790528903946811719593769883330183014106871448892590197907663127940389105839148316496743168) * P  + 4267270080545035284433644598887671094426274443370248817216628215934779105765984248154530920592719772057680699680821542119492996847533042237264473678549739751864895003776326352461856205021131737790702287472072987596525399235440615896408069566252228056574897189229656848387889870118808395671114572193459387747709913902651203991129695365718431617427508889830694470624798978077861624958716863673898384758466566581860756357101574133124882427199203937575238900405046801418417506412947643273827703690773448799232105889905072210900816880766608216869106990090137975787548247251978786199899596145202092125177596107010760962969346601002154111650011643296971505935972283077066119695942613878171882004523557317876042218509813803552666929909122026407476230714283473612318684531781308193492805157299872431754220853084420524286162246910228739203725750131069916616897713544325069758655186114469775402604605336116336703537064632935550159972773350368486484377680945430927515842101876834315814215604662858470773403779097654253555429060494065750098704354578618032243747474314894339348453698526676259880049156591277940564771895786397457226817432664068751811862368587754778422034330708023327816382011875222217353083907168936121762760582736004133887188395524334487091550282238581364359593986787782534970851451431327977165338145594109400094574796907983220538130421281858906690713605834772523008) * P  + 6179186974457547947841946670314264693093584047381411401611828321459853463049206822380185730499056078846486699493637904953461626806881436916847187204443649351062651518764678037587777363143988363626823668484607337158749046034731436404164293902391945688036106762279765957057579713058930092628361798535934449774473073070069513452693409320938867096322103586184881303761009604456696737817474713743336617857582703927499566393723462794333623365003714688319094021949493976041594347654234918416860502327785584141091290573860506180264558484066191175238262393910722141368085588844243342728478939405874341188920794665957318916203803661629120790423287699323715360485733980931927691207306910357422259588735058867680448525873534614254259790996997721621348603160363705756588275002337472883216893436175379821908938447338719045137992682813403977498080895201870768999478920433675700238697336554406564221783118997467941718600096279566573684772610232132585604490490602390325503770701028992903711334191341861536589125686762998077632783826397823316525412634858416628966209689988910887628090261433037099380485470647302006922110018553088226778038252662960436914278487784568861001720159421980034880902516282699031905246341606708454597702268995990444796488936030290964480438932933307123643851461356656380636983480016591854129153657232190317101116816991100752171994171039311405217152651504715267584) * P  - 3563267213496913302669958272213473062651328631055151042146489495187421344285575840257209045745644493360778375634426075656545201112777216373559209619244052172722351959269022223348761637348033510260058328325901779514250725154713720292698075971709378130543606590240749905859099922742793256290805633320762100961903631137830690223893439018735612017834676636748610053551950925920454881000438731617683497331921954441620713349052230510866700732518091309398865820074147881174757742124399958783711489200369844027232778726030411511030855931293233088658344600024747647594902267925214872420590821026646060649814496429413409190030152948040854949827953596437471625850063847547885896359998620563646590236205949539465441519181977672433821266572329182846465423732582493305388386170762868454541996383485619880015155679488941847075136616341249421687749719252137071549402198675702784587656384521069958374142760758180245144061692332535577437573467242896674211836555306568573760443552002180452348300649453898974904237302465829244087143869689311021793861215096113564168227783067893495560980844496641088957525910643377020315453817812443949050067955966308914586912900789180826800197203908343843810142141196431011834693184129069050533210035572561133788910058716565353070782587174884058500915199073136263977183861303413458744359713486829637957354564641296740499978165650022064689286053380487434752) * P  - 2465810462053946344466143459216016582286774684310156545892429802414774454721226450471172996869760606440569464703846028307642876716310968640950532192124190535322236494467963903242767494609219808636053462432890910784563969529146714635940941681741674772137509034620769357391511168432027843848723561303556997529978045208387983957698152214112256467210305595167826345794773221502996856545384837790671615646989388546916712497005154081750466890693400244489061682960951381337217813494524644519313310273548215240397261759319271194479325774293538922056285220720323945809809515361816243936013367670366549770434175090471955858649656415851073957559644220133550945467564760744976628274810001637543624243979427375430687264428275455499090014706381474959375021387723059857417762073929751104776802509340232806488197999537400779099763050445651958303326286123201413431636668088799888278259696676749840429872084190605682066200812364593813099410049003156716672562909546497441284724518165176395429455006657795052027977962059706383379705089072934349249916420324655025695580693391590909598555083576575315249128069842021832481669849825339622593862609147989843562843660343680229233426440906486781899553715928327424682182632542215941551032519525047093011447966113636818738568354040356365769841766410191857774703240431597877507996350239141805583627510391646919507140409411550281918679043025565144576) * P  + 2368838009373814872062797861845110880197970892683797046836879181164853669069511380825280367451113433490280327538372869418976306215732725797831129063861227030702088926743516908349520885143106963543409543439321044802373012082779367041029545025009312035501537189699121229315466253157596403046906655296708112617333028219790318949883736073115682966558966713722492511689606644562496190490079827969105543778244922040592484188362405568497768358360599936893368942909469584119551778239154060761250469626901576679454933246542686954388917123321716595762756898782358264953747448412098181561470389099451862471982092804566838569836806980072290850810354776140513390561654085301026386145580033688863300989060424096918722638486612485005080286991557711109388597236967098195293107907132805809188096209120345054075749178489255302243821537631774845085179602132824899262211921209648126267900295430204469895755455366950159014208395964066882090457236381955815061218054041884255199402859867348505850893549785612987225880889616747056874891240023199699292690197641836888085662529198008785305598786921072858068995048887989968414205197048305241341514921121105240589982025894220184942810050504200058135065354735656698695146087456034913060194945403965389691593407378395088999430380482704060406394790450635410001737647837418006205835139646377775429953412584755472050518921038391552715392340661362797056) * P  + 411515232506874558840206316847419062858978131016621773734579311523284560685774983975913615697220399460513652877085995584644824370463898032878141134003462129201303095747655133176973719605096365336032714307226360874556935372739986592878499816820839887275864512144923635088221399909280306735570761843214778017185603572561251800021287080556690224695939534791815694588027430356646283094065993828898542662198611951631609324490943833518967993187502051064117322955430776731313210757859694243061948503580697229990642719682174269760081302891236609067299538593146992510876878653084672276411275365081538757832455336569272397117821222645695644783747345325299812575330501564031179522905875629874588221973006118616532108273057331882594831685718597003675355378894343975860251994885086414627484884559593087068489578866365137837652239456019298797130475879727571825822677943543210866343596207369287140230149792202863022730059086328560896974028007460179708571469913310343304705103906098629616593541616352452973896530700264679807145923238569938721438394781104726362926955413899323553823345393351434030774023582929613176644363777511744723962263866588753351938869198065441219457305358718008923100194753263106739572563718488480017779200038106704016324810238698769958441009011239239337058963846359595014414396435226040743402198249603258011046053993429996049219222645909858283991384495477665792) * P  - 1089296458297021364141526992079125454305391409619938440577496843780342788619810375808652570814894712899162989564676815911136153932715923206510007569858014890425468656483620314269065004397672597582373746884084635112443052893119972986770513067666923766158824218225015152421652766078506905207714071588583827997002305069523747303343680680729737024933164594612337726158181801524254017980875583864228250440207267770903377455623216459070174084756311639312793423960480021636256650882924892246669691884999383317168851766326906623940202603970087500192376401635663202206173167042123141148615448867768724233598031079013423987938520352663450776472847760337837692913348619093871868903599777234215281627206166731294932187673147997933261411203643691583498077603997173617877441098328889617598308371581853429090590079373571733712544258678425979022886866923857570460087607178651079453227351996234831648573868961668698807698963371343063813138839500431751506453001500659956159102957396138085514136913786751005110495017784058036796496848321125550017315757363688123482204498320232869640263268557096621890052345714732287584714138290038077406526733019680593776426830202580938097029447334231671779220769903298146367598725339486419863045493366807667987875775321296456345295742864192439410849570128946297352881112026691096537295819022204492410933206341739707313286309193834863574254192107962307584) * P  + 191244854267255225605276591899788986581443600943468349298027956201493699977101382060673946148918889024100378547577032722951444109255730587432702828838883107484792614826772223303335133322734210971108717052317016565993978804041714877217250956107467249977501102869408990910996112097231436058499559412544713676967939945308852676339936660597220312056920458267052039785904265507157467477862171498403879310469467586933429301250781737782377014360387791816312083421888374266955085731085428544331064674732114367487134533725197367779761792991807831107417549256569915242678989452597043787135037745257856554708237642394438341925816009718853889018333374212491916886628253079119891688351248785698746461006031944465862747715695566453125048010426515538324173095205977569247247419685936969869261283658886368949807486056585411237376479123996606255589658928941482485199960839842291812745551957120355593832177363617032437670790425803183324562021045256400395470691309453429320803182743251840293024254734865909913824171363232427907832958599312784972242893802568502278465603857535379167045582372219630556121064455694485302231095990310369520095426911387866085872862418522267558294020626998938403388117527984186909190448337420167443104885627961322522450998742425545084491687149058873366184611066866042142410354336236103274678056767777619944387662205907855120113626648756012114265791806320480256) * P  + 304836129443299152286734866566599284258369781872575640132772793282143746205359028810773794543262430398055279163639441435074035780245649101963285243627313873383257170649407419921980819563309563532846940862550084562451822509258163040474080471786372551053377448863577713749063341677131257013309734085193235514054553396770546280168728765864158285910703475800055239009544340078338345953604152346401521883371441671680852531958949274675726181843430595856347513725071924480291507617986416215411144212439876862408483768361525753269928016796210068039973151217927264025097060160031196334095932322590178585908218772061060903720639118459356554914712122512875395579028494204196574130839582196751723916952108763750908218330184790529587948588603970693096476290881366667760139226986090199321593851824583182442120948370625296836189313747171287320513063544080311988174158323444002518606257578423216320613098892667053710843679160130481203860677552487529827707784198547543679243648731587433693183543172555810760030522968835652678782219258942752521903210583246611924534822481145635222640592815580282524454403346444151433992194140699442687962722535869403333119713440881411233203995960569862777447702714878490850235607701598692357822396702479764515745716569013164887338944907143577903921400595162342775102200135140847182486035064539563891066401970731506240227471493668283260680693824597522432) * P  - 152302865835467788925420354909615711691104292569822818223744166271560824258261162982478300951989263058413618418157714276485341612599536180543083540659746135652502712388349710212513170531987979336728625343920773040294643643538725363718291286018401017183356031891017162371140410504147676848841855078598629233404102899829827362763490233320284967518843114635646064233328358395701381204996283224936611448157885433347998183992332898264225102921354745436624094551942181272749873657138698231632786990610560218974501936879806143480328216753008285997708526824624714159468515564863194874619651664056291808955718958771059812803262761524680532342236479362412686379443867546344790780032777807295957254960326486695164547094326267251495268566421633151986046515043252609340791451132453469604403685285149169757631702430313586356081006560864327249731805173468510995425700539873432351409661284578808720201947750623647889386327009756492376019246849130980667324471408563944575554438237469267510735145163292842088522039536075213888993043493709193018546327735234688526411026984818543651760060568497027249487288853334487107320165685207680570345726204953299219100925039589984777412644588715772787662684966609803505649704335089956058579002477628782458297078056724089934386163241335926776363279835364690354225643277981487871393052031124785537731631525263027175761227059033770787549284028089442304) * P  - 36811794751683958342922739406670360164201046383413147987194284641093141110399225613187911114354579060463462410731483139689594690002373494980837762454698506613882384272959644666576461253058394908182446340858794987969147129360530668835024639201036168981387600963679403680305148802892619503392721837720422803648536891808287224822128204001301537035900455384456173648077447412716948920805098275790928658038435398454987696074315271476684422801636157357993321687009880891662823491342578999645355691656194259714894420554541682902734814154178111839121860317446607940678987219928036626706065871612362370258302457206886396419861088646461260589082244807608955068166681600658501394882307229151699392221876501992164942284310538602557012309486458118873461034021186337123836475609755396728266536088134457832748484149380743391433134213079959886106733977489186041082539597532946640680860317070093177728077939627057908033525537674857471772149845583987992693783376588199179956897161059295690422823374807529693899196855218808084528661159345639436072068181490158116325470955451096216562308426323187724939515264962937159661517770785269800561161909296394160657605843848852116675791252713998166163942842615217349479085938974042016535105744265318443455638147528332461339738374594924212831737373385045177126890090669235346130987655992765020585700415264809330183219412093120231220584170987642880) * P  + 43358238302106258943206681701896146059149326199526133936253539656712217535897327915652163350936453375067702687058290391275182527661900995830083095143388810735499033916254918487906011520631921441317452170701221930773003006837034528017698120252448602217288492893188110748412479704123125262737484235236582228464214533168202495773967846653383560721708400850594478787475590691811695530193654640261257726436162407698552282268456838863498537303757158589802014387726960640293562700005766946133670327335525684474750761990569197157187923794976560024934443712000423617527112730296511673872704990325184834659407487019235778474098116895185520044924875559947410093437996339899310727410882973654044649767831161666423705540301639442133121028147569778821053986426763468968715547353649588857498344199115800544657536010375843188648935460272023551456567778863679046584440876597405683179877153276379232693068141563695523832133704249941162836751792214557587194390515445375288482671356127461688042297242853836472320776913868908877987773332993510242296453026072245386893043001399840602986918354122642352819794393767664272621997214954958061745692569119505719196672161872359681638123425054957358071138307183847877453397236941116373209925519669949636527031125938392703049608998537122750552981292115463372947464511111452620536512961687611233477992690125287149809440138083053747629215244033966080) * P  - 2830005662686603828879781495899729447698751825539589834491082502850103219362210081612462882978131870629175136132801037057891779471449117070143418928971709112536176014722222715717784468426586292969573692793984487792163485333325641214826082537211526963869985238951807995047718399943948018934780853017947082624237488999442751914872134047349967612557067723755033247367557262516265115386661227824625201995440635373170221168620604792053074101733982124872939029455650606234067689783722490077737441329877845125763715895665631544264218095938019521694359566489943669625424756848913496170173604017129945026324818589808464851710102159720635326155341433402066060244504281060380987202118337438710878434669968601121951909744297999724073673848333476562929918601434447961898995497629100755038031238724608316590914674078246568134987295276863127780694185637845854003052572935789674041213339393653668944439696468874926280738463126382598114368529019957463158977303487877532504112425160222879885227206704128100731786883628385827795972239159793028226942577743517834323270702261290490272422729949114409814234036816171473688707607571606698998893083805747688074500999242048458596514244659990472676960630260084820370317878918440764966981884636797976599029007557528354903930584586213243681372694804254888540461654522507379701212162689530814277526613564450324268260404835534462308709289486524416) * P  - 5066768490868511272893961269415648629714012207455799314726945402866258013950546323730528572833810233418124802329885962349857399608724739043865778656173359047377834064042394564498455323934976520181653352697737244084333171710400850910040875112195634237710903522058257142902182712773661563081841852964220317874181391687695665503681381608321699365875910173168257809841387230138587750463446789498084811289053022369265987724864925871217478847654899242684799511115227027036159668690492869208422686131860134840153005918311548790075980465908695416639931658556287691945900370494764190488724572022901862428910535667096957823616864134969678428567532404845793729761620850671986373245281780453634617384985443039040446356450157871797512609892432473233298308379957598228593993150204067864561740348103850045950768857751925016878917263898119922192059029328510921505118505027711699246998041896862395589385059491353969319677121406642250136006078306896644666269865209602574230209470608914193830349693536954264792756686279769544034983941302885609909310202987213183011655492128837038834176467241348316495496321726995706789319370381341365858410458880464703304810976787272859518374630554147381020283620333190884692390889457741405816895863237415026406681335948528123203762426173268261077981946014533922183645262997263404368582887582509249705961525238064640856475258670847784295807032889294848) * P  + 986179250218486115944392513363821848586367089879874439155171694141526097589834989532742951800331363443440965272089005079300886926534401502659721297636496357548674350932614791145373857254502552782464394362623673939062592672393060129869969727255234664598365034705862174596502803240991353046875831113842711214653339949918273948801537116446790105585497077981731128449744571072850452448376935270807492536488674132641579051978555875156652945348405454413865062866323894990751797764675038271592656814748546694329147760630770464097514537595081776502313399868541700401766829415864322958347308624135895376987808764982307661889879393601215656144660929948588771757746950138378482061582754779194784725393401669335002335449437542166063706909664922857185258411125325654757626295912492956065613310970144605507909059470689711323680923877537046945934230480834622783573792440952420621169015181299403518834997434725346007790606211212812174215544227006158903347150844956298309645793939863900618190022402520569639729957811302046909138373049819370300964071583363243828879607038381020072419968296380091487773518003201213249418117947354824071522107672088631785652165204594912162661364426270770097713612245630352463955662867239746507475773974475679400709755070018384775683248978331064638501156113799994314586121972752194970129037789717989583976990851720033387902774511178136178854011579498496) * P  + 135223581302129551726635100379869505916128615711023073075302988358911219234312963590771589654190596937329927674844243671068940463563170364463758450902390804775871232503528964242403399560794514548706149694862429194044789171989954389768372075867501075945508001028100368233176191262712737376946342492840850880399222091509558643767333258197201769630499725652265603934233073468928608070278433625591973491242658498668932427942507069255579055028266102632733546547923921361889779990962737827534416469084621582847563958875438686383081956992390868540965504836948804277657790114087509191763545450957454469629266163595719123807998134720841957978556510719569545294763111341413244181073532420481924229278943242138853973227582670301821081890517031341593450667826660519091859932095871638886210187957059256946151784162969024260694220716526574651998068961481836329024296476208393069647143193080501167490403918581999974145810816865342519315160912170270433341412440790288948405912532258548230243759924831935438216578933783488693594995058581312577674360216622606780133783829031203168981534912431746573709289740710092640300370385727230431037236389273570352527775710825562237831798650436982846146699838291576630206626383227064277108371212818433636998777160139542225023580768969937669365791400408259765393641129024891734556280359807466919371071141965365227219364803825526388883413129297920) * P  - 45589898146271508880720894838691552078900912896899976052373510861769375231324566779518442095430163778321640399954387870189124134390465703134345363380371268636744160175808782881299798072947507725094518619846380001611386707026111121496849539052369001037781256644718137695906711809098352784153255981841789857716957291001459273783681469355807065372410232933427889690602374541942466276088653479461742128841477409429036358419744820520335695085459343681326700335342883892809083282543737431993977159285723431772460548737388603127463096528302593664667427242542252996902494495175505528885384460376993266863812671662883482583724765286664599148984176783315811018963354148477432254786613423606203457525270221714847466745939728030766135190810710164093450701615695663676721727797344731891871305343049855988938707054343071297355766267738247430513375534081802989877978528280328532808567967850419472188429535812054589740648759864652995650125689448077509551593619669042571477794356358382377899051377480794826800089361097188125333535298849091584318536600988409290368640688416345478691124605489508208569057114457649179007393635062046638555536949587103958438133767844446202298597564107042144997204189235121676564857408400507238333063553036415866858753865928607888363405616562973720956508937678494465043924401902316483294738564887841299510948268685427280854784127886778415623682572025856) * P  + 2851179265409169609230788170363733941135284164593262043498032505530586582747953463901211853405691303947997791139611936264320258552830469425851395699751151539787675076433015455665507388694171809393266408143862761253828314914199826753699284199953582052274922535988840702815707736042680831630962370708017830551718383650571017432326966299958850383015596548969778225603368162673514806887494607672746131500477013011274289955752630457708864127229983390485934169213755991375417180784598590640556552495229892585983535603685826026760815083857446077189887942975910128052102171829489198364612124399971767420937425878678257377951376029476274183189173618830704575135225328966083128002464639198974487687085867044124371530650468718871306382095328120215834972073990132399798249551144697635945263081122630636439080873493589957078756607771001377122722318909222574447691643320556304029595149837158257075859405979250296602514303468829650286306373095658179107307556748754038480204116940613741732247994594163054711815503290809155586877590936121776272617855486784473529599372255616813853844219958873154613877527511865594926416489003264681331325917225201263160352854528827677474349634413422528833748761519276540771235858780416733715625101158430597669855088285333439153144334967316057283361158579820861651476176934700871187119535551694476939858362740238001553199663434301582592696958582784)) * h1
  have hd : (6030342498950781788527296922778111382779766765786197449655859044995266461000496959751754088697741246022301058783239532301759645832011459463258478282063306487780223857231904508743700257166222809605009544208386321057063134880490083529717287536037883592526282802443708917424123200519946441531042514480211579666342201332560180692954816115924848653926304857193834447393995057051076009188679016048800547148789202116146019380880752578288647472897670287706088288670626808979979290828827611991675193243816963927114279959447664708541978019628149554956419150209255701330486410525075989543947090597047812269545784968394065004973572391799838297087175473799305037577840752441921204558639793019396931614859640380597914352198757917696768584548408677460602326149192510179417553389503157008433775928289732918439753262199928189263942289597131175788757435234807645752210300704715104982220348123254283914919107284381855028316422155053269059494200269036070309141177268248725768377088320572933506527000254750845904325102756772913278322408223183345947730433663147739919647854314523531082142129209718887618196515115086303163231981544873613989930796595672956524665622555875631648451115291634704099521388284161615331533647428024910390596738692190448094380121851172636550916667453347326009577085602731772315239695997325499544438468299809989603421150584115937204851321926539890456514863501498384384000000 : ℂ) ≠ 0 := by norm_num
  have hp := (mul_eq_zero.mp hg).resolve_left hd
  rcases mul_eq_zero.mp hp with h | h
  · exact Or.inl (eq_zero_of_pow_eq_zero h)
  · exact Or.inr (eq_zero_of_pow_eq_zero h)

end Case2ProjectiveNorm

section CommonRootIntegration

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

end CommonRootIntegration

namespace Case2Necessity

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

theorem chart_nonzero (P B sat : ℂ)
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

noncomputable def affinePolynomial (P B : ℂ) : Polynomial ℂ :=
  C (rB P B) * X + C (rC P B)

noncomputable def qEliminant (P B : ℂ) : Polynomial ℂ :=
  C (4*P^2-6*B) * affinePolynomial P B ^ 2 -
  C (rA P B) * (C (4*P) * X) * affinePolynomial P B +
  C (rA P B ^ 2) * (C (3*B-4) * X^2 + C (36*B))

noncomputable def lEliminant (P B : ℂ) : Polynomial ℂ :=
  C (l20 P B) * affinePolynomial P B ^ 2 -
  C (rA P B) * (C (l11 P B) * X + C (l10 P B)) * affinePolynomial P B +
  C (rA P B ^ 2) * (C (l02 P B) * X^2 + C (l01 P B) * X)

noncomputable def cEliminant (P B : ℂ) : Polynomial ℂ :=
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
set_option maxRecDepth 4096 in
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
  constructor
  · linear_combination hqe
  constructor
  · linear_combination hle
  · linear_combination hce


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
  obtain ⟨hP, hB, hK, hW⟩ := chart_nonzero P B sat hF hs'
  obtain ⟨hql, hqc⟩ := raw_resultants_vanish P B U V hq hc hF hr hl
  exact ⟨hP, hB, hK, hW, hql, hqc⟩

end Case2Necessity

namespace Case2Necessity

open Polynomial

noncomputable def reverseAffinePolynomial (P B : ℂ) : Polynomial ℂ :=
  C (rA P B) * X + C (rC P B)

noncomputable def reverseQEliminant (P B : ℂ) : Polynomial ℂ :=
  C (3*B-4) * reverseAffinePolynomial P B ^ 2 -
  C (rB P B) * (C (4*P) * X) * reverseAffinePolynomial P B +
  C (rB P B ^ 2) * (C (4*P^2-6*B) * X^2 + C (36*B))

noncomputable def reverseLEliminant (P B : ℂ) : Polynomial ℂ :=
  C (l02 P B) * reverseAffinePolynomial P B ^ 2 -
  C (rB P B) * (C (l11 P B) * X + C (l01 P B)) * reverseAffinePolynomial P B +
  C (rB P B ^ 2) * (C (l20 P B) * X^2 + C (l10 P B) * X)

noncomputable def reverseCEliminant (P B : ℂ) : Polynomial ℂ :=
  -C (-1) * reverseAffinePolynomial P B ^ 3 +
  C (rB P B) * (C (9*B-2) - C (2*P) * X) * reverseAffinePolynomial P B ^ 2 -
  C (rB P B ^ 2) * (-C (4*P) * X^2 + C (20*P) * X) * reverseAffinePolynomial P B +
  C (rB P B ^ 3) * (C (2*P^2) * X^3 - C (28*P^2) * X^2 - C (36*B))

theorem reverse_eliminant_degree_bounds (P B : ℂ) :
    (reverseQEliminant P B).natDegree ≤ 2 ∧
    (reverseLEliminant P B).natDegree ≤ 2 ∧
    (reverseCEliminant P B).natDegree ≤ 3 := by
  unfold reverseQEliminant reverseLEliminant reverseCEliminant reverseAffinePolynomial
  constructor
  · compute_degree
  constructor <;> compute_degree

set_option maxHeartbeats 600000 in
set_option maxRecDepth 4096 in
theorem reverse_eliminants_vanish (P B U V : ℂ)
    (hq : originalQ P B U V = 0) (hc : originalC P B U V = 0)
    (hF : scaleCurve P B = 0) (hr : originalR P B U V = 0)
    (hl : originalL P B U V = 0) :
    (reverseQEliminant P B).eval U = 0 ∧
    (reverseLEliminant P B).eval U = 0 ∧
    (reverseCEliminant P B).eval U = 0 := by
  have hr' := reduced_linear P B U V hF hr
  have hl' := reduced_quadratic P B U V hF hl
  have hline : rB P B * V + (rA P B * U + rC P B) = 0 := by
    linear_combination hr'
  have hq' : (3*B-4)*V^2+(4*P*U)*V+((4*P^2-6*B)*U^2+36*B)=0 := by
    unfold originalQ at hq
    linear_combination hq
  have hl'' : l02 P B * V^2 + (l11 P B * U + l01 P B) * V +
      (l20 P B * U^2 + l10 P B * U) = 0 := by
    linear_combination hl'
  have hc' : (-1 : ℂ)*V^3+(9*B-2-2*P*U)*V^2+
      (-4*P*U^2+20*P*U)*V+(2*P^2*U^3-28*P^2*U^2-36*B)=0 := by
    unfold originalC at hc
    linear_combination hc
  have hqe := eliminate_quadratic (rB P B) (rA P B * U + rC P B) V _ _ _ hline hq'
  have hle := eliminate_quadratic (rB P B) (rA P B * U + rC P B) V _ _ _ hline hl''
  have hce := eliminate_cubic (rB P B) (rA P B * U + rC P B) V _ _ _ _ hline hc'
  simp only [reverseQEliminant, reverseLEliminant, reverseCEliminant, reverseAffinePolynomial,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_X]
  constructor
  · linear_combination hqe
  constructor
  · linear_combination hle
  · linear_combination hce

theorem reverse_raw_resultants_vanish (P B U V : ℂ)
    (hq : originalQ P B U V = 0) (hc : originalC P B U V = 0)
    (hF : scaleCurve P B = 0) (hr : originalR P B U V = 0)
    (hl : originalL P B U V = 0) :
    Polynomial.resultant (reverseQEliminant P B) (reverseLEliminant P B) 2 2 = 0 ∧
    Polynomial.resultant (reverseQEliminant P B) (reverseCEliminant P B) 2 3 = 0 := by
  obtain ⟨hqe, hle, hce⟩ := reverse_eliminants_vanish P B U V hq hc hF hr hl
  obtain ⟨hqdeg, hldeg, hcdeg⟩ := reverse_eliminant_degree_bounds P B
  exact ⟨resultant_zero_of_common_root _ _ U 2 2 hqdeg hldeg (by decide) hqe hle,
    resultant_zero_of_common_root _ _ U 2 3 hqdeg hcdeg (by decide) hqe hce⟩

end Case2Necessity

namespace Case2SlopeBoundary

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

end Case2SlopeBoundary


namespace StarPencil

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem r_eq_zero_of_coefficients (p q r a b : ℂ)
    (h1 : ((((((r * b) + (2 * r * a)) + ((q) + (2 * q * a))) + (((q * a ^ 2) + (-2 * q * r * a ^ 2)) + ((-(q * r ^ 2 * a ^ 2)) + (2 * p * a)))) + ((((2 * p * a * b) + (-2 * p * r * b)) + ((-4 * p * r * a * b) + (-2 * p * r ^ 2 * a * b))) + (((-2 * p * q) + (-2 * p * q * r * a)) + ((-(p ^ 2 * r * b)) + (-(p ^ 2 * q)))))) : ℂ) = 0)
    (h2 : (((((1) + (2 * a)) + ((a ^ 2) + (-2 * r * a ^ 2))) + (((-(r ^ 2 * a ^ 2)) + (-2 * p)) + ((-(p * r * a)) + (-(p ^ 2))))) : ℂ) = 0)
    (h3 : ((((((2 * r * b) + (r * a)) + ((2 * q * b) + (2 * q * a * b))) + (((-2 * q * r * a) + (-4 * q * r * a * b)) + ((-2 * q * r ^ 2 * a * b) + (-(q ^ 2 * r * a))))) + ((((p) + (2 * p * b)) + ((p * b ^ 2) + (-2 * p * r * b ^ 2))) + (((-(p * r ^ 2 * b ^ 2)) + (-2 * p * q)) + ((-2 * p * q * r * b) + (-(p * q ^ 2)))))) : ℂ) = 0)
    (h4 : (((((2) + (2 * b)) + ((2 * a) + (2 * a * b))) + (((-4 * r * a * b) + (-2 * r ^ 2 * a * b)) + ((-(q * r * a)) + ((-(p * r * b)) + (-(p * q)))))) : ℂ) = 0)
    (h5 : (((((1) + (2 * b)) + ((b ^ 2) + (-2 * r * b ^ 2))) + (((-(r ^ 2 * b ^ 2)) + (-2 * q)) + ((-(q * r * b)) + (-(q ^ 2))))) : ℂ) = 0)
    (h6 : ((((2 * r) + ((r * a) + (-2 * r ^ 2 * a))) + ((-(r ^ 3 * a)) + ((-(p)) + (2 * p * r)))) : ℂ) = 0)
    (h7 : ((((2 * r) + ((r * b) + (-2 * r ^ 2 * b))) + ((-(r ^ 3 * b)) + ((-(q)) + (2 * q * r)))) : ℂ) = 0)
    : r = 0 := by
  have hr : (61193160 : ℂ) * r = 0 := by
    linear_combination ((((((((17805835860) + ((-15021895626 * b) + (36012480 * b ^ 2))) + ((-8788879392 * a) + ((324112320 * a * b) + (25662251609 * r)))) + (((48954302800 * r * b) + ((17153058864 * r * a) + (-864299520 * r * a * b))) + (((15488327756 * r ^ 2 * b) + (86927064 * r ^ 2 * a)) + ((-10222159302 * q) + (-49424064 * q * b))))) + ((((47312928 * q * a) + ((12466660502 * q * r) + (371425248 * q * r * b))) + (((786624336 * q * r * a) + (162056160 * q ^ 2)) + ((23656464 * q ^ 2 * a) + (3119674176 * q ^ 2 * r)))) + (((14056132615 * p) + ((-139827648 * p * b) + (6289864752 * p * r))) + (((379186608 * p * r * b) + (579552576 * p * q)) + ((12356016 * p * q * b) + (3114459360 * p * q * r))))))) * h1 + ((((((((-18204291594) + (-18483383994 * b)) + ((-279092400 * b ^ 2) + ((-26945023378 * r) + (-34011043912 * r * b)))) + (((-8597438306 * r * b ^ 2) + ((-36012480 * r * b ^ 3) + (-729012048 * r * a))) + ((3619782744 * r * a * b) + ((36012480 * r * a * b ^ 2) + (-14763373433 * r ^ 2 * b))))) + ((((-105341256 * r ^ 2 * b ^ 2) + ((-3114459360 * r ^ 2 * a) + (37999728 * r ^ 2 * a * b))) + ((-32558675356 * q) + ((5790344040 * q * b) + (-432149760 * q * b ^ 2)))) + (((9545141472 * q * a) + ((-324112320 * q * a * b) + (3270356475 * q * r))) + ((-41385623356 * q * r * b) + ((792274560 * q * r * b ^ 2) + (-19277819575 * q * r * a)))))) + (((((864299520 * q * r * a * b) + ((546299880 * q * r ^ 2 * b) + (-86927064 * q * r ^ 2 * a))) + ((2636370466 * q ^ 2) + ((49424064 * q ^ 2 * b) + (-47312928 * q ^ 2 * a)))) + (((2005471460 * q ^ 2 * r) + ((-1163699808 * q ^ 2 * r * b) + (-786624336 * q ^ 2 * r * a))) + ((-558193440 * q ^ 3) + ((-23656464 * q ^ 3 * a) + (-3119674176 * q ^ 3 * r))))) + ((((396137280 * p) + ((-2764245672 * p * b) + (396137280 * p * b ^ 2))) + ((5555810784 * p * r * b) + ((-792274560 * p * r * b ^ 2) + (-51962064 * p * r ^ 2 * b)))) + (((-2349504240 * p * q) + ((-51962064 * p * q * r) + (390487056 * p * q * r * b))) + ((-194715744 * p * q ^ 2) + ((-12356016 * p * q ^ 2 * b) + (-3114459360 * p * q ^ 2 * r)))))))) * h2 + ((((((-17587548564) + ((8672488080 * b) + (15376971954 * a))) + ((-360124800 * a * b) + ((-25929152897 * r) + (-17043464736 * r * b)))) + (((-49591591912 * r * a) + ((864299520 * r * a * b) + (-15818938388 * r ^ 2 * a))) + ((-13933521655 * q) + ((148272192 * q * a) + (-6239348352 * q * r))))) + ((((-359069232 * q * r * a) + ((10134571206 * p) + (-24712032 * p * b))) + ((22600896 * p * a) + ((-12679216334 * p * r) + (-779918544 * p * r * b)))) + (((-384836832 * p * r * a) + ((-545837424 * p * q) + (-23656464 * p * q * a))) + (((-3119674176 * p * q * r) + (-189065520 * p ^ 2)) + ((-12356016 * p ^ 2 * b) + (-3114459360 * p ^ 2 * r))))))) * h3)) + (((((((((125218368) + (-8837381229 * b)) + ((8903704773 * a) + ((-58894824 * a * b) + (27693936 * r)))) + (((-32640517698 * r * b) + ((756262080 * r * b ^ 2) + (33268712418 * r * a))) + ((169946448 * r * a * b) + ((-756262080 * r * a ^ 2) + (-565159567 * r ^ 2 * b))))) + ((((847046935 * r ^ 2 * a) + ((94162536 * r ^ 2 * a * b) + (25528343246 * q))) + ((-8660132064 * q * b) + ((-15747283306 * q * a) + (756262080 * q * a * b)))) + (((12484524624 * q * r) + ((25844293824 * q * r * b) + (41860891576 * q * r * a))) + ((-1656574080 * q * r * a * b) + ((7801624570 * q * r ^ 2 * a) + (12373684567 * q ^ 2)))))) + (((((-148272192 * q ^ 2 * a) + (6239348352 * q ^ 2 * r)) + ((755206512 * q ^ 2 * r * a) + ((-25765368398 * p) + (15531655618 * p * b)))) + (((8739241896 * p * a) + ((-756262080 * p * a * b) + (-12469977456 * p * r))) + ((-41374185208 * p * r * b) + ((-25913290800 * p * r * a) + (1656574080 * p * r * a * b))))) + ((((-7578858562 * p * r ^ 2 * b) + ((-60946032 * p * r ^ 2 * a) + (-26823168 * p * q))) + ((-2913960 * p * q * r) + ((779918544 * p * q * r * b) + (-786624336 * p * q * r * a)))) + (((767562528 * p * q ^ 2) + ((-12498902935 * p ^ 2) + (139827648 * p ^ 2 * b))) + ((-6237902688 * p ^ 2 * r) + ((-775323888 * p ^ 2 * r * b) + (-780974112 * p ^ 2 * q)))))))) * h4 + (((((((17953854858) + (18350736906 * a)) + ((396882048 * a ^ 2) + (26950828666 * r))) + (((767562528 * r * b) + (33523343512 * r * a)) + ((-3609195552 * r * a * b) + ((8261953874 * r * a ^ 2) + (3119674176 * r ^ 2 * b))))) + ((((14995087745 * r ^ 2 * a) + (-396137280 * q)) + ((2828221440 * q * a) + ((-396137280 * q * a ^ 2) + (-5681154912 * q * r * a)))) + (((792274560 * q * r * a ^ 2) + (32313564892 * p)) + ((-9428750160 * p * b) + ((-6428726112 * p * a) + (324112320 * p * a * b)))))) + (((((432149760 * p * a ^ 2) + (-3020938947 * p * r)) + ((19081195159 * p * r * b) + ((42510432868 * p * r * a) + (-864299520 * p * r * a * b)))) + (((-792274560 * p * r * a ^ 2) + (2352111648 * p * q)) + ((-383781264 * p * q * r * a) + ((-2548782370 * p ^ 2) + (24712032 * p ^ 2 * b))))) + ((((-22600896 * p ^ 2 * a) + (-1790001668 * p ^ 2 * r)) + ((779918544 * p ^ 2 * r * b) + ((1177111392 * p ^ 2 * r * a) + (174412176 * p ^ 2 * q)))) + (((23656464 * p ^ 2 * q * a) + (3119674176 * p ^ 2 * q * r)) + ((585202800 * p ^ 3) + ((12356016 * p ^ 3 * b) + (3114459360 * p ^ 3 * r)))))))) * h5) + ((((((((42430867332 * b) + (45231125484 * b ^ 2)) + ((-756262080 * b ^ 3) + (11299939118 * a))) + (((13398402400 * a * b) + (9247516226 * a * b ^ 2)) + ((36012480 * a * b ^ 3) + (729012048 * a ^ 2)))) + ((((-2863520664 * a ^ 2 * b) + (-36012480 * a ^ 2 * b ^ 2)) + ((19485036288 * r * b) + (17649398716 * r * b ^ 2))) + (((31020819463 * r * a * b) + (-82983816 * r * a * b ^ 2)) + ((3114459360 * r * a ^ 2) + (-37999728 * r * a ^ 2 * b))))) + (((((27187261076 * q * b) + (-8800829088 * q * b ^ 2)) + ((1858221757 * q * a) + (15285499400 * q * a * b))) + (((2124760711 * q * a ^ 2) + (8583792792 * q * r * b)) + ((3620496000 * q ^ 2 * b) + (-6454818144 * q ^ 2 * a)))) + ((((14465302436 * p * b) + (7352261972 * p * b ^ 2)) + ((3114459360 * p * a) + (3114459360 * p * a * b))) + (((8566812408 * p * r * b) + (-15263127304 * p * q * b)) + ((-6263883720 * p * q * a) + (3556520232 * p ^ 2 * b))))))) * h6 + ((((((-11462500910 * b) + ((-767562528 * b ^ 2) + (-43060549404 * a))) + (((-13473433600 * a * b) + (2852933472 * a * b ^ 2)) + ((-45924783324 * a ^ 2) + (-9251924690 * a ^ 2 * b)))) + (((756262080 * a ^ 3) + ((-3119674176 * r * b ^ 2) + (-19485036288 * r * a))) + (((-31514167327 * r * a * b) + (-17951539900 * r * a ^ 2)) + ((-3119674176 * q * b) + (-14727932708 * q * a))))) + ((((-3119674176 * q * a * b) + ((-7486940708 * q * a ^ 2) + (-8583792792 * q * r * a))) + (((-3620496000 * q ^ 2 * a) + (-1461404101 * p * b)) + ((-2037730423 * p * b ^ 2) + (-27107378372 * p * a)))) + (((-15420159392 * p * a * b) + ((8812194000 * p * a ^ 2) + (-8566812408 * p * r * a))) + (((6239348352 * p * q * b) + (15586222264 * p * q * a)) + ((6559748808 * p ^ 2 * b) + (-3634463328 * p ^ 2 * a))))))) * h7)))
  exact (mul_eq_zero.mp hr).resolve_left (by norm_num)

theorem coefficients_force_standard_star (p q r a b : ℂ)
    (h1 : ((((((r * b) + (2 * r * a)) + ((q) + (2 * q * a))) + (((q * a ^ 2) + (-2 * q * r * a ^ 2)) + ((-(q * r ^ 2 * a ^ 2)) + (2 * p * a)))) + ((((2 * p * a * b) + (-2 * p * r * b)) + ((-4 * p * r * a * b) + (-2 * p * r ^ 2 * a * b))) + (((-2 * p * q) + (-2 * p * q * r * a)) + ((-(p ^ 2 * r * b)) + (-(p ^ 2 * q)))))) : ℂ) = 0)
    (h2 : (((((1) + (2 * a)) + ((a ^ 2) + (-2 * r * a ^ 2))) + (((-(r ^ 2 * a ^ 2)) + (-2 * p)) + ((-(p * r * a)) + (-(p ^ 2))))) : ℂ) = 0)
    (h3 : ((((((2 * r * b) + (r * a)) + ((2 * q * b) + (2 * q * a * b))) + (((-2 * q * r * a) + (-4 * q * r * a * b)) + ((-2 * q * r ^ 2 * a * b) + (-(q ^ 2 * r * a))))) + ((((p) + (2 * p * b)) + ((p * b ^ 2) + (-2 * p * r * b ^ 2))) + (((-(p * r ^ 2 * b ^ 2)) + (-2 * p * q)) + ((-2 * p * q * r * b) + (-(p * q ^ 2)))))) : ℂ) = 0)
    (h4 : (((((2) + (2 * b)) + ((2 * a) + (2 * a * b))) + (((-4 * r * a * b) + (-2 * r ^ 2 * a * b)) + ((-(q * r * a)) + ((-(p * r * b)) + (-(p * q)))))) : ℂ) = 0)
    (h5 : (((((1) + (2 * b)) + ((b ^ 2) + (-2 * r * b ^ 2))) + (((-(r ^ 2 * b ^ 2)) + (-2 * q)) + ((-(q * r * b)) + (-(q ^ 2))))) : ℂ) = 0)
    (h6 : ((((2 * r) + ((r * a) + (-2 * r ^ 2 * a))) + ((-(r ^ 3 * a)) + ((-(p)) + (2 * p * r)))) : ℂ) = 0)
    (h7 : ((((2 * r) + ((r * b) + (-2 * r ^ 2 * b))) + ((-(r ^ 3 * b)) + ((-(q)) + (2 * q * r)))) : ℂ) = 0)
    : p = 0 ∧ q = 0 ∧ r = 0 ∧ a = -1 ∧ b = -1 := by
  have hr := r_eq_zero_of_coefficients p q r a b h1 h2 h3 h4 h5 h6 h7
  have hp : p = 0 := by simpa [hr] using h6
  have hq : q = 0 := by simpa [hr] using h7
  have ha2 : (a + 1) ^ 2 = 0 := by
    have hh := h2
    simp only [hp, hr, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero, neg_zero] at hh
    linear_combination hh
  have hb2 : (b + 1) ^ 2 = 0 := by
    have hh := h5
    simp only [hq, hr, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero, neg_zero] at hh
    linear_combination hh
  have ha1 : a + 1 = 0 := by
    have hh : (a + 1) * (a + 1) = 0 := by simpa only [pow_two] using ha2
    exact (mul_eq_zero.mp hh).elim id id
  have hb1 : b + 1 = 0 := by
    have hh : (b + 1) * (b + 1) = 0 := by simpa only [pow_two] using hb2
    exact (mul_eq_zero.mp hh).elim id id
  refine ⟨hp, hq, hr, ?_, ?_⟩
  · linear_combination ha1
  · linear_combination hb1

end StarPencil

namespace StarPencil

theorem standard_star_triangle_extension_impossible (u v d f : ℂ)
    (h5 : -v - 4*d - 2*f - 2 = 0)
    (h10 : -2*(u + v + 3*d + 3*f + 1) = 0)
    (h13 : -4*(2*u + v + 2*d + f + 3) = 0)
    (h16 : -u - 2*d - 4*f - 2 = 0)
    (h19 : -4*(u + 2*v + d + 2*f + 3) = 0) : False := by
  have h : (36 : ℂ) = 0 := by
    linear_combination -h13 - h19 - 8*h5 - 8*h16 + 10*h10
  norm_num at h

end StarPencil

section ModularTransferIntegration
set_option maxHeartbeats 800000 in
theorem no_common_complex_zero_of_modular_coprime
    (f g : Polynomial ℤ) (p m n : ℕ) [Fact p.Prime]
    (hfdeg : f.natDegree ≤ m) (hgdeg : g.natDegree ≤ n) (hmpos : 0 < m)
    (hfmod : (f.map (Int.castRingHom (ZMod p))).natDegree = m)
    (hgmod : (g.map (Int.castRingHom (ZMod p))).natDegree = n)
    (hcoprime : IsCoprime (f.map (Int.castRingHom (ZMod p)))
      (g.map (Int.castRingHom (ZMod p))))
    (z : ℂ)
    (hf : (f.map (Int.castRingHom ℂ)).eval z = 0)
    (hg : (g.map (Int.castRingHom ℂ)).eval z = 0) : False := by
  have hc : Polynomial.resultant (f.map (Int.castRingHom ℂ))
      (g.map (Int.castRingHom ℂ)) m n = 0 :=
    resultant_zero_of_common_root _ _ z m n
      (Polynomial.natDegree_map_le.trans hfdeg)
      (Polynomial.natDegree_map_le.trans hgdeg) hmpos hf hg
  have hz : Polynomial.resultant f g m n = 0 := by
    have hcast : ((Polynomial.resultant f g m n : ℤ) : ℂ) = 0 := by
      simpa only [Polynomial.resultant_map_map, Int.coe_castRingHom] using hc
    exact Int.cast_eq_zero.mp hcast
  have hp : Polynomial.resultant (f.map (Int.castRingHom (ZMod p)))
      (g.map (Int.castRingHom (ZMod p))) m n = 0 := by
    rw [Polynomial.resultant_map_map, hz, map_zero]
  rw [← hfmod, ← hgmod] at hp
  exact Polynomial.resultant_ne_zero _ _ hcoprime hp

end ModularTransferIntegration

end PEqualNP.Outside.L_gct_231_aux
