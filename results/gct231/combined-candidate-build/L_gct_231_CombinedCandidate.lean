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

end PEqualNP.Outside.L_gct_231_aux
