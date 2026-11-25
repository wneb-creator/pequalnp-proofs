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


end PEqualNP.Outside.L_gct_231_aux
