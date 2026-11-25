import Mathlib
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem three_edge_orbits :
    ∀ pick : Fin 3 → Fin 6, Function.Injective pick →
      ∃ p : Equiv.Perm (Fin 4), ∃ q : Equiv.Perm (Fin 3), ∃ kind : Fin 3,
        ∀ k : Fin 3, SameUnorderedEnds
          (p (edgeEnds (pick (q k))).1, p (edgeEnds (pick (q k))).2)
          (edgeEnds (canonicalEdges kind k)) := by
  unfold SameUnorderedEnds
  decide

end PEqualNP.Outside.L_gct_231_aux
