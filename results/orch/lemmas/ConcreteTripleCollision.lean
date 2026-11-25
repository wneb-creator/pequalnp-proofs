import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases



namespace PEqualNP.Outside.L_gct_231.RowKernel

lemma permanent_zero_row (M : Matrix (Fin 4) (Fin 4) ℂ) (i : Fin 4)
    (hz : ∀ j : Fin 4, M i j=0) : Matrix.permanent M=0 := by
  unfold Matrix.permanent
  apply Finset.sum_eq_zero
  intro σ hσ
  apply Finset.prod_eq_zero (Finset.mem_univ (σ.symm i))
  simpa only [Equiv.apply_symm_apply] using hz (σ.symm i)

lemma constant_row_zero (T : Fin 4 × Fin 4 → ℂ) (i : Fin 4) (c : ℂ)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+z*T (r,s))=24)
    (hc : ∀ j : Fin 4, T (i,j)=c) : c=0 := by
  by_contra hn
  have hzero : Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+(-c⁻¹)*T (r,s))=0 := by
    apply permanent_zero_row _ i
    intro j
    simp [Matrix.of_apply,hc,inv_mul_cancel₀ hn]
  have hh := hp (-c⁻¹)
  rw [hzero] at hh
  norm_num at hh

def rowDifference (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (i : Fin 4) :
    L →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun := fun T j => T.1 (i,j.succ)-T.1 (i,0)
  map_add' := by
    intro T S
    funext j
    change (T.1 (i,j.succ)+S.1 (i,j.succ))-(T.1 (i,0)+S.1 (i,0)) =
      (T.1 (i,j.succ)-T.1 (i,0))+(S.1 (i,j.succ)-S.1 (i,0))
    abel
  map_smul' := by
    intro z T
    funext j
    change z*T.1 (i,j.succ)-z*T.1 (i,0)=z*(T.1 (i,j.succ)-T.1 (i,0))
    exact (mul_sub _ _ _).symm

lemma rowDifference_eq_zero_iff
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hp : ∀ T ∈ L, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+T (r,s))=24)
    (i : Fin 4) (T : L) :
    rowDifference L i T=0 ↔ ∀ j : Fin 4, T.1 (i,j)=0 := by
  constructor
  · intro hz
    have hc : ∀ j : Fin 4, T.1 (i,j)=T.1 (i,0) := by
      intro j
      refine Fin.cases rfl (fun k => ?_) j
      have he := congrFun hz k
      exact sub_eq_zero.mp he
    have hpz (z : ℂ) : Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
        (1 : ℂ)+z*T.1 (r,s))=24 := by
      simpa only [Pi.smul_apply,smul_eq_mul] using hp (z • T.1) (L.smul_mem z T.2)
    have h0 := constant_row_zero T.1 i (T.1 (i,0)) hpz hc
    exact fun j => (hc j).trans h0
  · intro hz
    funext j
    change T.1 (i,j.succ)-T.1 (i,0)=0
    rw [hz, hz, sub_self]

lemma nonzero_zero_row_of_not_injective
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hp : ∀ T ∈ L, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+T (r,s))=24)
    (i : Fin 4) (hs : ¬ Function.Injective (rowDifference L i)) :
    ∃ T : Fin 4 × Fin 4 → ℂ, T ∈ L ∧ T≠0 ∧ ∀ j : Fin 4, T (i,j)=0 := by
  have hker : (rowDifference L i).ker≠⊥ := by
    intro hh
    exact hs (LinearMap.ker_eq_bot.mp hh)
  obtain ⟨T,hT,hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨T.1,T.2,?_,(rowDifference_eq_zero_iff L hp i T).mp hT⟩
  intro hz
  apply hne
  exact Subtype.ext hz

lemma nonzero_zero_row_of_not_surjective
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (h3 : Module.finrank ℂ L=3)
    (hp : ∀ T ∈ L, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+T (r,s))=24)
    (i : Fin 4) (hs : ¬ Function.Surjective (rowDifference L i)) :
    ∃ T : Fin 4 × Fin 4 → ℂ, T ∈ L ∧ T≠0 ∧ ∀ j : Fin 4, T (i,j)=0 := by
  apply nonzero_zero_row_of_not_injective L hp i
  intro hinj
  apply hs
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
  simpa using h3

lemma row_dichotomy
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (h3 : Module.finrank ℂ L=3)
    (hp : ∀ T ∈ L, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+T (r,s))=24)
    (i : Fin 4) :
    Function.Bijective (rowDifference L i) ∨
    ∃ T : Fin 4 × Fin 4 → ℂ, T ∈ L ∧ T≠0 ∧ ∀ j : Fin 4, T (i,j)=0 := by
  by_cases hs : Function.Surjective (rowDifference L i)
  · left
    refine ⟨?_,hs⟩
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr hs
    simpa using h3
  · exact Or.inr (nonzero_zero_row_of_not_surjective L h3 hp i hs)

lemma zero_row_directions_of_singular_rows
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (h3 : Module.finrank ℂ L=3)
    (hp : ∀ T ∈ L, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+T (r,s))=24)
    (hs : ∀ i : Fin 4, ¬ Function.Surjective (rowDifference L i)) :
    ∃ A : Fin 4 → (Fin 4 × Fin 4 → ℂ),
      ∀ i : Fin 4, A i ∈ L ∧ A i≠0 ∧ ∀ j : Fin 4, A i (i,j)=0 := by
  choose A hA using fun i => nonzero_zero_row_of_not_surjective L h3 hp i (hs i)
  exact ⟨A,hA⟩

lemma row_chart_of_bijective
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (i : Fin 4)
    (hb : Function.Bijective (rowDifference L i)) :
    ∃ F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ),
      Function.Injective F ∧ F.range=L ∧
      ∀ (x : Fin 3 → ℂ) (j : Fin 3), F x (i,j.succ)-F x (i,0)=x j := by
  let e : L ≃ₗ[ℂ] (Fin 3 → ℂ) := LinearEquiv.ofBijective (rowDifference L i) hb
  let F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) := L.subtype.comp e.symm.toLinearMap
  refine ⟨F,?_,?_,?_⟩
  · intro x y hxy
    apply e.symm.injective
    exact Subtype.ext hxy
  · ext T
    constructor
    · rintro ⟨x,rfl⟩
      exact (e.symm x).2
    · intro hT
      refine ⟨e ⟨T,hT⟩,?_⟩
      change (e.symm (e ⟨T,hT⟩)).1=T
      simp only [LinearEquiv.symm_apply_apply]
  · intro x j
    exact congrFun (e.apply_symm_apply x) j

lemma row_chart_of_surjective
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (h3 : Module.finrank ℂ L=3) (i : Fin 4)
    (hs : Function.Surjective (rowDifference L i)) :
    ∃ F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ),
      Function.Injective F ∧ F.range=L ∧
      ∀ (x : Fin 3 → ℂ) (j : Fin 3), F x (i,j.succ)-F x (i,0)=x j := by
  apply row_chart_of_bijective L i
  refine ⟨?_,hs⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr hs
  simpa using h3

end PEqualNP.Outside.L_gct_231.RowKernel


namespace PEqualNP.Outside.L_gct_231.Cover

lemma perm_first_two (i j : Fin 4) (hij : i≠j) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0=i ∧ σ 1=j := by
  let τ : Equiv.Perm (Fin 4) := Equiv.swap 0 i
  have hτ : τ 0=i := by simp [τ]
  have hj0 : τ.symm j≠0 := by
    intro hh
    have he := congrArg τ hh
    rw [Equiv.apply_symm_apply,hτ] at he
    exact hij he.symm
  let σ : Equiv.Perm (Fin 4) := (Equiv.swap 1 (τ.symm j)).trans τ
  refine ⟨σ,?_,?_⟩
  · change τ (Equiv.swap 1 (τ.symm j) 0)=i
    have hh : Equiv.swap 1 (τ.symm j) 0=0 := by
      simp [Equiv.swap_apply_def,Ne.symm hj0]
    rw [hh,hτ]
  · change τ (Equiv.swap 1 (τ.symm j) 1)=j
    rw [Equiv.swap_apply_left,Equiv.apply_symm_apply]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def directionLine (v : V) : Submodule ℂ V := Submodule.span ℂ ({v} : Set V)

lemma pair_independent_iff_lines_ne (A B : V) (hA : A≠0) (hB : B≠0) :
    LinearIndependent ℂ ![A,B] ↔ directionLine A≠directionLine B := by
  rw [LinearIndependent.pair_iff' hA]
  constructor
  · intro hind heq
    have hmem : B ∈ directionLine A := by
      rw [heq]
      exact Submodule.mem_span_singleton_self B
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hmem
    exact hind a ha
  · intro hne a ha
    have ha0 : a≠0 := by
      intro hh
      rw [hh,zero_smul] at ha
      exact hB ha.symm
    apply hne
    change Submodule.span ℂ ({A} : Set V)=Submodule.span ℂ ({B} : Set V)
    rw [←ha,Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha0)]

lemma four_direction_cover (v : Fin 4 → V) (hne : ∀ i, v i≠0)
    (htriple : ∀ i j k : Fin 4, i≠j → i≠k → j≠k →
      directionLine (v i)=directionLine (v j) →
      directionLine (v i)=directionLine (v k) → False)
    (hdouble : ∀ σ : Equiv.Perm (Fin 4),
      directionLine (v (σ 0))=directionLine (v (σ 1)) →
      directionLine (v (σ 2))=directionLine (v (σ 3)) → False)
    (hcollinear : ∀ i j k : Fin 4, i≠j → i≠k → j≠k →
      LinearIndependent ℂ ![v i,v j] → LinearIndependent ℂ ![v i,v k] →
      LinearIndependent ℂ ![v j,v k] → ¬LinearIndependent ℂ ![v i,v j,v k] → False)
    (hrepeated : ∀ σ : Equiv.Perm (Fin 4),
      directionLine (v (σ 0))=directionLine (v (σ 1)) →
      LinearIndependent ℂ ![v (σ 0),v (σ 2),v (σ 3)] → False)
    (hframe : (∀ i j k : Fin 4, i≠j → i≠k → j≠k →
      LinearIndependent ℂ ![v i,v j,v k]) → False) : False := by
  classical
  by_cases hp : Pairwise (fun i j : Fin 4 => directionLine (v i)≠directionLine (v j))
  · by_cases hf : ∀ i j k : Fin 4, i≠j → i≠k → j≠k → LinearIndependent ℂ ![v i,v j,v k]
    · exact hframe hf
    · simp only [not_forall,not_imp] at hf
      obtain ⟨i,j,k,hij,hik,hjk,hdep⟩ := hf
      exact hcollinear i j k hij hik hjk
        ((pair_independent_iff_lines_ne _ _ (hne i) (hne j)).mpr (hp hij))
        ((pair_independent_iff_lines_ne _ _ (hne i) (hne k)).mpr (hp hik))
        ((pair_independent_iff_lines_ne _ _ (hne j) (hne k)).mpr (hp hjk)) hdep
  · simp only [Pairwise,not_forall,not_imp,not_not] at hp
    obtain ⟨i,j,hij,heq⟩ := hp
    obtain ⟨σ,hσ0,hσ1⟩ := perm_first_two i j hij
    have h01 : directionLine (v (σ 0))=directionLine (v (σ 1)) := by rw [hσ0,hσ1]; exact heq
    have hi01 : σ 0≠σ 1 := σ.injective.ne (by decide)
    have hi02 : σ 0≠σ 2 := σ.injective.ne (by decide)
    have hi03 : σ 0≠σ 3 := σ.injective.ne (by decide)
    have hi12 : σ 1≠σ 2 := σ.injective.ne (by decide)
    have hi13 : σ 1≠σ 3 := σ.injective.ne (by decide)
    have hi23 : σ 2≠σ 3 := σ.injective.ne (by decide)
    have h02 : directionLine (v (σ 0))≠directionLine (v (σ 2)) :=
      fun hh => htriple (σ 0) (σ 1) (σ 2) hi01 hi02 hi12 h01 hh
    have h03 : directionLine (v (σ 0))≠directionLine (v (σ 3)) :=
      fun hh => htriple (σ 0) (σ 1) (σ 3) hi01 hi03 hi13 h01 hh
    by_cases h23 : directionLine (v (σ 2))=directionLine (v (σ 3))
    · exact hdouble σ h01 h23
    · by_cases hind : LinearIndependent ℂ ![v (σ 0),v (σ 2),v (σ 3)]
      · exact hrepeated σ h01 hind
      · exact hcollinear (σ 0) (σ 2) (σ 3) hi02 hi03 hi23
          ((pair_independent_iff_lines_ne _ _ (hne _) (hne _)).mpr h02)
          ((pair_independent_iff_lines_ne _ _ (hne _) (hne _)).mpr h03)
          ((pair_independent_iff_lines_ne _ _ (hne _) (hne _)).mpr h23) hind

end PEqualNP.Outside.L_gct_231.Cover

namespace PEqualNP.Outside.L_gct_231.GlobalCover

open RowKernel Cover

abbrev Ambient := Fin 4 × Fin 4 → ℂ

def Level (L : Submodule ℂ Ambient) : Prop :=
  (∀ T ∈ L, ∀ i j : Fin 4, T (i,j)=T (j,i)) ∧
  ∀ T ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1 : ℂ)+T (i,j))=24

def Directions (L : Submodule ℂ Ambient) (A : Fin 4 → Ambient) : Prop :=
  ∀ i : Fin 4, A i ∈ L ∧ A i≠0 ∧ ∀ j : Fin 4, A i (i,j)=0

lemma conditional_refutation
    (hfull : ∀ (L : Submodule ℂ Ambient), Module.finrank ℂ L=3 → Level L →
      ∀ i : Fin 4, Function.Surjective (rowDifference L i) → False)
    (htriple : ∀ (L : Submodule ℂ Ambient), Module.finrank ℂ L=3 → Level L →
      ∀ A : Fin 4 → Ambient, Directions L A →
      ∀ i j k : Fin 4, i≠j → i≠k → j≠k →
        directionLine (A i)=directionLine (A j) →
        directionLine (A i)=directionLine (A k) → False)
    (hdouble : ∀ (L : Submodule ℂ Ambient), Module.finrank ℂ L=3 → Level L →
      ∀ A : Fin 4 → Ambient, Directions L A → ∀ σ : Equiv.Perm (Fin 4),
        directionLine (A (σ 0))=directionLine (A (σ 1)) →
        directionLine (A (σ 2))=directionLine (A (σ 3)) → False)
    (hcollinear : ∀ (L : Submodule ℂ Ambient), Module.finrank ℂ L=3 → Level L →
      ∀ A : Fin 4 → Ambient, Directions L A →
      ∀ i j k : Fin 4, i≠j → i≠k → j≠k →
        LinearIndependent ℂ ![A i,A j] → LinearIndependent ℂ ![A i,A k] →
        LinearIndependent ℂ ![A j,A k] → ¬LinearIndependent ℂ ![A i,A j,A k] → False)
    (hrepeated : ∀ (L : Submodule ℂ Ambient), Module.finrank ℂ L=3 → Level L →
      ∀ A : Fin 4 → Ambient, Directions L A → ∀ σ : Equiv.Perm (Fin 4),
        directionLine (A (σ 0))=directionLine (A (σ 1)) →
        LinearIndependent ℂ ![A (σ 0),A (σ 2),A (σ 3)] → False)
    (hframe : ∀ (L : Submodule ℂ Ambient), Module.finrank ℂ L=3 → Level L →
      ∀ A : Fin 4 → Ambient, Directions L A →
        (∀ i j k : Fin 4, i≠j → i≠k → j≠k → LinearIndependent ℂ ![A i,A j,A k]) → False) :
    ¬ (∃ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ), Module.finrank ℂ L=3 ∧
      (∀ T ∈ L, ∀ i j : Fin 4, T (i,j)=T (j,i)) ∧
      ∀ T ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1 : ℂ)+T (i,j))=24) := by
  rintro ⟨L,h3,hs,hp⟩
  have hL : Level L := ⟨hs,hp⟩
  have hsing (i : Fin 4) : ¬Function.Surjective (rowDifference L i) := hfull L h3 hL i
  obtain ⟨A,hA⟩ := zero_row_directions_of_singular_rows L h3 hp hsing
  apply four_direction_cover A (fun i => (hA i).2.1)
  · exact htriple L h3 hL A hA
  · exact hdouble L h3 hL A hA
  · exact hcollinear L h3 hL A hA
  · exact hrepeated L h3 hL A hA
  · exact hframe L h3 hL A hA

end PEqualNP.Outside.L_gct_231.GlobalCover


namespace PEqualNP.Outside.L_gct_231_aux.Diagonal

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


lemma diagonal_zero (u : Fin 4 → ℂ)
    (h : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (1 : ℂ) + z * (if i = j then u i else 0)) = 24) : u = 0 := by
  let e1 := u 0 + u 1 + u 2 + u 3
  let e2 := u 0 * u 1 + u 0 * u 2 + u 0 * u 3 +
    u 1 * u 2 + u 1 * u 3 + u 2 * u 3
  let e3 := u 0 * u 1 * u 2 + u 0 * u 1 * u 3 +
    u 0 * u 2 * u 3 + u 1 * u 2 * u 3
  let e4 := u 0 * u 1 * u 2 * u 3
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  have hm2 := h (-2)
  simp [perm4, Matrix.of_apply] at h1 hm1 h2 hm2
  have he1 : e1 = 0 := by
    dsimp [e1]
    linear_combination (1 / 9 : ℂ) * h1 - (1 / 9 : ℂ) * hm1 -
      (1 / 72 : ℂ) * h2 + (1 / 72 : ℂ) * hm2
  have he2 : e2 = 0 := by
    dsimp [e2]
    linear_combination (1 / 3 : ℂ) * h1 + (1 / 3 : ℂ) * hm1 -
      (1 / 48 : ℂ) * h2 - (1 / 48 : ℂ) * hm2
  have he3 : e3 = 0 := by
    dsimp [e3]
    linear_combination -(1 / 6 : ℂ) * h1 + (1 / 6 : ℂ) * hm1 +
      (1 / 12 : ℂ) * h2 - (1 / 12 : ℂ) * hm2
  have he4 : e4 = 0 := by
    dsimp [e4]
    linear_combination -(1 / 6 : ℂ) * h1 - (1 / 6 : ℂ) * hm1 +
      (1 / 24 : ℂ) * h2 + (1 / 24 : ℂ) * hm2
  dsimp [e1, e2, e3, e4] at he1 he2 he3 he4
  funext i
  change u i = 0
  apply eq_zero_of_pow_eq_zero (n := 4)
  fin_cases i
  · change u 0 ^ 4 = 0
    linear_combination (u 0 ^ 3) * he1 - (u 0 ^ 2) * he2 + (u 0) * he3 - he4
  · change u 1 ^ 4 = 0
    linear_combination (u 1 ^ 3) * he1 - (u 1 ^ 2) * he2 + (u 1) * he3 - he4
  · change u 2 ^ 4 = 0
    linear_combination (u 2 ^ 3) * he1 - (u 2 ^ 2) * he2 + (u 2) * he3 - he4
  · change u 3 ^ 4 = 0
    linear_combination (u 3 ^ 3) * he1 - (u 3 ^ 2) * he2 + (u 3) * he3 - he4

end PEqualNP.Outside.L_gct_231_aux.Diagonal

namespace PEqualNP.Outside.L_gct_231.GlobalCover

open RowKernel Cover

lemma scaled_level (L : Submodule ℂ Ambient) (hL : Level L) (T : Ambient) (hT : T∈L) :
    ∀ z : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) => (1:ℂ)+z*T (r,s))=24 := by
  intro z
  simpa only [Pi.smul_apply,smul_eq_mul] using hL.2 (z • T) (L.smul_mem z hT)

lemma row_zero_of_same_line (T S : Ambient) (i : Fin 4)
    (heq : directionLine T=directionLine S) (hS : ∀ j : Fin 4, S (i,j)=0) :
    ∀ j : Fin 4, T (i,j)=0 := by
  have hmem : T∈directionLine S := by
    rw [←heq]
    exact Submodule.mem_span_singleton_self T
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hmem
  intro j
  rw [←hc]
  simp only [Pi.smul_apply,smul_eq_mul,hS,mul_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma three_zero_rows_zero (T : Ambient)
    (hs : ∀ r s : Fin 4, T (r,s)=T (s,r))
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) => (1:ℂ)+z*T (r,s))=24)
    (i j k : Fin 4) (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (hi : ∀ r : Fin 4, T (i,r)=0) (hj : ∀ r : Fin 4, T (j,r)=0)
    (hk : ∀ r : Fin 4, T (k,r)=0) : T=0 := by
  have hdiag (r s : Fin 4) (hrs : r≠s) : T (r,s)=0 := by
    by_cases hri : r=i
    · simpa only [hri] using hi s
    by_cases hrj : r=j
    · simpa only [hrj] using hj s
    by_cases hrk : r=k
    · simpa only [hrk] using hk s
    by_cases hsi : s=i
    · rw [hs,hsi]
      exact hi r
    by_cases hsj : s=j
    · rw [hs,hsj]
      exact hj r
    by_cases hsk : s=k
    · rw [hs,hsk]
      exact hk r
    have hb := Finset.card_le_card (Finset.subset_univ ({i,j,k,r,s} : Finset (Fin 4)))
    simp [hij,hik,hjk,Ne.symm hri,Ne.symm hrj,Ne.symm hrk,
      Ne.symm hsi,Ne.symm hsj,Ne.symm hsk,hrs] at hb
  have hz : (fun r : Fin 4 => T (r,r))=0 := by
    apply PEqualNP.Outside.L_gct_231_aux.Diagonal.diagonal_zero
    intro z
    convert hp z using 1
    congr 1
    ext r s
    simp only [Matrix.of_apply]
    by_cases hrs : r=s
    · simp [hrs]
    · simp [hrs,hdiag r s hrs]
  funext p
  rcases p with ⟨r,s⟩
  change T (r,s)=0
  by_cases hrs : r=s
  · subst s
    exact congrFun hz r
  · exact hdiag r s hrs

lemma triple_collision_impossible (L : Submodule ℂ Ambient) (hL : Level L)
    (A : Fin 4 → Ambient) (hA : Directions L A)
    (i j k : Fin 4) (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (heqj : directionLine (A i)=directionLine (A j))
    (heqk : directionLine (A i)=directionLine (A k)) : False := by
  apply (hA i).2.1
  exact three_zero_rows_zero (A i) (hL.1 _ (hA i).1)
    (scaled_level L hL _ (hA i).1) i j k hij hik hjk (hA i).2.2
    (row_zero_of_same_line _ _ j heqj (hA j).2.2)
    (row_zero_of_same_line _ _ k heqk (hA k).2.2)

end PEqualNP.Outside.L_gct_231.GlobalCover
