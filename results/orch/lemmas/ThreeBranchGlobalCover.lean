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
import Mathlib.Tactic.FieldSimp





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



namespace PEqualNP.Outside.L_gct_231.TwoBlock

lemma branch_zero (h t x y : ℂ)
    (hh : h ^ 2 = 2)
    (hy : y * (2*h*x+t+3*y) = 0)
    (hq : -3*t^2-12*t*y+4*x^2-6*y^2 = 0)
    (hc : -h*t^2*y-5*h*t*y^2+4*h*x^2*y-6*h*y^3+t^2*x+2*t*x*y-4*x*y^2 = 0) :
    t = 0 ∧ x = 0 ∧ y = 0 := by
  by_cases hy0 : y = 0
  · subst y
    have hx3 : x ^ 3 = 0 := by
      linear_combination (x/4)*hq + (3/4 : ℂ)*hc
    have hx : x = 0 := eq_zero_of_pow_eq_zero hx3
    subst x
    have ht2 : t ^ 2 = 0 := by linear_combination (-1/3 : ℂ)*hq
    exact ⟨eq_zero_of_pow_eq_zero ht2, rfl, rfl⟩
  · have hl : 2*h*x+t+3*y = 0 := (mul_eq_zero.mp hy).resolve_left hy0
    have ht : t = -2*h*x-3*y := by linear_combination hl
    rw [ht] at hq hc
    have hQ : -20*x^2-12*h*x*y+3*y^2 = 0 := by
      linear_combination hq + 12*x^2*hh
    have hRprod : x * (8*x^2+4*h*x*y-5*y^2) = 0 := by
      linear_combination hc - 2*x*(-2*h*x*y+2*x^2-y^2)*hh
    by_cases hx0 : x = 0
    · have hy2 : y ^ 2 = 0 := by
        subst x
        linear_combination (1/3 : ℂ)*hQ
      exact False.elim (hy0 (eq_zero_of_pow_eq_zero hy2))
    · have hR : 8*x^2+4*h*x*y-5*y^2 = 0 :=
        (mul_eq_zero.mp hRprod).resolve_left hx0
      have hxl : x * (19*x+12*h*y) = 0 := by
        linear_combination (-5/4 : ℂ)*hQ - (3/4 : ℂ)*hR
      have hL : 19*x+12*h*y = 0 := (mul_eq_zero.mp hxl).resolve_left hx0
      have hx2 : x ^ 2 = 0 := by
        linear_combination ((115*x-12*h*y)/265)*hL +
          (144*y^2/265)*hh + (96/265 : ℂ)*hQ
      exact False.elim (hx0 (eq_zero_of_pow_eq_zero hx2))

lemma quadrics_and_cubic_zero (h t x y z : ℂ)
    (hh : h ^ 2 = 2)
    (h0 : (y-z)*(y+z) = 0)
    (h1 : (y+z)*(4*h*x+2*t+5*y+z) = 0)
    (h2 : (y-z)*(4*h*x-2*t-5*y+z) = 0)
    (hq : -3*t^2-12*t*y+4*x^2-9*y^2+3*z^2 = 0)
    (hc : -h*t^2*z-5*h*t*y*z+4*h*x^2*z-6*h*y^2*z+
      t^2*x+2*t*x*y-2*x*y^2-2*x*z^2 = 0) :
    t = 0 ∧ x = 0 ∧ y = 0 ∧ z = 0 := by
  rcases mul_eq_zero.mp h0 with hm | hp
  · have hz : z = y := (sub_eq_zero.mp hm).symm
    subst z
    have hy : y*(2*h*x+t+3*y) = 0 := by linear_combination (1/4 : ℂ)*h1
    have hq' : -3*t^2-12*t*y+4*x^2-6*y^2 = 0 := by linear_combination hq
    have hc' : -h*t^2*y-5*h*t*y^2+4*h*x^2*y-6*h*y^3+
        t^2*x+2*t*x*y-4*x*y^2 = 0 := by linear_combination hc
    rcases branch_zero h t x y hh hy hq' hc' with ⟨ht, hx, hy0⟩
    exact ⟨ht, hx, hy0, hy0⟩
  · have hz : z = -y := by linear_combination hp
    rw [hz] at h2 hq hc
    have hh' : (-h)^2 = 2 := by linear_combination hh
    have hy : y*(2*(-h)*x+t+3*y) = 0 := by linear_combination (-1/4 : ℂ)*h2
    have hq' : -3*t^2-12*t*y+4*x^2-6*y^2 = 0 := by linear_combination hq
    have hc' : -(-h)*t^2*y-5*(-h)*t*y^2+4*(-h)*x^2*y-6*(-h)*y^3+
        t^2*x+2*t*x*y-4*x*y^2 = 0 := by linear_combination hc
    rcases branch_zero (-h) t x y hh' hy hq' hc' with ⟨ht, hx, hy0⟩
    refine ⟨ht, hx, hy0, ?_⟩
    simpa only [hy0, neg_zero] using hz


namespace MatrixBridge

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


def blockA (h : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![((-1) + h), 1, 0, 0], ![1, ((-1) + ((-1) * h)), 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]

def blockB (h : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, ((-1) + h), 1], ![0, 0, 1, ((-1) + ((-1) * h))]]

def extension (h t x y z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![(((-2) * z) + (t * ((-1) + h)) + (x * ((-2) + h)) + (y * ((-4) + (2 * h)))), 0, (x + z), (x + y)], ![0, ((2 * z) + (t * (1 + h)) + (y * (4 + (2 * h))) + ((-1) * x * (2 + h))), (x + ((-1) * y)), (x + ((-1) * z))], ![(x + z), (x + ((-1) * y)), (((-2) * z) + (t * (1 + ((-1) * h))) + (x * ((-2) + h)) + (y * (4 + ((-2) * h)))), 0], ![(x + y), (x + ((-1) * z)), 0, ((2 * z) + (t * ((-1) + ((-1) * h))) + ((-1) * x * (2 + h)) + ((-1) * y * (4 + (2 * h))))]]

def coefficient2 (h t x y z U V : ℂ) : ℂ :=
  (((-36) * (y ^ 2)) + ((-12) * (t ^ 2)) + (12 * (z ^ 2)) + (16 * (x ^ 2)) + (h * (((-16) * U * x * y) + ((-16) * U * x * z) + ((-16) * V * x * z) + (16 * V * x * y))) + ((-48) * t * y) + ((-20) * U * (y ^ 2)) + ((-20) * V * (y ^ 2)) + ((-4) * U * (z ^ 2)) + ((-4) * V * (z ^ 2)) + ((-36) * U * V * (y ^ 2)) + ((-24) * U * y * z) + ((-8) * U * t * y) + ((-8) * U * t * z) + ((-8) * V * t * y) + (8 * V * t * z) + (24 * V * y * z) + (36 * U * V * (z ^ 2)))

def coefficient3 (h t x y z U V : ℂ) : ℂ :=
  ((h * (((-36) * U * (y ^ 3)) + ((-32) * z * (x ^ 2)) + ((-20) * U * (z ^ 3)) + ((-20) * V * (z ^ 3)) + (8 * z * (t ^ 2)) + (36 * V * (y ^ 3)) + (48 * z * (y ^ 2)) + ((-60) * V * y * (z ^ 2)) + ((-20) * V * t * (z ^ 2)) + ((-16) * V * y * (x ^ 2)) + ((-4) * V * y * (t ^ 2)) + (4 * U * y * (t ^ 2)) + (4 * U * z * (t ^ 2)) + (4 * V * z * (t ^ 2)) + (16 * U * y * (x ^ 2)) + (16 * U * z * (x ^ 2)) + (16 * V * z * (x ^ 2)) + (20 * U * t * (z ^ 2)) + (40 * t * y * z) + (44 * U * z * (y ^ 2)) + (44 * V * z * (y ^ 2)) + (60 * U * y * (z ^ 2)) + (20 * U * t * y * z) + (20 * V * t * y * z))) + ((-8) * x * (t ^ 2)) + (16 * x * (y ^ 2)) + (16 * x * (z ^ 2)) + ((-16) * t * x * y) + (16 * U * x * (y ^ 2)) + (16 * V * x * (y ^ 2)) + (40 * U * x * (z ^ 2)) + (40 * V * x * (z ^ 2)) + ((-56) * V * x * y * z) + ((-24) * V * t * x * z) + (24 * U * t * x * y) + (24 * U * t * x * z) + (24 * V * t * x * y) + (56 * U * x * y * z))

def coefficient4 (h t x y z U V : ℂ) : ℂ :=
  ((t ^ 4) + (24 * (x ^ 4)) + (25 * (z ^ 4)) + (81 * (y ^ 4)) + (h * (((-40) * x * (z ^ 3)) + (32 * z * (x ^ 3)) + ((-152) * x * z * (y ^ 2)) + ((-16) * x * z * (t ^ 2)) + ((-128) * t * x * y * z))) + ((-246) * (y ^ 2) * (z ^ 2)) + ((-96) * (x ^ 2) * (y ^ 2)) + ((-30) * (t ^ 2) * (z ^ 2)) + ((-18) * (t ^ 2) * (y ^ 2)) + ((-12) * (t ^ 2) * (x ^ 2)) + ((-8) * (x ^ 2) * (z ^ 2)) + ((-160) * t * y * (z ^ 2)) + ((-32) * t * y * (x ^ 2)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma permanent_expansion (h t x y z U V W : ℂ) (hh : h^2 = 2) :
    Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + U*blockA h r s + V*blockB h r s + W*extension h t x y z r s) - 24 =
    W^2*(coefficient2 h t x y z U V + W*coefficient3 h t x y z U V +
      W^2*coefficient4 h t x y z U V) := by
  simp [perm4, Matrix.of_apply, blockA, blockB, extension, coefficient2, coefficient3, coefficient4]
  linear_combination (((-2) * (U ^ 2)) + ((-2) * (V ^ 2)) + (W * (((-4) * U * x) + ((-4) * V * x) + (4 * x * (U ^ 2)) + (4 * x * (V ^ 2)) + ((-4) * U * x * (V ^ 2)) + ((-4) * V * x * (U ^ 2)) + ((-4) * h * y * (V ^ 2)) + ((-2) * h * t * (V ^ 2)) + (2 * h * t * (U ^ 2)) + (4 * h * y * (U ^ 2)) + ((-4) * U * h * y * (V ^ 2)) + ((-4) * U * h * z * (V ^ 2)) + ((-4) * V * h * z * (U ^ 2)) + (2 * U * x * (V ^ 2) * (h ^ 2)) + (2 * V * x * (U ^ 2) * (h ^ 2)) + (4 * V * h * y * (U ^ 2)))) + ((W ^ 2) * (((-16) * (y ^ 2)) + ((-4) * (t ^ 2)) + ((-4) * (x ^ 2)) + ((U ^ 2) * (t ^ 2)) + ((V ^ 2) * (t ^ 2)) + ((-16) * t * y) + ((-8) * U * (y ^ 2)) + ((-8) * V * (y ^ 2)) + ((-4) * (U ^ 2) * (x ^ 2)) + ((-4) * (V ^ 2) * (x ^ 2)) + (4 * (U ^ 2) * (z ^ 2)) + (4 * (V ^ 2) * (z ^ 2)) + (8 * U * (x ^ 2)) + (8 * V * (x ^ 2)) + (16 * (U ^ 2) * (y ^ 2)) + (16 * (V ^ 2) * (y ^ 2)) + ((U ^ 2) * (h ^ 2) * (x ^ 2)) + ((V ^ 2) * (h ^ 2) * (x ^ 2)) + ((-1) * (U ^ 2) * (h ^ 2) * (t ^ 2)) + ((-1) * (V ^ 2) * (h ^ 2) * (t ^ 2)) + ((-18) * U * V * (y ^ 2)) + ((-16) * y * z * (U ^ 2)) + ((-8) * U * V * (x ^ 2)) + ((-8) * U * y * z) + ((-4) * U * t * y) + ((-4) * U * t * z) + ((-4) * V * t * y) + ((-4) * t * z * (U ^ 2)) + ((-4) * (U ^ 2) * (h ^ 2) * (y ^ 2)) + ((-4) * (V ^ 2) * (h ^ 2) * (y ^ 2)) + (4 * V * t * z) + (4 * t * z * (V ^ 2)) + (8 * V * y * z) + (8 * t * y * (U ^ 2)) + (8 * t * y * (V ^ 2)) + (16 * y * z * (V ^ 2)) + (18 * U * V * (z ^ 2)) + ((-8) * V * h * x * y) + ((-4) * V * h * t * x) + ((-4) * h * x * z * (U ^ 2)) + ((-4) * h * x * z * (V ^ 2)) + ((-4) * t * y * (U ^ 2) * (h ^ 2)) + ((-4) * t * y * (V ^ 2) * (h ^ 2)) + ((-2) * h * t * x * (U ^ 2)) + (2 * h * t * x * (V ^ 2)) + (4 * U * V * (h ^ 2) * (x ^ 2)) + (4 * U * h * t * x) + (8 * U * h * x * y) + ((-16) * U * V * h * x * z))) + ((W ^ 3) * ((8 * (x ^ 3)) + ((-48) * x * (y ^ 2)) + ((-8) * U * (x ^ 3)) + ((-8) * V * (x ^ 3)) + ((-8) * x * (t ^ 2)) + ((-40) * t * x * y) + ((-16) * V * h * (y ^ 3)) + (2 * U * x * (t ^ 2)) + (2 * U * (h ^ 2) * (x ^ 3)) + (2 * V * x * (t ^ 2)) + (2 * V * (h ^ 2) * (x ^ 3)) + (16 * U * h * (y ^ 3)) + (26 * U * x * (z ^ 2)) + (26 * V * x * (z ^ 2)) + (38 * U * x * (y ^ 2)) + (38 * V * x * (y ^ 2)) + ((-16) * V * h * t * (y ^ 2)) + ((-12) * U * h * z * (x ^ 2)) + ((-12) * V * h * z * (x ^ 2)) + ((-8) * U * x * y * z) + ((-8) * U * x * (h ^ 2) * (y ^ 2)) + ((-8) * V * x * (h ^ 2) * (y ^ 2)) + ((-4) * U * h * t * (x ^ 2)) + ((-4) * U * h * y * (x ^ 2)) + ((-4) * V * h * y * (t ^ 2)) + ((-4) * V * t * x * z) + ((-2) * U * x * (h ^ 2) * (t ^ 2)) + ((-2) * V * x * (h ^ 2) * (t ^ 2)) + (4 * U * h * y * (t ^ 2)) + (4 * U * h * z * (t ^ 2)) + (4 * U * t * x * z) + (4 * V * h * t * (x ^ 2)) + (4 * V * h * y * (x ^ 2)) + (4 * V * h * z * (t ^ 2)) + (8 * V * x * y * z) + (16 * U * h * t * (y ^ 2)) + (16 * U * h * z * (y ^ 2)) + (16 * V * h * z * (y ^ 2)) + (28 * U * t * x * y) + (28 * V * t * x * y) + ((-8) * U * t * x * y * (h ^ 2)) + ((-8) * V * t * x * y * (h ^ 2)) + (16 * U * h * t * y * z) + (16 * V * h * t * y * z))) + ((W ^ 4) * (((-104) * (y ^ 4)) + ((-6) * (x ^ 4)) + ((h ^ 2) * (t ^ 4)) + ((h ^ 2) * (x ^ 4)) + ((-136) * t * (y ^ 3)) + ((-58) * (t ^ 2) * (y ^ 2)) + ((-40) * (y ^ 2) * (z ^ 2)) + ((-10) * (t ^ 2) * (z ^ 2)) + ((-8) * y * (t ^ 3)) + ((-2) * (t ^ 2) * (x ^ 2)) + (16 * (h ^ 2) * (y ^ 4)) + (26 * (x ^ 2) * (z ^ 2)) + (46 * (x ^ 2) * (y ^ 2)) + ((-40) * t * y * (z ^ 2)) + ((-8) * h * z * (x ^ 3)) + ((-8) * (h ^ 2) * (x ^ 2) * (y ^ 2)) + ((-2) * (h ^ 2) * (t ^ 2) * (x ^ 2)) + (8 * y * (h ^ 2) * (t ^ 3)) + (24 * t * y * (x ^ 2)) + (24 * (h ^ 2) * (t ^ 2) * (y ^ 2)) + (32 * t * (h ^ 2) * (y ^ 3)) + ((-8) * t * y * (h ^ 2) * (x ^ 2)) + (8 * h * x * z * (t ^ 2)) + (32 * h * x * z * (y ^ 2)) + (32 * h * t * x * y * z))) + ((-2) * (U ^ 2) * (V ^ 2)) + ((U ^ 2) * (V ^ 2) * (h ^ 2)))*hh

lemma factor_coefficients (a b c : ℂ)
    (hp : ∀ W : ℂ, W^2*(a+W*b+W^2*c)=0) : a=0 ∧ b=0 := by
  have h1 := hp 1
  have hm := hp (-1)
  have h2 := hp 2
  constructor
  · linear_combination h1+(1/3:ℂ)*hm-(1/12:ℂ)*h2
  · linear_combination (1/2:ℂ)*h1-(1/2:ℂ)*hm

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma normalized_extension_zero (h t x y z : ℂ) (hh : h^2 = 2)
    (hp : ∀ U V W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + U*blockA h r s + V*blockB h r s + W*extension h t x y z r s) = 24) :
    t = 0 ∧ x = 0 ∧ y = 0 ∧ z = 0 := by
  have he (U V : ℂ) : coefficient2 h t x y z U V=0 ∧ coefficient3 h t x y z U V=0 := by
    apply factor_coefficients
    intro W
    rw [← permanent_expansion h t x y z U V W hh, hp U V W]
    ring
  have h00 := (he 0 0).1
  have h10 := (he 1 0).1
  have h01 := (he 0 1).1
  have h11 := (he 1 1).1
  have hccc := (he 0 0).2
  simp only [coefficient2, coefficient3] at h00 h10 h01 h11 hccc
  apply quadrics_and_cubic_zero h t x y z hh
  · linear_combination (-1/36:ℂ)*(h11-h10-h01+h00)
  · linear_combination (-1/4:ℂ)*(h10-h00)
  · linear_combination (1/4:ℂ)*(h01-h00)
  · linear_combination (1/4:ℂ)*h00
  · linear_combination (-1/8:ℂ)*hccc

def gauged (a b c d u v w k : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![a, 0, u, v], ![0, b, w, k], ![u, w, c, 0], ![v, k, 0, d]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma gauged_first_order (h a b c d u v w k U V : ℂ) (hh : h^2=2)
    (hp : ∀ W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*blockA h r s+V*blockB h r s+W*gauged a b c d u v w k r s)=24) :
    ((6 * a) + (6 * b) + (6 * c) + (6 * d) + (12 * k) + (12 * u) + (12 * v) + (12 * w) + (h * (((-4) * U * u) + ((-4) * U * v) + ((-4) * V * u) + ((-4) * V * w) + ((-2) * U * a) + ((-2) * V * c) + (2 * U * b) + (2 * V * d) + (4 * U * k) + (4 * U * w) + (4 * V * k) + (4 * V * v))) + ((-2) * U * a) + ((-2) * U * b) + ((-2) * V * c) + ((-2) * V * d) + ((-4) * U * V * v) + ((-4) * U * V * w) + (4 * U * V * k) + (4 * U * V * u)) = 0 := by
  have h1 := hp 1
  have hm1 := hp (-1)
  have h2 := hp 2
  have hm2 := hp (-2)
  simp [perm4, Matrix.of_apply, blockA, blockB, gauged] at h1 hm1 h2 hm2
  linear_combination (2/3:ℂ)*h1-(2/3:ℂ)*hm1-(1/12:ℂ)*h2+(1/12:ℂ)*hm2+(((a * (V ^ 2)) + (b * (V ^ 2)) + (c * (U ^ 2)) + (d * (U ^ 2)) + ((-1) * U * a * (V ^ 2)) + ((-1) * U * b * (V ^ 2)) + ((-1) * V * c * (U ^ 2)) + ((-1) * V * d * (U ^ 2)) + ((-2) * U * V * k) + ((-2) * U * V * u) + (2 * U * V * v) + (2 * U * V * w) + (U * b * h * (V ^ 2)) + (V * d * h * (U ^ 2)) + ((-1) * U * a * h * (V ^ 2)) + ((-1) * V * c * h * (U ^ 2))))*hh

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma gauged_zero (h a b c d u v w k : ℂ) (hh : h^2=2)
    (hp : ∀ U V W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*blockA h r s+V*blockB h r s+W*gauged a b c d u v w k r s)=24) :
    gauged a b c d u v w k = 0 := by
  have h00 := gauged_first_order h a b c d u v w k 0 0 hh (hp 0 0)
  have h10 := gauged_first_order h a b c d u v w k 1 0 hh (hp 1 0)
  have h01 := gauged_first_order h a b c d u v w k 0 1 hh (hp 0 1)
  have h11 := gauged_first_order h a b c d u v w k 1 1 hh (hp 1 1)
  have l0 : (k + u + ((-1) * v) + ((-1) * w))=0 := by linear_combination (1/4:ℂ)*(h11-h10-h01+h00)
  have l1 : (a + b + c + d + (4 * v) + (4 * w))=0 := by linear_combination (1/6:ℂ)*h00-2*l0
  have l2 : ((a * ((-1) + ((-1) * h))) + (b * ((-1) + h)) + ((-4) * h * (u + ((-1) * w))))=0 := by linear_combination (1/2:ℂ)*(h10-h00)-2*h*l0
  have l3 : ((c * ((-1) + ((-1) * h))) + (d * ((-1) + h)) + ((-4) * h * (u + ((-1) * v))))=0 := by linear_combination (1/2:ℂ)*(h01-h00)-2*h*l0
  have heq : gauged a b c d u v w k = extension h (((a * (1 + h)) + (u * (2 + (2 * h))) + ((-1) * (2 + h) * (((1 / 2 : ℂ) * v) + ((1 / 2 : ℂ) * w))) + (2 * h * (((1 / 2 : ℂ) * v) + ((-1 / 2 : ℂ) * w))))) ((((1 / 2 : ℂ) * v) + ((1 / 2 : ℂ) * w))) ((((1 / 2 : ℂ) * v) + ((-1 / 2 : ℂ) * w))) ((u + ((-1 / 2 : ℂ) * v) + ((-1 / 2 : ℂ) * w))) := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [gauged, extension] <;> try ring
    · linear_combination ((-1 / 2 : ℂ) * (v + ((-3) * w) + (2 * a) + (4 * u)))*hh
    · linear_combination (1 + h)*l2 + ((1 / 2 : ℂ) * (((-1) * v) + ((-5) * w) + ((-2) * b) + (4 * u)))*hh
    · linear_combination 1*l0
    · linear_combination ((1 / 2 : ℂ) + ((-1 / 4 : ℂ) * h))*l1 + ((-1 / 4 : ℂ) * h)*l2 + ((-1 / 4 : ℂ) * h)*l3 + ((1 / 4 : ℂ) * (b + d + ((-1) * c) + ((-2) * w) + (3 * a) + (6 * v)))*hh
    · linear_combination 1*l0
    · linear_combination ((1 / 2 : ℂ) + ((1 / 4 : ℂ) * h))*l1 + ((-1) + ((-3 / 4 : ℂ) * h))*l2 + ((1 / 4 : ℂ) * h)*l3 + ((-1 / 4 : ℂ) * (d + ((-1) * a) + ((-1) * c) + ((-6) * w) + ((-3) * b) + (2 * v)))*hh
  have hpE : ∀ U V W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
    (1 : ℂ)+U*blockA h r s+V*blockB h r s+W*extension h (((a * (1 + h)) + (u * (2 + (2 * h))) + ((-1) * (2 + h) * (((1 / 2 : ℂ) * v) + ((1 / 2 : ℂ) * w))) + (2 * h * (((1 / 2 : ℂ) * v) + ((-1 / 2 : ℂ) * w))))) ((((1 / 2 : ℂ) * v) + ((1 / 2 : ℂ) * w))) ((((1 / 2 : ℂ) * v) + ((-1 / 2 : ℂ) * w))) ((u + ((-1 / 2 : ℂ) * v) + ((-1 / 2 : ℂ) * w))) r s)=24 := by
    intro U V W
    rw [← heq]
    exact hp U V W
  obtain ⟨ht,hx,hy,hz⟩ := normalized_extension_zero h (((a * (1 + h)) + (u * (2 + (2 * h))) + ((-1) * (2 + h) * (((1 / 2 : ℂ) * v) + ((1 / 2 : ℂ) * w))) + (2 * h * (((1 / 2 : ℂ) * v) + ((-1 / 2 : ℂ) * w))))) ((((1 / 2 : ℂ) * v) + ((1 / 2 : ℂ) * w))) ((((1 / 2 : ℂ) * v) + ((-1 / 2 : ℂ) * w))) ((u + ((-1 / 2 : ℂ) * v) + ((-1 / 2 : ℂ) * w))) hh hpE
  rw [heq, ht, hx, hy, hz]
  ext r s
  fin_cases r <;> fin_cases s <;> simp [extension]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma two_blocks_maximal (h : ℂ) (hh : h^2=2)
    (C : Matrix (Fin 4) (Fin 4) ℂ)
    (hs : ∀ r s : Fin 4, C r s=C s r)
    (hp : ∀ U V W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*blockA h r s+V*blockB h r s+W*C r s)=24) :
    ∃ p q : ℂ, C=Matrix.of fun (r s : Fin 4) => p*blockA h r s+q*blockB h r s := by
  let G := gauged (C 0 0-(h-1)*C 0 1) (C 1 1-(-h-1)*C 0 1)
    (C 2 2-(h-1)*C 2 3) (C 3 3-(-h-1)*C 2 3) (C 0 2) (C 0 3) (C 1 2) (C 1 3)
  have h10 := hs 1 0
  have h20 := hs 2 0
  have h30 := hs 3 0
  have h21 := hs 2 1
  have h31 := hs 3 1
  have h32 := hs 3 2
  have heq : C=Matrix.of fun (r s : Fin 4) =>
      C 0 1*blockA h r s+C 2 3*blockB h r s+G r s := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [G, gauged, blockA, blockB, Matrix.of_apply, h10, h20, h30, h21, h31, h32] <;> ring
  have hG : G=0 := by
    apply gauged_zero h _ _ _ _ _ _ _ _ hh
    intro U V W
    have he := hp (U-W*C 0 1) (V-W*C 2 3) W
    convert he using 1
    congr 1
    ext r s
    have hr := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M r s) heq
    simp only [Matrix.of_apply] at hr ⊢
    change (1 : ℂ)+U*blockA h r s+V*blockB h r s+W*G r s = _
    linear_combination (-W)*hr
  refine ⟨C 0 1,C 2 3,heq.trans ?_⟩
  ext r s
  simp only [Matrix.of_apply, hG, Matrix.zero_apply, add_zero]

lemma block_root (a b c : ℂ) (hS : a+c+2*b=0) (hQ : a*c+b^2=0)
    (hne : a≠0 ∨ b≠0 ∨ c≠0) :
    b≠0 ∧ ∃ h : ℂ, h^2=2 ∧ a=b*(h-1) ∧ c=b*(-h-1) := by
  have hb : b≠0 := by
    intro hb
    have ha2 : a^2=0 := by linear_combination a*hS-hQ+(b-2*a)*hb
    have ha := eq_zero_of_pow_eq_zero ha2
    have hc : c=0 := by linear_combination hS-ha-2*hb
    exact hne.elim (fun hn => hn ha) (fun hn => hn.elim (fun hn => hn hb) (fun hn => hn hc))
  have hmul : (a/b)*b=a := div_mul_cancel₀ a hb
  have haq : a^2+2*a*b-b^2=0 := by linear_combination a*hS-hQ
  refine ⟨hb,a/b+1,?_,?_,?_⟩
  · apply mul_right_cancel₀ (pow_ne_zero 2 hb)
    linear_combination (a/b*b+a+2*b)*hmul+haq
  · linear_combination -hmul
  · linear_combination hS+hmul

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma two_roots_maximal (h k : ℂ) (hh : h^2=2) (hk : k^2=2)
    (C : Matrix (Fin 4) (Fin 4) ℂ)
    (hs : ∀ r s : Fin 4, C r s=C s r)
    (hp : ∀ U V W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*blockA h r s+V*blockB k r s+W*C r s)=24) :
    ∃ p q : ℂ, C=Matrix.of fun (r s : Fin 4) => p*blockA h r s+q*blockB k r s := by
  by_cases hkh : k=h
  · subst k
    exact two_blocks_maximal h hh C hs hp
  have hprod : (k-h)*(k+h)=0 := by linear_combination hk-hh
  have hsum : k+h=0 := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hkh)
  have hkh : k= -h := by linear_combination hsum
  subst k
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 2 3
  let C' : Matrix (Fin 4) (Fin 4) ℂ := C.submatrix σ σ
  have hs' (r s : Fin 4) : C' r s=C' s r := hs _ _
  have hp' (U V W : ℂ) : Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*blockA h r s+V*blockB h r s+W*C' r s)=24 := by
    let M : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun r s =>
      (1 : ℂ)+U*blockA h r s+V*blockB (-h) r s+W*C r s
    have heq : M.submatrix σ σ=Matrix.of (fun (r s : Fin 4) =>
        (1 : ℂ)+U*blockA h r s+V*blockB h r s+W*C' r s) := by
      ext r s
      fin_cases r <;> fin_cases s <;>
        simp [M,C',σ,Matrix.submatrix_apply,Matrix.of_apply,blockA,blockB,Equiv.swap_apply_def] <;> ring
    have hinv : Matrix.permanent (M.submatrix σ σ)=Matrix.permanent M := by
      change Matrix.permanent ((M.submatrix σ id).submatrix id σ)=Matrix.permanent M
      rw [Matrix.permanent_permute_rows,Matrix.permanent_permute_cols]
    rw [← heq]
    exact hinv.trans (hp U V W)
  obtain ⟨p,q,hC⟩ := two_blocks_maximal h hh C' hs' hp'
  refine ⟨p,q,?_⟩
  have heq := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M.submatrix σ σ) hC
  have hCinv : C'.submatrix σ σ=C := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [C',σ,Matrix.submatrix_apply,Equiv.swap_apply_def]
  rw [hCinv] at heq
  apply heq.trans
  ext r s
  change p*blockA h (σ r) (σ s)+q*blockB h (σ r) (σ s)=_
  fin_cases r <;> fin_cases s <;> simp [σ,blockA,blockB,Equiv.swap_apply_def] <;> ring

def topBlock (a b c : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![a,b,0,0],![b,c,0,0],![0,0,0,0],![0,0,0,0]]

def bottomBlock (a b c : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0,0,0,0],![0,0,0,0],![0,0,a,b],![0,0,b,c]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma disjoint_blocks_maximal (a b c d e f : ℂ)
    (hA : a≠0 ∨ b≠0 ∨ c≠0) (hB : d≠0 ∨ e≠0 ∨ f≠0)
    (C : Matrix (Fin 4) (Fin 4) ℂ)
    (hs : ∀ r s : Fin 4, C r s=C s r)
    (hp : ∀ U V W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*topBlock a b c r s+V*bottomBlock d e f r s+W*C r s)=24) :
    ∃ p q : ℂ, C=Matrix.of fun (r s : Fin 4) => p*topBlock a b c r s+q*bottomBlock d e f r s := by
  have hA1 := hp 1 0 0
  have hAm := hp (-1) 0 0
  have hB1 := hp 0 1 0
  have hBm := hp 0 (-1) 0
  simp [perm4,Matrix.of_apply,topBlock,bottomBlock] at hA1 hAm hB1 hBm
  have hAS : a+c+2*b=0 := by linear_combination (1/12:ℂ)*(hA1-hAm)
  have hAQ : a*c+b^2=0 := by linear_combination (1/4:ℂ)*(hA1+hAm)
  have hBS : d+f+2*e=0 := by linear_combination (1/12:ℂ)*(hB1-hBm)
  have hBQ : d*f+e^2=0 := by linear_combination (1/4:ℂ)*(hB1+hBm)
  obtain ⟨hb,h,hh,ha,hc⟩ := block_root a b c hAS hAQ hA
  obtain ⟨he,k,hk,hd,hf⟩ := block_root d e f hBS hBQ hB
  have heqA : topBlock a b c=Matrix.of (fun (r s : Fin 4) => b*blockA h r s) := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [topBlock,blockA,ha,hc] <;> ring_nf <;> simp
  have heqB : bottomBlock d e f=Matrix.of (fun (r s : Fin 4) => e*blockB k r s) := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [bottomBlock,blockB,hd,hf] <;> ring_nf <;> simp
  have hp' (U V W : ℂ) : Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*blockA h r s+V*blockB k r s+W*C r s)=24 := by
    have hp0 := hp (U/b) (V/e) W
    rw [heqA,heqB] at hp0
    simpa only [Matrix.of_apply,← mul_assoc,div_mul_cancel₀ U hb,div_mul_cancel₀ V he] using hp0
  obtain ⟨p,q,hC⟩ := two_roots_maximal h k hh hk C hs hp'
  refine ⟨p/b,q/e,hC.trans ?_⟩
  ext r s
  rw [heqA,heqB]
  simp only [Matrix.of_apply,← mul_assoc,div_mul_cancel₀ p hb,div_mul_cancel₀ q he]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma two_double_kernel_rows_maximal (A B C : Matrix (Fin 4) (Fin 4) ℂ)
    (hsA : ∀ r s : Fin 4, A r s=A s r)
    (hsB : ∀ r s : Fin 4, B r s=B s r)
    (hsC : ∀ r s : Fin 4, C r s=C s r)
    (hA2 : ∀ j : Fin 4, A 2 j=0) (hA3 : ∀ j : Fin 4, A 3 j=0)
    (hB0 : ∀ j : Fin 4, B 0 j=0) (hB1 : ∀ j : Fin 4, B 1 j=0)
    (hA : A≠0) (hB : B≠0)
    (hp : ∀ U V W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*A r s+V*B r s+W*C r s)=24) :
    ∃ p q : ℂ, C=Matrix.of fun (r s : Fin 4) => p*A r s+q*B r s := by
  have heqA : A=topBlock (A 0 0) (A 0 1) (A 1 1) := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [topBlock,hA2,hA3,hsA 0 2,hsA 0 3,hsA 1 2,hsA 1 3,hsA 1 0]
  have heqB : B=bottomBlock (B 2 2) (B 2 3) (B 3 3) := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [bottomBlock,hB0,hB1,hsB 2 0,hsB 3 0,hsB 2 1,hsB 3 1,hsB 3 2]
  have hAne : A 0 0≠0 ∨ A 0 1≠0 ∨ A 1 1≠0 := by
    by_contra hn
    have ha : A 0 0=0 := Classical.not_not.mp (fun h => hn (Or.inl h))
    have hb : A 0 1=0 := Classical.not_not.mp (fun h => hn (Or.inr (Or.inl h)))
    have hc : A 1 1=0 := Classical.not_not.mp (fun h => hn (Or.inr (Or.inr h)))
    apply hA
    apply heqA.trans
    ext r s
    fin_cases r <;> fin_cases s <;> simp [topBlock,ha,hb,hc]
  have hBne : B 2 2≠0 ∨ B 2 3≠0 ∨ B 3 3≠0 := by
    by_contra hn
    have ha : B 2 2=0 := Classical.not_not.mp (fun h => hn (Or.inl h))
    have hb : B 2 3=0 := Classical.not_not.mp (fun h => hn (Or.inr (Or.inl h)))
    have hc : B 3 3=0 := Classical.not_not.mp (fun h => hn (Or.inr (Or.inr h)))
    apply hB
    apply heqB.trans
    ext r s
    fin_cases r <;> fin_cases s <;> simp [bottomBlock,ha,hb,hc]
  have hp' (U V W : ℂ) : Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*topBlock (A 0 0) (A 0 1) (A 1 1) r s+
      V*bottomBlock (B 2 2) (B 2 3) (B 3 3) r s+W*C r s)=24 := by
    have hc := hp U V W
    rw [heqA,heqB] at hc
    exact hc
  obtain ⟨p,q,hC⟩ := disjoint_blocks_maximal (A 0 0) (A 0 1) (A 1 1)
    (B 2 2) (B 2 3) (B 3 3) hAne hBne C hsC hp'
  refine ⟨p,q,hC.trans ?_⟩
  rw [← heqA,← heqB]

end MatrixBridge

end PEqualNP.Outside.L_gct_231.TwoBlock


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

namespace PEqualNP.Outside.L_gct_231.GlobalCover

open RowKernel Cover

def permMatrix (σ : Equiv.Perm (Fin 4)) (T : Ambient) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun r s => T (σ r,σ s)

lemma permMatrix_ne_zero (σ : Equiv.Perm (Fin 4)) (T : Ambient) (hT : T≠0) :
    permMatrix σ T≠0 := by
  intro hz
  apply hT
  funext p
  rcases p with ⟨r,s⟩
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M (σ.symm r) (σ.symm s)) hz
  simpa only [permMatrix,Matrix.of_apply,Equiv.apply_symm_apply,Matrix.zero_apply,Pi.zero_apply] using he

lemma permMatrix_symmetric (L : Submodule ℂ Ambient) (hL : Level L)
    (σ : Equiv.Perm (Fin 4)) (T : Ambient) (hT : T∈L) :
    ∀ r s : Fin 4, permMatrix σ T r s=permMatrix σ T s r := by
  intro r s
  exact hL.1 T hT (σ r) (σ s)

lemma level_three_reindex (L : Submodule ℂ Ambient) (hL : Level L)
    (σ : Equiv.Perm (Fin 4)) (A B C : Ambient) (hA : A∈L) (hB : B∈L) (hC : C∈L) :
    ∀ U V W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1:ℂ)+U*permMatrix σ A r s+V*permMatrix σ B r s+W*permMatrix σ C r s)=24 := by
  intro U V W
  let T : Ambient := U • A+V • B+W • C
  have hT : T∈L := L.add_mem (L.add_mem (L.smul_mem U hA) (L.smul_mem V hB)) (L.smul_mem W hC)
  let M : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun r s => (1:ℂ)+T (r,s)
  have hinv : Matrix.permanent (M.submatrix σ σ)=Matrix.permanent M := by
    change Matrix.permanent ((M.submatrix σ id).submatrix id σ)=Matrix.permanent M
    rw [Matrix.permanent_permute_rows,Matrix.permanent_permute_cols]
  have hp := hinv.trans (hL.2 T hT)
  have heq : M.submatrix σ σ=Matrix.of (fun (r s : Fin 4) =>
      (1:ℂ)+U*permMatrix σ A r s+V*permMatrix σ B r s+W*permMatrix σ C r s) := by
    ext r s
    simp [M,T,permMatrix,Matrix.submatrix_apply,Matrix.of_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_assoc]
  rw [←heq]
  exact hp

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma double_collision_impossible (L : Submodule ℂ Ambient)
    (h3 : Module.finrank ℂ L=3) (hL : Level L)
    (A : Fin 4 → Ambient) (hA : Directions L A) (σ : Equiv.Perm (Fin 4))
    (h01 : directionLine (A (σ 0))=directionLine (A (σ 1)))
    (h23 : directionLine (A (σ 2))=directionLine (A (σ 3))) : False := by
  have hr1 := row_zero_of_same_line _ _ (σ 1) h01 (hA (σ 1)).2.2
  have hr3 := row_zero_of_same_line _ _ (σ 3) h23 (hA (σ 3)).2.2
  have hspan (T : Ambient) (hT : T∈L) :
      ∃ p q : ℂ, T=p • A (σ 2)+q • A (σ 0) := by
    obtain ⟨p,q,heq⟩ := TwoBlock.MatrixBridge.two_double_kernel_rows_maximal
      (permMatrix σ (A (σ 2))) (permMatrix σ (A (σ 0))) (permMatrix σ T)
      (permMatrix_symmetric L hL σ _ (hA (σ 2)).1)
      (permMatrix_symmetric L hL σ _ (hA (σ 0)).1)
      (permMatrix_symmetric L hL σ T hT)
      (fun j => (hA (σ 2)).2.2 (σ j)) (fun j => hr3 (σ j))
      (fun j => (hA (σ 0)).2.2 (σ j)) (fun j => hr1 (σ j))
      (permMatrix_ne_zero σ _ (hA (σ 2)).2.1) (permMatrix_ne_zero σ _ (hA (σ 0)).2.1)
      (level_three_reindex L hL σ _ _ T (hA (σ 2)).1 (hA (σ 0)).1 hT)
    refine ⟨p,q,?_⟩
    funext x
    rcases x with ⟨r,s⟩
    have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M (σ.symm r) (σ.symm s)) heq
    simpa only [permMatrix,Matrix.of_apply,Equiv.apply_symm_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using he
  exact Projective.no_three_dimensional_pair_span L h3 (A (σ 2)) (A (σ 0)) hspan

end PEqualNP.Outside.L_gct_231.GlobalCover



namespace PEqualNP.Outside.L_gct_231

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in

lemma collinearArrowhead_mid_annihilated (g i k d e f : ℂ)
    (hq0 : ((e ^ 2) + (f ^ 2) + ((-1) * (i ^ 2)) + ((-1) * (k ^ 2)) + ((-1) * i * k) + ((-2) * e * i) + ((-2) * f * k) + (2 * e * f)) = 0)
    (hq1 : (((-2) * (f ^ 2)) + (2 * (k ^ 2)) + (i * k) + ((-1) * g * i) + ((-1) * g * k) + ((-2) * e * f) + (2 * d * e) + (2 * d * f) + (4 * f * k)) = 0)
    (hq2 : ((d ^ 2) + (f ^ 2) + ((-1) * (g ^ 2)) + ((-1) * (k ^ 2)) + (g * k) + ((-2) * d * f) + ((-2) * d * g) + ((-2) * f * k)) = 0)
    (hc0 : ((i * (f ^ 2)) + (k * (e ^ 2)) + ((-1) * i * (k ^ 2)) + ((-1) * k * (i ^ 2)) + ((-2) * e * i * k) + ((-2) * f * i * k)) = 0)
    (hc1 : ((g * (e ^ 2)) + (g * (f ^ 2)) + (k * (i ^ 2)) + ((-1) * g * (i ^ 2)) + ((-1) * g * (k ^ 2)) + ((-1) * k * (e ^ 2)) + ((-2) * i * (f ^ 2)) + (2 * i * (k ^ 2)) + ((-2) * e * g * i) + ((-2) * f * g * k) + ((-2) * g * i * k) + (2 * d * e * k) + (2 * d * f * i) + (2 * e * f * g) + (2 * e * i * k) + (4 * f * i * k)) = 0)
    (hc2 : ((i * (d ^ 2)) + (i * (f ^ 2)) + (k * (d ^ 2)) + ((-1) * i * (g ^ 2)) + ((-1) * i * (k ^ 2)) + ((-1) * k * (g ^ 2)) + ((-2) * g * (f ^ 2)) + (2 * g * (k ^ 2)) + ((-2) * d * e * k) + ((-2) * d * f * i) + ((-2) * d * g * i) + ((-2) * d * g * k) + ((-2) * e * f * g) + ((-2) * f * i * k) + (2 * g * i * k) + (4 * f * g * k)) = 0)
    (hc3 : ((g * (f ^ 2)) + (k * (g ^ 2)) + ((-1) * g * (k ^ 2)) + ((-1) * k * (d ^ 2)) + ((-2) * f * g * k) + (2 * d * g * k)) = 0)
    : e ^ 2 * f ^ 3 * i = 0 := by
  linear_combination
    ((-1 / 123480 : ℂ) * (((-8079) * (f ^ 4)) + ((-142929) * (d ^ 2) * (f ^ 2)) + ((-42948) * i * (f ^ 3)) + ((-42176) * i * (d ^ 3)) + ((-42176) * k * (d ^ 3)) + ((-31342) * d * (e ^ 3)) + ((-31221) * (e ^ 2) * (f ^ 2)) + ((-22706) * e * (f ^ 3)) + ((-13166) * (f ^ 2) * (i ^ 2)) + ((-10270) * g * (i ^ 3)) + ((-2840) * e * (k ^ 3)) + ((-769) * (e ^ 2) * (k ^ 2)) + ((-96) * g * (f ^ 3)) + (1448 * i * (k ^ 3)) + (2342 * d * (f ^ 3)) + (4013 * (e ^ 2) * (g ^ 2)) + (4472 * f * (k ^ 3)) + (7374 * (d ^ 2) * (i ^ 2)) + (7983 * (f ^ 2) * (g ^ 2)) + (10270 * k * (i ^ 3)) + (11686 * k * (f ^ 3)) + (14614 * (i ^ 2) * (k ^ 2)) + (17023 * (f ^ 2) * (k ^ 2)) + (31342 * f * (e ^ 3)) + (42176 * d * (k ^ 3)) + (42889 * (d ^ 2) * (e ^ 2)) + (148666 * e * (d ^ 3)) + (148666 * f * (d ^ 3)) + (168704 * (d ^ 2) * (k ^ 2)) + ((-113172) * e * i * (f ^ 2)) + ((-93808) * d * i * (f ^ 2)) + ((-93672) * e * f * (d ^ 2)) + ((-78704) * f * i * (e ^ 2)) + ((-59304) * d * g * (i ^ 2)) + ((-42176) * d * g * (k ^ 2)) + ((-39352) * e * g * (i ^ 2)) + ((-37436) * d * k * (f ^ 2)) + ((-35462) * f * k * (e ^ 2)) + ((-32288) * d * e * (f ^ 2)) + ((-24208) * f * g * (i ^ 2)) + ((-20540) * e * f * (i ^ 2)) + ((-20038) * d * e * (g ^ 2)) + ((-20038) * d * f * (g ^ 2)) + ((-15671) * i * k * (e ^ 2)) + ((-11906) * d * g * (f ^ 2)) + ((-11718) * g * k * (i ^ 2)) + ((-11668) * d * f * (e ^ 2)) + ((-4424) * f * g * (k ^ 2)) + ((-2488) * g * k * (e ^ 2)) + ((-1780) * e * g * (k ^ 2)) + ((-1448) * g * i * (k ^ 2)) + ((-96) * f * i * (g ^ 2)) + ((-48) * f * k * (g ^ 2)) + (96 * g * k * (f ^ 2)) + (1272 * e * g * (f ^ 2)) + (4620 * e * i * (g ^ 2)) + (4620 * e * k * (g ^ 2)) + (5372 * e * f * (g ^ 2)) + (5792 * d * f * (i ^ 2)) + (7220 * e * f * (k ^ 2)) + (9335 * g * i * (f ^ 2)) + (9674 * d * g * (e ^ 2)) + (11240 * e * k * (d ^ 2)) + (15671 * g * i * (e ^ 2)) + (15856 * e * k * (f ^ 2)) + (20038 * g * i * (d ^ 2)) + (20038 * g * k * (d ^ 2)) + (20540 * d * e * (i ^ 2)) + (37740 * e * i * (k ^ 2)) + (39352 * e * k * (i ^ 2)) + (44276 * e * g * (d ^ 2)) + (44276 * f * g * (d ^ 2)) + (44556 * d * k * (i ^ 2)) + (45796 * f * i * (k ^ 2)) + (50292 * d * k * (e ^ 2)) + (50540 * f * k * (i ^ 2)) + (57200 * f * g * (e ^ 2)) + (78704 * d * i * (e ^ 2)) + (82202 * d * f * (k ^ 2)) + (92431 * i * k * (f ^ 2)) + (97230 * d * e * (k ^ 2)) + (103060 * e * i * (d ^ 2)) + (111764 * i * k * (d ^ 2)) + (128908 * d * i * (k ^ 2)) + (178932 * f * i * (d ^ 2)) + (417192 * f * k * (d ^ 2)) + ((-143656) * d * g * i * k) + ((-92932) * d * e * g * k) + ((-65954) * d * e * g * i) + ((-58914) * d * f * g * i) + ((-34036) * e * f * g * k) + ((-26108) * f * g * i * k) + ((-16504) * d * e * f * g) + ((-10236) * e * g * i * k) + ((-4524) * d * f * g * k) + (9972 * e * f * g * i) + (10112 * d * e * f * i) + (58606 * d * e * i * k) + (98992 * e * f * i * k) + (145108 * d * e * f * k) + (247234 * d * f * i * k))) * hq0 +
    ((1 / 123480 : ℂ) * (((-15671) * (e ^ 4)) + ((-10270) * (i ^ 4)) + ((-84352) * (d ^ 2) * (i ^ 2)) + ((-84352) * (d ^ 2) * (k ^ 2)) + ((-59892) * e * (i ^ 3)) + ((-52763) * (e ^ 2) * (i ^ 2)) + ((-44556) * d * (i ^ 3)) + ((-24208) * f * (i ^ 3)) + ((-23936) * k * (e ^ 3)) + ((-18568) * g * (e ^ 3)) + ((-11718) * k * (i ^ 3)) + ((-10573) * (f ^ 2) * (i ^ 2)) + ((-2674) * f * (e ^ 3)) + ((-1448) * (i ^ 2) * (k ^ 2)) + (4013 * (e ^ 2) * (g ^ 2)) + (4520 * g * (f ^ 3)) + (4520 * i * (f ^ 3)) + (5680 * (e ^ 2) * (k ^ 2)) + (7374 * g * (i ^ 3)) + (7983 * (f ^ 2) * (g ^ 2)) + (18750 * e * (f ^ 3)) + (20038 * e * (d ^ 3)) + (20038 * f * (d ^ 3)) + (24058 * d * (e ^ 3)) + (24910 * d * (f ^ 3)) + (25123 * (e ^ 2) * (f ^ 2)) + (36293 * (d ^ 2) * (f ^ 2)) + (70694 * i * (e ^ 3)) + (80339 * (d ^ 2) * (e ^ 2)) + ((-173324) * e * i * (d ^ 2)) + ((-168656) * f * k * (d ^ 2)) + ((-113170) * d * e * (i ^ 2)) + ((-104390) * i * k * (d ^ 2)) + ((-89348) * d * k * (i ^ 2)) + ((-78672) * d * e * (k ^ 2)) + ((-56544) * e * f * (i ^ 2)) + ((-45072) * d * i * (k ^ 2)) + ((-42176) * d * g * (i ^ 2)) + ((-42176) * d * g * (k ^ 2)) + ((-40076) * e * g * (d ^ 2)) + ((-40076) * f * g * (d ^ 2)) + ((-38868) * f * g * (e ^ 2)) + ((-20038) * d * e * (g ^ 2)) + ((-20038) * d * f * (g ^ 2)) + ((-18312) * e * k * (i ^ 2)) + ((-17984) * d * k * (f ^ 2)) + ((-17023) * g * k * (f ^ 2)) + ((-17023) * i * k * (f ^ 2)) + ((-14422) * g * i * (f ^ 2)) + ((-8944) * d * f * (k ^ 2)) + ((-8944) * e * f * (k ^ 2)) + ((-5104) * e * k * (f ^ 2)) + ((-4472) * f * g * (k ^ 2)) + ((-4472) * f * i * (k ^ 2)) + ((-3560) * d * i * (e ^ 2)) + ((-3180) * e * g * (f ^ 2)) + ((-1448) * g * i * (k ^ 2)) + ((-1351) * g * k * (e ^ 2)) + ((-96) * f * i * (g ^ 2)) + ((-56) * e * i * (k ^ 2)) + ((-48) * f * k * (g ^ 2)) + (552 * f * k * (i ^ 2)) + (2840 * e * g * (k ^ 2)) + (3898 * d * f * (i ^ 2)) + (4620 * e * i * (g ^ 2)) + (4620 * e * k * (g ^ 2)) + (5372 * e * f * (g ^ 2)) + (5372 * f * g * (i ^ 2)) + (5926 * g * k * (i ^ 2)) + (8436 * d * k * (e ^ 2)) + (19062 * e * i * (f ^ 2)) + (26404 * f * k * (e ^ 2)) + (29762 * g * i * (e ^ 2)) + (32380 * d * e * (f ^ 2)) + (33316 * e * g * (i ^ 2)) + (44776 * d * f * (e ^ 2)) + (45576 * f * i * (e ^ 2)) + (50052 * d * i * (f ^ 2)) + (50202 * d * g * (e ^ 2)) + (58142 * d * g * (f ^ 2)) + (64991 * i * k * (e ^ 2)) + (75532 * e * k * (d ^ 2)) + (80248 * f * i * (d ^ 2)) + (123256 * e * f * (d ^ 2)) + ((-114390) * d * e * i * k) + ((-88216) * d * e * f * k) + ((-75112) * d * e * g * i) + ((-73566) * d * f * i * k) + ((-64410) * d * f * g * k) + ((-42176) * d * g * i * k) + ((-17444) * e * f * g * i) + ((-7224) * f * g * i * k) + (2376 * e * f * i * k) + (10572 * e * f * g * k) + (11052 * e * g * i * k) + (39884 * d * f * g * i) + (69354 * d * e * g * k) + (86548 * d * e * f * i) + (95096 * d * e * f * g))) * hq1 +
    ((-1 / 123480 : ℂ) * ((5227 * (e ^ 4)) + (7374 * (i ^ 4)) + (8079 * (f ^ 4)) + ((-42176) * d * (i ^ 3)) + ((-42176) * d * (k ^ 3)) + ((-36004) * d * (f ^ 3)) + ((-24402) * i * (e ^ 3)) + ((-17023) * (f ^ 2) * (k ^ 2)) + ((-13948) * k * (e ^ 3)) + ((-11686) * k * (f ^ 3)) + ((-10591) * (e ^ 2) * (k ^ 2)) + ((-4472) * f * (k ^ 3)) + ((-3034) * (e ^ 2) * (f ^ 2)) + ((-1448) * i * (k ^ 3)) + (1364 * e * (f ^ 3)) + (2840 * e * (k ^ 3)) + (3641 * (f ^ 2) * (i ^ 2)) + (4232 * i * (f ^ 3)) + (4478 * (i ^ 2) * (k ^ 2)) + (5468 * f * (i ^ 3)) + (8908 * f * (e ^ 3)) + (12012 * d * (e ^ 3)) + (13300 * k * (i ^ 3)) + (15295 * (e ^ 2) * (i ^ 2)) + (28696 * e * (i ^ 3)) + (40076 * (d ^ 2) * (e ^ 2)) + (40076 * (d ^ 2) * (f ^ 2)) + ((-104390) * d * e * (i ^ 2)) + ((-84352) * d * i * (k ^ 2)) + ((-84352) * d * k * (i ^ 2)) + ((-64314) * d * f * (k ^ 2)) + ((-46748) * d * e * (f ^ 2)) + ((-39286) * f * k * (e ^ 2)) + ((-11648) * f * i * (k ^ 2)) + ((-7680) * e * f * (i ^ 2)) + ((-7140) * d * i * (e ^ 2)) + ((-7112) * i * k * (f ^ 2)) + ((-1804) * f * k * (i ^ 2)) + ((-96) * f * g * (i ^ 2)) + ((-48) * f * g * (k ^ 2)) + (1268 * d * f * (e ^ 2)) + (3296 * e * k * (f ^ 2)) + (4013 * g * i * (e ^ 2)) + (4013 * g * k * (e ^ 2)) + (4620 * e * g * (i ^ 2)) + (4620 * e * g * (k ^ 2)) + (6220 * f * i * (e ^ 2)) + (7983 * g * i * (f ^ 2)) + (7983 * g * k * (f ^ 2)) + (9272 * e * i * (k ^ 2)) + (10668 * e * f * (k ^ 2)) + (12730 * i * k * (e ^ 2)) + (20038 * d * f * (i ^ 2)) + (21030 * e * i * (f ^ 2)) + (32936 * d * k * (e ^ 2)) + (35128 * e * k * (i ^ 2)) + (42368 * d * i * (f ^ 2)) + (60114 * d * e * (k ^ 2)) + (80152 * e * f * (d ^ 2)) + (82348 * d * k * (f ^ 2)) + ((-85120) * d * f * i * k) + ((-84352) * d * e * i * k) + ((-20038) * d * e * g * i) + ((-20038) * d * e * g * k) + ((-20038) * d * f * g * i) + ((-20038) * d * f * g * k) + ((-144) * f * g * i * k) + (5372 * e * f * g * i) + (5372 * e * f * g * k) + (9240 * e * g * i * k) + (13444 * e * f * i * k) + (47828 * d * e * f * i) + (127884 * d * e * f * k))) * hq2 +
    ((-1 / 30870 : ℂ) * ((2947 * (f ^ 3)) + ((-42908) * d * (f ^ 2)) + ((-33630) * d * (e ^ 2)) + ((-20785) * e * (k ^ 2)) + ((-10381) * i * (d ^ 2)) + ((-7270) * k * (e ^ 2)) + ((-7215) * k * (d ^ 2)) + ((-6284) * g * (f ^ 2)) + ((-3350) * k * (f ^ 2)) + ((-2963) * i * (k ^ 2)) + ((-2947) * f * (k ^ 2)) + (477 * i * (f ^ 2)) + (2760 * f * (e ^ 2)) + (4470 * g * (e ^ 2)) + (39523 * e * (f ^ 2)) + (39961 * f * (d ^ 2)) + (43029 * d * (k ^ 2)) + (43111 * e * (d ^ 2)) + ((-82634) * d * e * f) + ((-37362) * e * f * k) + ((-20278) * d * e * k) + ((-9102) * f * i * k) + ((-8100) * d * e * i) + ((-6332) * d * g * k) + ((-1680) * e * i * k) + ((-650) * e * f * g) + (219 * f * g * k) + (6672 * e * g * k) + (8100 * e * f * i) + (9904 * d * f * i) + (11156 * d * f * g) + (22407 * d * i * k) + (23852 * d * e * g) + (86654 * d * f * k))) * hc0 +
    ((-1 / 61740 : ℂ) * (((-4472) * (f ^ 3)) + ((-39590) * d * (f ^ 2)) + ((-18178) * d * (e ^ 2)) + ((-12080) * e * (k ^ 2)) + ((-10032) * f * (e ^ 2)) + ((-10019) * i * (d ^ 2)) + ((-10019) * k * (d ^ 2)) + ((-7935) * g * (f ^ 2)) + ((-7715) * i * (f ^ 2)) + ((-1867) * k * (e ^ 2)) + (607 * g * (e ^ 2)) + (1448 * i * (k ^ 2)) + (4472 * f * (k ^ 2)) + (12104 * e * (f ^ 2)) + (14032 * k * (f ^ 2)) + (40076 * e * (d ^ 2)) + (40076 * f * (d ^ 2)) + (42176 * d * (k ^ 2)) + ((-63796) * d * e * f) + ((-21834) * e * f * k) + ((-15748) * d * e * k) + ((-11946) * e * f * i) + ((-7472) * e * f * g) + ((-4900) * e * i * k) + ((-374) * d * e * i) + (48 * f * g * k) + (8900 * f * i * k) + (18564 * d * f * i) + (20038 * d * e * g) + (20038 * d * f * g) + (21228 * d * i * k) + (87094 * d * f * k))) * hc1 +
    ((1 / 5145 : ℂ) * (((-424) * k * (f ^ 2)) + ((-210) * e * (f ^ 2)) + (315 * f * (e ^ 2)) + (385 * e * (k ^ 2)) + (424 * i * (f ^ 2)) + ((-32) * d * f * k) + (525 * d * e * f) + (984 * e * f * k))) * hc2 +
    ((-8 / 5145 : ℂ) * f * k * ((4 * d) + (53 * f))) * hc3

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma collinearArrowhead_classification (g i k d e f : ℂ)
    (hq0 : ((e ^ 2) + (f ^ 2) + ((-1) * (i ^ 2)) + ((-1) * (k ^ 2)) + ((-1) * i * k) + ((-2) * e * i) + ((-2) * f * k) + (2 * e * f)) = 0)
    (hq1 : (((-2) * (f ^ 2)) + (2 * (k ^ 2)) + (i * k) + ((-1) * g * i) + ((-1) * g * k) + ((-2) * e * f) + (2 * d * e) + (2 * d * f) + (4 * f * k)) = 0)
    (hq2 : ((d ^ 2) + (f ^ 2) + ((-1) * (g ^ 2)) + ((-1) * (k ^ 2)) + (g * k) + ((-2) * d * f) + ((-2) * d * g) + ((-2) * f * k)) = 0)
    (hc0 : ((i * (f ^ 2)) + (k * (e ^ 2)) + ((-1) * i * (k ^ 2)) + ((-1) * k * (i ^ 2)) + ((-2) * e * i * k) + ((-2) * f * i * k)) = 0)
    (hc1 : ((g * (e ^ 2)) + (g * (f ^ 2)) + (k * (i ^ 2)) + ((-1) * g * (i ^ 2)) + ((-1) * g * (k ^ 2)) + ((-1) * k * (e ^ 2)) + ((-2) * i * (f ^ 2)) + (2 * i * (k ^ 2)) + ((-2) * e * g * i) + ((-2) * f * g * k) + ((-2) * g * i * k) + (2 * d * e * k) + (2 * d * f * i) + (2 * e * f * g) + (2 * e * i * k) + (4 * f * i * k)) = 0)
    (hc2 : ((i * (d ^ 2)) + (i * (f ^ 2)) + (k * (d ^ 2)) + ((-1) * i * (g ^ 2)) + ((-1) * i * (k ^ 2)) + ((-1) * k * (g ^ 2)) + ((-2) * g * (f ^ 2)) + (2 * g * (k ^ 2)) + ((-2) * d * e * k) + ((-2) * d * f * i) + ((-2) * d * g * i) + ((-2) * d * g * k) + ((-2) * e * f * g) + ((-2) * f * i * k) + (2 * g * i * k) + (4 * f * g * k)) = 0)
    (hc3 : ((g * (f ^ 2)) + (k * (g ^ 2)) + ((-1) * g * (k ^ 2)) + ((-1) * k * (d ^ 2)) + ((-2) * f * g * k) + (2 * d * g * k)) = 0)
    (hrow0 : g ≠ 0 ∨ d ≠ 0) (hrow1 : i ≠ 0 ∨ e ≠ 0)
    (hrow2 : k ≠ 0 ∨ f ≠ 0)
    : g = 0 ∧ i = 0 ∧ k = 0 ∧ d = f ∧ e = -f := by
  have hd : d ≠ 0 := by
    intro hz
    have hp : g ^ 3 = 0 := by
      subst d
      linear_combination hc3 - g * hq2
    exact hrow0.elim (fun h => h (eq_zero_of_pow_eq_zero hp)) (fun h => h hz)
  have he : e ≠ 0 := by
    intro hz
    have hp : i ^ 3 = 0 := by
      subst e
      linear_combination hc0 - i * hq0
    exact hrow1.elim (fun h => h (eq_zero_of_pow_eq_zero hp)) (fun h => h hz)
  have hf : f ≠ 0 := by
    intro hz
    have hp : k ^ 3 = 0 := by
      subst f
      linear_combination hc0 - k * hq0
    exact hrow2.elim (fun h => h (eq_zero_of_pow_eq_zero hp)) (fun h => h hz)
  have hi : i = 0 := by
    have hp := collinearArrowhead_mid_annihilated g i k d e f hq0 hq1 hq2 hc0 hc1 hc2 hc3
    exact (mul_eq_zero.mp hp).resolve_left (mul_ne_zero (pow_ne_zero 2 he) (pow_ne_zero 3 hf))
  have hg : g = 0 := by
    have hp := collinearArrowhead_mid_annihilated i g (-k) e d (-f)
      (by linear_combination 1 * hq2)
      (by linear_combination 1 * hq1)
      (by linear_combination 1 * hq0)
      (by linear_combination 1 * hc3)
      (by linear_combination 1 * hc2)
      (by linear_combination 1 * hc1)
      (by linear_combination 1 * hc0)
    exact (mul_eq_zero.mp hp).resolve_left (mul_ne_zero (pow_ne_zero 2 hd) (pow_ne_zero 3 (neg_ne_zero.mpr hf)))
  have hk : k = 0 := by
    have hp := collinearArrowhead_mid_annihilated (-g) k i (-d) f e
      (by linear_combination 1 * hq0)
      (by linear_combination (-2) * hq0 + (-1) * hq1)
      (by linear_combination 1 * hq0 + 1 * hq1 + 1 * hq2)
      (by linear_combination 1 * hc0)
      (by linear_combination (-3) * hc0 + (-1) * hc1)
      (by linear_combination 3 * hc0 + 2 * hc1 + 1 * hc2)
      (by linear_combination (-1) * hc0 + (-1) * hc1 + (-1) * hc2 + (-1) * hc3)
    exact (mul_eq_zero.mp hp).resolve_left (mul_ne_zero (pow_ne_zero 2 hf) (pow_ne_zero 3 he))
  have hdf : d = f := by
    have hp : (d - f) ^ 2 = 0 := by
      subst g; subst i; subst k
      linear_combination hq2
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hp)
  have hef : e = -f := by
    have hp : (e + f) ^ 2 = 0 := by
      subst g; subst i; subst k
      linear_combination hq0
    exact eq_neg_of_add_eq_zero_left (eq_zero_of_pow_eq_zero hp)
  exact ⟨hg, hi, hk, hdf, hef⟩


namespace ArrowheadMatrix

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


def arrowhead (g i k d e f m n x y : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![g*y, 0, 0, d*y], ![0, i*x, 0, e*x],
    ![0, 0, k*(x-y), f*(x-y)], ![d*y, e*x, f*(x-y), m*x+n*y]]

def star3 (u v : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0, 0, 0, u], ![0, 0, 0, v], ![0, 0, 0, -u-v], ![u, v, -u-v, 0]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma normalized_level_classification (g i k d e f : ℂ)
    (hp : ∀ x y : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + arrowhead g i k d e f (-i-k-2*e-2*f) (-g+k-2*d+2*f) x y r s) = 24)
    (hrow0 : g ≠ 0 ∨ d ≠ 0) (hrow1 : i ≠ 0 ∨ e ≠ 0)
    (hrow2 : k ≠ 0 ∨ f ≠ 0) :
    g = 0 ∧ i = 0 ∧ k = 0 ∧ d = f ∧ e = -f := by
  have hap := hp (1) (0)
  have ham := hp (-1) (0)
  have happ := hp (2) (0)
  have hamm := hp (-2) (0)
  have hbp := hp (0) (1)
  have hbm := hp (0) (-1)
  have hbpp := hp (0) (2)
  have hbmm := hp (0) (-2)
  have hcp := hp (1) (1)
  have hcm := hp (-1) (-1)
  have hcpp := hp (2) (2)
  have hcmm := hp (-2) (-2)
  have hdp := hp (1) (-1)
  have hdm := hp (-1) (1)
  have hdpp := hp (2) (-2)
  have hdmm := hp (-2) (2)
  simp [perm4, Matrix.of_apply, arrowhead] at hap ham happ hamm hbp hbm hbpp hbmm hcp hcm hcpp hcmm hdp hdm hdpp hdmm
  have hq0 : ((e ^ 2) + (f ^ 2) + ((-1) * (i ^ 2)) + ((-1) * (k ^ 2)) + ((-1) * i * k) + ((-2) * e * i) + ((-2) * f * k) + (2 * e * f)) = 0 := by
    linear_combination (1/3 : ℂ)*hap + (1/3 : ℂ)*ham - (1/48 : ℂ)*happ - (1/48 : ℂ)*hamm
  have hq2 : ((d ^ 2) + (f ^ 2) + ((-1) * (g ^ 2)) + ((-1) * (k ^ 2)) + (g * k) + ((-2) * d * f) + ((-2) * d * g) + ((-2) * f * k)) = 0 := by
    linear_combination (1/3 : ℂ)*hbp + (1/3 : ℂ)*hbm - (1/48 : ℂ)*hbpp - (1/48 : ℂ)*hbmm
  have hq1 : (((-2) * (f ^ 2)) + (2 * (k ^ 2)) + (i * k) + ((-1) * g * i) + ((-1) * g * k) + ((-2) * e * f) + (2 * d * e) + (2 * d * f) + (4 * f * k)) = 0 := by
    linear_combination (1/3 : ℂ)*hcp + (1/3 : ℂ)*hcm - (1/48 : ℂ)*hcpp - (1/48 : ℂ)*hcmm - hq0 - hq2
  have hc0 : ((i * (f ^ 2)) + (k * (e ^ 2)) + ((-1) * i * (k ^ 2)) + ((-1) * k * (i ^ 2)) + ((-2) * e * i * k) + ((-2) * f * i * k)) = 0 := by
    linear_combination (1/12 : ℂ)*happ - (1/12 : ℂ)*hamm - (1/6 : ℂ)*hap + (1/6 : ℂ)*ham
  have hc3 : ((g * (f ^ 2)) + (k * (g ^ 2)) + ((-1) * g * (k ^ 2)) + ((-1) * k * (d ^ 2)) + ((-2) * f * g * k) + (2 * d * g * k)) = 0 := by
    linear_combination (1/12 : ℂ)*hbpp - (1/12 : ℂ)*hbmm - (1/6 : ℂ)*hbp + (1/6 : ℂ)*hbm
  have hc1 : ((g * (e ^ 2)) + (g * (f ^ 2)) + (k * (i ^ 2)) + ((-1) * g * (i ^ 2)) + ((-1) * g * (k ^ 2)) + ((-1) * k * (e ^ 2)) + ((-2) * i * (f ^ 2)) + (2 * i * (k ^ 2)) + ((-2) * e * g * i) + ((-2) * f * g * k) + ((-2) * g * i * k) + (2 * d * e * k) + (2 * d * f * i) + (2 * e * f * g) + (2 * e * i * k) + (4 * f * i * k)) = 0 := by
    linear_combination (1/2 : ℂ)*((1/12 : ℂ)*hcpp - (1/12 : ℂ)*hcmm - (1/6 : ℂ)*hcp + (1/6 : ℂ)*hcm) - (1/2 : ℂ)*((1/12 : ℂ)*hdpp - (1/12 : ℂ)*hdmm - (1/6 : ℂ)*hdp + (1/6 : ℂ)*hdm) - hc3
  have hc2 : ((i * (d ^ 2)) + (i * (f ^ 2)) + (k * (d ^ 2)) + ((-1) * i * (g ^ 2)) + ((-1) * i * (k ^ 2)) + ((-1) * k * (g ^ 2)) + ((-2) * g * (f ^ 2)) + (2 * g * (k ^ 2)) + ((-2) * d * e * k) + ((-2) * d * f * i) + ((-2) * d * g * i) + ((-2) * d * g * k) + ((-2) * e * f * g) + ((-2) * f * i * k) + (2 * g * i * k) + (4 * f * g * k)) = 0 := by
    linear_combination (1/2 : ℂ)*((1/12 : ℂ)*hcpp - (1/12 : ℂ)*hcmm - (1/6 : ℂ)*hcp + (1/6 : ℂ)*hcm) + (1/2 : ℂ)*((1/12 : ℂ)*hdpp - (1/12 : ℂ)*hdmm - (1/6 : ℂ)*hdp + (1/6 : ℂ)*hdm) - hc0
  exact collinearArrowhead_classification g i k d e f hq0 hq1 hq2 hc0 hc1 hc2 hc3 hrow0 hrow1 hrow2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma level_classification (g i k d e f m n : ℂ)
    (hp : ∀ x y : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + arrowhead g i k d e f m n x y r s) = 24)
    (hrow0 : g ≠ 0 ∨ d ≠ 0) (hrow1 : i ≠ 0 ∨ e ≠ 0)
    (hrow2 : k ≠ 0 ∨ f ≠ 0) :
    g = 0 ∧ i = 0 ∧ k = 0 ∧ d = f ∧ e = -f ∧ m = 0 ∧ n = 0 := by
  have ha1 := hp 1 0
  have ham1 := hp (-1) 0
  have ha2 := hp 2 0
  have ham2 := hp (-2) 0
  have hb1 := hp 0 1
  have hbm1 := hp 0 (-1)
  have hb2 := hp 0 2
  have hbm2 := hp 0 (-2)
  simp [perm4, Matrix.of_apply, arrowhead] at ha1 ham1 ha2 ham2 hb1 hbm1 hb2 hbm2
  have hm : m = -i-k-2*e-2*f := by
    linear_combination (1/9 : ℂ)*ha1 - (1/9 : ℂ)*ham1 - (1/72 : ℂ)*ha2 + (1/72 : ℂ)*ham2
  have hn : n = -g+k-2*d+2*f := by
    linear_combination (1/9 : ℂ)*hb1 - (1/9 : ℂ)*hbm1 - (1/72 : ℂ)*hb2 + (1/72 : ℂ)*hbm2
  rw [hm, hn] at hp
  rcases normalized_level_classification g i k d e f hp hrow0 hrow1 hrow2 with
    ⟨hg, hi, hk, hd, he⟩
  refine ⟨hg, hi, hk, hd, he, ?_, ?_⟩
  · linear_combination hm - hi - hk - 2*he
  · linear_combination hn - hg + hk - 2*hd

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma three_collinear_zero_rows (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hsA : ∀ r s : Fin 4, A r s = A s r)
    (hsB : ∀ r s : Fin 4, B r s = B s r)
    (hA0 : ∀ j : Fin 4, A 0 j = 0)
    (hB1 : ∀ j : Fin 4, B 1 j = 0)
    (hAB2 : ∀ j : Fin 4, A 2 j + B 2 j = 0)
    (hp : ∀ x y : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + x*A r s + y*B r s) = 24)
    (hrow0 : ∃ j : Fin 4, B 0 j ≠ 0)
    (hrow1 : ∃ j : Fin 4, A 1 j ≠ 0)
    (hrow2 : ∃ j : Fin 4, A 2 j ≠ 0) :
    ∃ f : ℂ, f ≠ 0 ∧ A = star3 0 (-f) ∧ B = star3 f 0 := by
  have hA12 : A 1 2 = 0 := by
    have h := hAB2 1
    rw [hsB 2 1, hB1 2, add_zero] at h
    exact (hsA 1 2).trans h
  have hB02 : B 0 2 = 0 := by
    have h := hAB2 0
    rw [hsA 2 0, hA0 2, zero_add] at h
    exact (hsB 0 2).trans h
  have hB22 : B 2 2 = -A 2 2 := by linear_combination hAB2 2
  have hB23 : B 2 3 = -A 2 3 := by linear_combination hAB2 3
  have hAshape : A =
      ![![0,0,0,0], ![0,A 1 1,0,A 1 3],
        ![0,0,A 2 2,A 2 3], ![0,A 1 3,A 2 3,A 3 3]] := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [hA0, hA12, hsA 1 0, hsA 2 0, hsA 3 0,
        hsA 2 1, hsA 3 1, hsA 3 2]
  have hBshape : B =
      ![![B 0 0,0,0,B 0 3], ![0,0,0,0],
        ![0,0,-A 2 2,-A 2 3], ![B 0 3,0,-A 2 3,B 3 3]] := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [hB1, hB02, hB22, hB23, hsB 0 1,
        hsB 2 0, hsB 3 0, hsB 2 1, hsB 3 1, hsB 3 2]
  have hfamily (x y : ℂ) :
      Matrix.of (fun (r s : Fin 4) => x*A r s + y*B r s) =
      arrowhead (B 0 0) (A 1 1) (A 2 2) (B 0 3) (A 1 3) (A 2 3)
        (A 3 3) (B 3 3) x y := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [Matrix.of_apply, arrowhead, hA0, hB1, hA12, hB02, hB22, hB23,
        hsA 1 0, hsA 2 0, hsA 3 0, hsA 2 1, hsA 3 1, hsA 3 2,
        hsB 0 1, hsB 2 0, hsB 3 0, hsB 2 1, hsB 3 1, hsB 3 2] <;> ring
  have hp' : ∀ x y : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + arrowhead (B 0 0) (A 1 1) (A 2 2) (B 0 3) (A 1 3) (A 2 3)
        (A 3 3) (B 3 3) x y r s) = 24 := by
    intro x y
    rw [← hfamily x y]
    simpa only [Matrix.of_apply, add_assoc] using hp x y
  have h0 : B 0 0 ≠ 0 ∨ B 0 3 ≠ 0 := by
    by_cases hg : B 0 0 = 0
    · right
      intro hd
      rcases hrow0 with ⟨j, hj⟩
      fin_cases j <;> simp [hg, hd, hB02, hsB 0 1, hB1] at hj
    · exact Or.inl hg
  have h1 : A 1 1 ≠ 0 ∨ A 1 3 ≠ 0 := by
    by_cases hi : A 1 1 = 0
    · right
      intro he
      rcases hrow1 with ⟨j, hj⟩
      fin_cases j <;> simp [hi, he, hA12, hsA 1 0, hA0] at hj
    · exact Or.inl hi
  have h2 : A 2 2 ≠ 0 ∨ A 2 3 ≠ 0 := by
    by_cases hk : A 2 2 = 0
    · right
      intro hf
      rcases hrow2 with ⟨j, hj⟩
      fin_cases j <;> simp [hk, hf, hA12, hsA 2 0, hsA 2 1, hA0] at hj
    · exact Or.inl hk
  rcases level_classification (B 0 0) (A 1 1) (A 2 2) (B 0 3) (A 1 3) (A 2 3)
      (A 3 3) (B 3 3) hp' h0 h1 h2 with ⟨hg, hi, hk, hd, he, hm, hn⟩
  refine ⟨A 2 3, h2.resolve_left (fun h => h hk), ?_, ?_⟩
  · apply hAshape.trans
    ext r s
    fin_cases r <;> fin_cases s <;> simp [star3, hi, hk, he, hm]
  · apply hBshape.trans
    ext r s
    fin_cases r <;> fin_cases s <;> simp [star3, hg, hk, hd, hn]


namespace OrdinaryStarMaximal

def star (x y : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0, x, y, -x - y], ![x, 0, 0, 0],
    ![y, 0, 0, 0], ![-x - y, 0, 0, 0]]

def symMatrix (a b c d e f g h i j : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![a, b, c, d], ![b, e, f, g], ![c, f, h, i], ![d, g, i, j]]

lemma first_order (a b c d e f g h i j : ℂ)
    (hp : ∀ x y z : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + star x y r s + z * symMatrix a b c d e f g h i j r s) = 24) (x y : ℂ) :
    6 * a + 12 * b + 12 * c + 12 * d + e * x ^ 2 - 4 * e * x + 6 * e + 2 * f * x * y - 4 * f * x - 4 * f * y + 12 * f - 2 * g * x ^ 2 - 2 * g * x * y + 4 * g * y + 12 * g + h * y ^ 2 - 4 * h * y + 6 * h - 2 * i * x * y + 4 * i * x - 2 * i * y ^ 2 + 12 * i + j * x ^ 2 + 2 * j * x * y + 4 * j * x + j * y ^ 2 + 4 * j * y + 6 * j = 0 := by
  have h1 := hp x y 1
  have hm1 := hp x y (-1)
  have h2 := hp x y 2
  have hm2 := hp x y (-2)
  simp [perm4, Matrix.of_apply, star, symMatrix] at h1 hm1 h2 hm2
  linear_combination (2 / 3 : ℂ) * h1 - (2 / 3 : ℂ) * hm1 -
    (1 / 12 : ℂ) * h2 + (1 / 12 : ℂ) * hm2

lemma maximal_coordinates (a b c d e f g h i j : ℂ)
    (hp : ∀ x y z : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + star x y r s + z * symMatrix a b c d e f g h i j r s) = 24) :
    a = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0 ∧ i = 0 ∧ j = 0 ∧ d = -b - c := by
  have v0 := first_order a b c d e f g h i j hp 0 0
  have v1 := first_order a b c d e f g h i j hp 1 0
  have v2 := first_order a b c d e f g h i j hp (-1) 0
  have v3 := first_order a b c d e f g h i j hp 0 1
  have v4 := first_order a b c d e f g h i j hp 0 (-1)
  have v5 := first_order a b c d e f g h i j hp 1 1
  have he : e = j := by
    linear_combination (-2/3 : ℂ) * v0 + (5/12 : ℂ) * v1 + (1/4 : ℂ) * v2 + (1/3 : ℂ) * v3 + (-1/3 : ℂ) * v5
  have hf : f = j := by
    linear_combination (5/6 : ℂ) * v0 + (-3/8 : ℂ) * v1 + (-1/8 : ℂ) * v2 + (-3/8 : ℂ) * v3 + (-1/8 : ℂ) * v4 + (1/6 : ℂ) * v5
  have hg : g = j := by
    linear_combination (1/6 : ℂ) * v0 + (-1/24 : ℂ) * v1 + (-1/8 : ℂ) * v2 + (1/6 : ℂ) * v3 + (-1/6 : ℂ) * v5
  have hh : h = j := by
    linear_combination (-2/3 : ℂ) * v0 + (1/3 : ℂ) * v1 + (5/12 : ℂ) * v3 + (1/4 : ℂ) * v4 + (-1/3 : ℂ) * v5
  have hi : i = j := by
    linear_combination (1/6 : ℂ) * v0 + (1/6 : ℂ) * v1 + (-1/24 : ℂ) * v3 + (-1/8 : ℂ) * v4 + (-1/6 : ℂ) * v5
  have ha : a + 2 * (b + c + d) + 9 * j = 0 := by
    linear_combination (-5/6 : ℂ) * v0 + (-1/4 : ℂ) * v1 + (1/4 : ℂ) * v2 + (-1/4 : ℂ) * v3 + (1/4 : ℂ) * v4 + (1 : ℂ) * v5
  have hae : a = -2 * (b + c + d) - 9 * j := by
    linear_combination ha
  have h1 := hp 0 0 1
  have hm1 := hp 0 0 (-1)
  have h2 := hp 0 0 2
  have hm2 := hp 0 0 (-2)
  rw [he, hf, hg, hh, hi, hae] at h1 hm1 h2 hm2
  simp [perm4, Matrix.of_apply, star, symMatrix] at h1 hm1 h2 hm2
  have hq : 2 * ((b + c + d) ^ 2 - 6 * (b + c + d) * j - 63 * j ^ 2) = 0 := by
    linear_combination (2 / 3 : ℂ) * h1 + (2 / 3 : ℂ) * hm1 -
      (1 / 24 : ℂ) * h2 - (1 / 24 : ℂ) * hm2
  have hc : 4 * j * ((b + c + d) ^ 2 - 6 * (b + c + d) * j - 39 * j ^ 2) = 0 := by
    linear_combination (1 / 12 : ℂ) * h2 - (1 / 12 : ℂ) * hm2 -
      (1 / 6 : ℂ) * h1 + (1 / 6 : ℂ) * hm1
  have hj3 : j ^ 3 = 0 := by
    linear_combination (1 / 96 : ℂ) * hc - (j / 48) * hq
  have hj : j = 0 := eq_zero_of_pow_eq_zero hj3
  rw [hj] at hq
  have hp2 : (b + c + d) ^ 2 = 0 := by
    linear_combination (1 / 2 : ℂ) * hq
  have hp0 : b + c + d = 0 := eq_zero_of_pow_eq_zero hp2
  have hd : d = -b - c := by
    linear_combination hp0
  refine ⟨?_, he.trans hj, hf.trans hj, hg.trans hj, hh.trans hj, hi.trans hj, hj, hd⟩
  linear_combination ha - 2 * hp0 - 9 * hj

lemma star_plane_maximal (T : Matrix (Fin 4) (Fin 4) ℂ)
    (hs : ∀ r s : Fin 4, T r s = T s r)
    (hp : ∀ x y z : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + star x y r s + z * T r s) = 24) :
    T = star (T 0 1) (T 0 2) := by
  have hT : T = symMatrix (T 0 0) (T 0 1) (T 0 2) (T 0 3)
      (T 1 1) (T 1 2) (T 1 3) (T 2 2) (T 2 3) (T 3 3) := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [symMatrix]
    all_goals exact hs _ _
  have hc := maximal_coordinates (T 0 0) (T 0 1) (T 0 2) (T 0 3)
    (T 1 1) (T 1 2) (T 1 3) (T 2 2) (T 2 3) (T 3 3)
    (by simpa only [← hT] using hp)
  rcases hc with ⟨ha, he, hf, hg, hh, hi, hj, hd⟩
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [star, ha, he, hf, hg, hh, hi, hj, hd,
      hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2]


end OrdinaryStarMaximal

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma star3_maximal (T : Matrix (Fin 4) (Fin 4) ℂ)
    (hs : ∀ r s : Fin 4, T r s = T s r)
    (hp : ∀ u v z : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + star3 u v r s + z*T r s) = 24) :
    ∃ u v : ℂ, T = star3 u v := by
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 0 3
  let T' : Matrix (Fin 4) (Fin 4) ℂ := T.submatrix σ σ
  have hs' (r s : Fin 4) : T' r s = T' s r := hs _ _
  have hp' (x y z : ℂ) : Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + OrdinaryStarMaximal.star x y r s + z*T' r s) = 24 := by
    let M : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun r s =>
      (1 : ℂ) + star3 (-x-y) x r s + z*T r s
    have heq : M.submatrix σ σ = Matrix.of (fun (r s : Fin 4) =>
        (1 : ℂ) + OrdinaryStarMaximal.star x y r s + z*T' r s) := by
      ext r s
      fin_cases r <;> fin_cases s <;>
        simp [M, T', σ, Matrix.submatrix_apply, Matrix.of_apply,
          OrdinaryStarMaximal.star, star3, Equiv.swap_apply_def] <;> ring
    have hinv : Matrix.permanent (M.submatrix σ σ) = Matrix.permanent M := by
      change Matrix.permanent ((M.submatrix σ id).submatrix id σ) = Matrix.permanent M
      rw [Matrix.permanent_permute_rows, Matrix.permanent_permute_cols]
    rw [← heq]
    exact hinv.trans (hp (-x-y) x z)
  have hmax := OrdinaryStarMaximal.star_plane_maximal T' hs' hp'
  refine ⟨-T' 0 1 - T' 0 2, T' 0 1, ?_⟩
  have hT : T = T'.submatrix σ σ := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [T', σ, Matrix.submatrix_apply, Equiv.swap_apply_def]
  calc
    T = T'.submatrix σ σ := hT
    _ = (OrdinaryStarMaximal.star (T' 0 1) (T' 0 2)).submatrix σ σ :=
      congrArg (fun (M : Matrix (Fin 4) (Fin 4) ℂ) => M.submatrix σ σ) hmax
    _ = star3 (-T' 0 1 - T' 0 2) (T' 0 1) := by
      ext r s
      change OrdinaryStarMaximal.star (T' 0 1) (T' 0 2) (σ r) (σ s) =
        star3 (-T' 0 1 - T' 0 2) (T' 0 1) r s
      fin_cases r <;> fin_cases s <;>
        simp [σ, OrdinaryStarMaximal.star, star3, Equiv.swap_apply_def] <;> ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma three_collinear_zero_rows_third_in_span (A B C : Matrix (Fin 4) (Fin 4) ℂ)
    (hsA : ∀ r s : Fin 4, A r s = A s r)
    (hsB : ∀ r s : Fin 4, B r s = B s r)
    (hsC : ∀ r s : Fin 4, C r s = C s r)
    (hA0 : ∀ j : Fin 4, A 0 j = 0)
    (hB1 : ∀ j : Fin 4, B 1 j = 0)
    (hAB2 : ∀ j : Fin 4, A 2 j + B 2 j = 0)
    (hp : ∀ x y z : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + x*A r s + y*B r s + z*C r s) = 24)
    (hrow0 : ∃ j : Fin 4, B 0 j ≠ 0)
    (hrow1 : ∃ j : Fin 4, A 1 j ≠ 0)
    (hrow2 : ∃ j : Fin 4, A 2 j ≠ 0) :
    ∃ x y : ℂ, C = Matrix.of (fun (r s : Fin 4) => x*A r s + y*B r s) := by
  have hpAB (x y : ℂ) : Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + x*A r s + y*B r s) = 24 := by
    simpa only [zero_mul, add_zero] using hp x y 0
  rcases three_collinear_zero_rows A B hsA hsB hA0 hB1 hAB2 hpAB hrow0 hrow1 hrow2 with
    ⟨f, hf, hA, hB⟩
  have hspan (u v : ℂ) : Matrix.of (fun (r s : Fin 4) =>
      (-v/f)*A r s + (u/f)*B r s) = star3 u v := by
    rw [hA, hB]
    ext r s
    fin_cases r <;> fin_cases s <;> simp [Matrix.of_apply, star3] <;>
      field_simp [hf] <;> ring
  have hpStar (u v z : ℂ) : Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + star3 u v r s + z*C r s) = 24 := by
    rw [← hspan u v]
    simpa only [Matrix.of_apply, add_assoc] using hp (-v/f) (u/f) z
  rcases star3_maximal C hsC hpStar with ⟨u, v, hC⟩
  exact ⟨-v/f, u/f, hC.trans (hspan u v).symm⟩

end ArrowheadMatrix

end PEqualNP.Outside.L_gct_231



namespace PEqualNP.Outside.L_gct_231.Overlap

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


lemma block_root (a b c : ℂ) (hS : a+c+2*b=0) (hQ : a*c+b^2=0)
    (hne : a≠0 ∨ b≠0 ∨ c≠0) :
    b≠0 ∧ ∃ h : ℂ, h^2=2 ∧ a=b*(h-1) ∧ c=b*(-h-1) := by
  have hb : b≠0 := by
    intro hb
    have ha2 : a^2=0 := by linear_combination a*hS-hQ+(b-2*a)*hb
    have ha := eq_zero_of_pow_eq_zero ha2
    have hc : c=0 := by linear_combination hS-ha-2*hb
    exact hne.elim (fun hn => hn ha) (fun hn => hn.elim (fun hn => hn hb) (fun hn => hn hc))
  have hmul : (a/b)*b=a := div_mul_cancel₀ a hb
  have haq : a^2+2*a*b-b^2=0 := by linear_combination a*hS-hQ
  refine ⟨hb,a/b+1,?_,?_,?_⟩
  · apply mul_right_cancel₀ (pow_ne_zero 2 hb)
    linear_combination (a/b*b+a+2*b)*hmul+haq
  · linear_combination -hmul
  · linear_combination hS+hmul

lemma roots_overlap_impossible (h k : ℂ) (hh : h^2=2) (hk : k^2=2)
    (hp : 1-h-k-h*k=0) : False := by
  have hl : 2*h-k-3=0 := by linear_combination (h-1)*hp+(1+k)*hh
  have ht : h-(5/4:ℂ)=0 := by
    linear_combination (1/3:ℂ)*hh-(1/12:ℂ)*hk-(1/12:ℂ)*(2*h+k-3)*hl
  have hbad : (7:ℂ)=0 := by linear_combination (16*h+20)*ht-16*hh
  norm_num at hbad

def topBlock (a b c : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![a,b,0,0],![b,c,0,0],![0,0,0,0],![0,0,0,0]]

def sideBlock (a b c : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![a,0,b,0],![0,0,0,0],![b,0,c,0],![0,0,0,0]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma normalized_overlap_impossible (h k : ℂ) (hh : h^2=2) (hk : k^2=2)
    (hp : ∀ U V : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*topBlock (h-1) 1 (-h-1) r s+V*sideBlock (k-1) 1 (-k-1) r s)=24) : False := by
  have h1 := hp 1 1
  have hm1 := hp (-1) (-1)
  have h2 := hp 2 2
  have hm2 := hp (-2) (-2)
  simp [perm4,Matrix.of_apply,topBlock,sideBlock] at h1 hm1 h2 hm2
  apply roots_overlap_impossible h k hh hk
  linear_combination (1/3:ℂ)*(h1+hm1)-(1/48:ℂ)*(h2+hm2)+hh+hk

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma overlap_blocks_impossible (a b c d e f : ℂ)
    (hA : a≠0 ∨ b≠0 ∨ c≠0) (hB : d≠0 ∨ e≠0 ∨ f≠0)
    (hp : ∀ U V : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*topBlock a b c r s+V*sideBlock d e f r s)=24) : False := by
  have hA1 := hp 1 0
  have hAm := hp (-1) 0
  have hB1 := hp 0 1
  have hBm := hp 0 (-1)
  simp [perm4,Matrix.of_apply,topBlock,sideBlock] at hA1 hAm hB1 hBm
  have hAS : a+c+2*b=0 := by linear_combination (1/12:ℂ)*(hA1-hAm)
  have hAQ : a*c+b^2=0 := by linear_combination (1/4:ℂ)*(hA1+hAm)
  have hBS : d+f+2*e=0 := by linear_combination (1/12:ℂ)*(hB1-hBm)
  have hBQ : d*f+e^2=0 := by linear_combination (1/4:ℂ)*(hB1+hBm)
  obtain ⟨hb,h,hh,ha,hc⟩ := block_root a b c hAS hAQ hA
  obtain ⟨he,k,hk,hd,hf⟩ := block_root d e f hBS hBQ hB
  apply normalized_overlap_impossible h k hh hk
  intro U V
  have hp0 := hp (U/b) (V/e)
  have heqA : topBlock a b c=Matrix.of (fun (r s : Fin 4) => b*topBlock (h-1) 1 (-h-1) r s) := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [topBlock,ha,hc] <;> ring_nf <;> simp
  have heqB : sideBlock d e f=Matrix.of (fun (r s : Fin 4) => e*sideBlock (k-1) 1 (-k-1) r s) := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [sideBlock,hd,hf] <;> ring_nf <;> simp
  rw [heqA,heqB] at hp0
  simpa only [Matrix.of_apply,← mul_assoc,div_mul_cancel₀ U hb,div_mul_cancel₀ V he] using hp0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma overlap_zero_rows_impossible (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hsA : ∀ r s : Fin 4, A r s=A s r)
    (hsB : ∀ r s : Fin 4, B r s=B s r)
    (hA2 : ∀ j : Fin 4, A 2 j=0) (hA3 : ∀ j : Fin 4, A 3 j=0)
    (hB1 : ∀ j : Fin 4, B 1 j=0) (hB3 : ∀ j : Fin 4, B 3 j=0)
    (hA : A≠0) (hB : B≠0)
    (hp : ∀ U V : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*A r s+V*B r s)=24) : False := by
  have heqA : A=topBlock (A 0 0) (A 0 1) (A 1 1) := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [topBlock,hA2,hA3,hsA 0 2,hsA 0 3,hsA 1 2,hsA 1 3,hsA 1 0]
  have heqB : B=sideBlock (B 0 0) (B 0 2) (B 2 2) := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [sideBlock,hB1,hB3,hsB 0 1,hsB 0 3,hsB 2 1,hsB 2 3,hsB 2 0]
  have hAne : A 0 0≠0 ∨ A 0 1≠0 ∨ A 1 1≠0 := by
    by_contra hn
    have ha : A 0 0=0 := Classical.not_not.mp (fun h => hn (Or.inl h))
    have hb : A 0 1=0 := Classical.not_not.mp (fun h => hn (Or.inr (Or.inl h)))
    have hc : A 1 1=0 := Classical.not_not.mp (fun h => hn (Or.inr (Or.inr h)))
    apply hA
    apply heqA.trans
    ext r s
    fin_cases r <;> fin_cases s <;> simp [topBlock,ha,hb,hc]
  have hBne : B 0 0≠0 ∨ B 0 2≠0 ∨ B 2 2≠0 := by
    by_contra hn
    have ha : B 0 0=0 := Classical.not_not.mp (fun h => hn (Or.inl h))
    have hb : B 0 2=0 := Classical.not_not.mp (fun h => hn (Or.inr (Or.inl h)))
    have hc : B 2 2=0 := Classical.not_not.mp (fun h => hn (Or.inr (Or.inr h)))
    apply hB
    apply heqB.trans
    ext r s
    fin_cases r <;> fin_cases s <;> simp [sideBlock,ha,hb,hc]
  apply overlap_blocks_impossible (A 0 0) (A 0 1) (A 1 1)
    (B 0 0) (B 0 2) (B 2 2) hAne hBne
  intro U V
  have hc := hp U V
  rw [heqA,heqB] at hc
  exact hc

lemma submatrix_ne_zero (M : Matrix (Fin 4) (Fin 4) ℂ)
    (hM : M≠0) (σ : Equiv.Perm (Fin 4)) : M.submatrix σ σ≠0 := by
  intro hz
  apply hM
  ext r s
  have he := congrArg (fun N : Matrix (Fin 4) (Fin 4) ℂ => N (σ.symm r) (σ.symm s)) hz
  simpa only [Matrix.submatrix_apply,Equiv.apply_symm_apply,Matrix.zero_apply] using he

lemma permanent_pair_reindex (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hp : ∀ U V : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*A r s+V*B r s)=24) (σ : Equiv.Perm (Fin 4)) :
    ∀ U V : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*(A.submatrix σ σ) r s+V*(B.submatrix σ σ) r s)=24 := by
  intro U V
  let M : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun r s => (1 : ℂ)+U*A r s+V*B r s
  change Matrix.permanent (M.submatrix σ σ)=24
  have he : Matrix.permanent (M.submatrix σ σ)=Matrix.permanent M := by
    change Matrix.permanent ((M.submatrix σ id).submatrix id σ)=Matrix.permanent M
    rw [Matrix.permanent_permute_rows,Matrix.permanent_permute_cols]
  exact he.trans (hp U V)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma three_collinear_leaf_rows (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hsA : ∀ r s : Fin 4, A r s=A s r)
    (hsB : ∀ r s : Fin 4, B r s=B s r)
    (hA0 : ∀ j : Fin 4, A 0 j=0) (hB1 : ∀ j : Fin 4, B 1 j=0)
    (hAB2 : ∀ j : Fin 4, A 2 j+B 2 j=0)
    (hA : A≠0) (hB : B≠0) (hAB : A+B≠0)
    (hp : ∀ U V : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*A r s+V*B r s)=24) :
    (∃ j : Fin 4, B 0 j≠0) ∧ (∃ j : Fin 4, A 1 j≠0) ∧ (∃ j : Fin 4, A 2 j≠0) := by
  have hsAB (r s : Fin 4) : (A+B) r s=(A+B) s r :=
    congrArg₂ (·+·) (hsA r s) (hsB r s)
  have hpAS (U V : ℂ) : Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*A r s+V*(A+B) r s)=24 := by
    convert hp (U+V) V using 1
    congr 1
    ext r s
    simp only [Matrix.of_apply,Matrix.add_apply]
    ring
  have hpBS (U V : ℂ) : Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*B r s+V*(A+B) r s)=24 := by
    convert hp V (U+V) using 1
    congr 1
    ext r s
    simp only [Matrix.of_apply,Matrix.add_apply]
    ring
  constructor
  · by_contra hn
    have hB0 (j : Fin 4) : B 0 j=0 := Classical.not_not.mp ((not_exists.mp hn) j)
    have hS0 (j : Fin 4) : (A+B) 0 j=0 := by simp [Matrix.add_apply,hA0,hB0]
    let σ : Equiv.Perm (Fin 4) :=
      { toFun := ![3,2,1,0], invFun := ![3,2,1,0], left_inv := by decide, right_inv := by decide }
    apply overlap_zero_rows_impossible (B.submatrix σ σ) ((A+B).submatrix σ σ)
      (fun r s => hsB (σ r) (σ s)) (fun r s => hsAB (σ r) (σ s))
      _ _ _ _ (submatrix_ne_zero B hB σ) (submatrix_ne_zero (A+B) hAB σ)
      (permanent_pair_reindex B (A+B) hpBS σ)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hB1 (σ j)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hB0 (σ j)
    · intro j
      simpa [σ,Matrix.submatrix_apply,Matrix.add_apply] using hAB2 (σ j)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hS0 (σ j)
  constructor
  · by_contra hn
    have hA1 (j : Fin 4) : A 1 j=0 := Classical.not_not.mp ((not_exists.mp hn) j)
    have hS1 (j : Fin 4) : (A+B) 1 j=0 := by simp [Matrix.add_apply,hA1,hB1]
    let σ : Equiv.Perm (Fin 4) :=
      { toFun := ![3,2,0,1], invFun := ![2,3,1,0], left_inv := by decide, right_inv := by decide }
    apply overlap_zero_rows_impossible (A.submatrix σ σ) ((A+B).submatrix σ σ)
      (fun r s => hsA (σ r) (σ s)) (fun r s => hsAB (σ r) (σ s))
      _ _ _ _ (submatrix_ne_zero A hA σ) (submatrix_ne_zero (A+B) hAB σ)
      (permanent_pair_reindex A (A+B) hpAS σ)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hA0 (σ j)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hA1 (σ j)
    · intro j
      simpa [σ,Matrix.submatrix_apply,Matrix.add_apply] using hAB2 (σ j)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hS1 (σ j)
  · by_contra hn
    have hA2 (j : Fin 4) : A 2 j=0 := Classical.not_not.mp ((not_exists.mp hn) j)
    have hB2 (j : Fin 4) : B 2 j=0 := by simpa only [hA2,zero_add] using hAB2 j
    let σ : Equiv.Perm (Fin 4) :=
      { toFun := ![3,1,0,2], invFun := ![2,1,3,0], left_inv := by decide, right_inv := by decide }
    apply overlap_zero_rows_impossible (A.submatrix σ σ) (B.submatrix σ σ)
      (fun r s => hsA (σ r) (σ s)) (fun r s => hsB (σ r) (σ s))
      _ _ _ _ (submatrix_ne_zero A hA σ) (submatrix_ne_zero B hB σ)
      (permanent_pair_reindex A B hp σ)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hA0 (σ j)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hA2 (σ j)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hB1 (σ j)
    · intro j
      simpa [σ,Matrix.submatrix_apply] using hB2 (σ j)

end PEqualNP.Outside.L_gct_231.Overlap

namespace PEqualNP.Outside.L_gct_231.GlobalCover

open RowKernel Cover

lemma perm_first_three (i j k : Fin 4) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0=i ∧ σ 1=j ∧ σ 2=k := by
  obtain ⟨τ,hτ0,hτ1⟩ := perm_first_two i j hij
  have hk0 : τ.symm k≠0 := by
    intro hh
    have he := congrArg τ hh
    rw [Equiv.apply_symm_apply,hτ0] at he
    exact hik he.symm
  have hk1 : τ.symm k≠1 := by
    intro hh
    have he := congrArg τ hh
    rw [Equiv.apply_symm_apply,hτ1] at he
    exact hjk he.symm
  let σ : Equiv.Perm (Fin 4) := (Equiv.swap 2 (τ.symm k)).trans τ
  refine ⟨σ,?_,?_,?_⟩
  · change τ (Equiv.swap 2 (τ.symm k) 0)=i
    have hh : Equiv.swap 2 (τ.symm k) 0=0 := by simp [Equiv.swap_apply_def,Ne.symm hk0]
    rw [hh,hτ0]
  · change τ (Equiv.swap 2 (τ.symm k) 1)=j
    have hh : Equiv.swap 2 (τ.symm k) 1=1 := by simp [Equiv.swap_apply_def,Ne.symm hk1]
    rw [hh,hτ1]
  · change τ (Equiv.swap 2 (τ.symm k) 2)=k
    rw [Equiv.swap_apply_left,Equiv.apply_symm_apply]

lemma last_dependent_triple_coefficients (A B D : Ambient)
    (hA : A≠0) (hB : B≠0)
    (hAB : LinearIndependent ℂ ![A,B])
    (hAD : LinearIndependent ℂ ![A,D])
    (hBD : LinearIndependent ℂ ![B,D])
    (hdep : ¬LinearIndependent ℂ ![A,B,D]) :
    ∃ a b : ℂ, a≠0 ∧ b≠0 ∧ D=a • A+b • B := by
  have hrange : Set.range (![A,B] : Fin 2 → Ambient)=({A,B} : Set Ambient) := by
    ext x
    simp [eq_comm,or_comm]
  have hspan : D∈Submodule.span ℂ ({A,B} : Set Ambient) := by
    by_contra hn
    apply hdep
    have hh : LinearIndependent ℂ (Fin.snoc (![A,B] : Fin 2 → Ambient) D) :=
      linearIndependent_finSnoc.mpr ⟨hAB,by simpa only [hrange] using hn⟩
    have heq : Fin.snoc (![A,B] : Fin 2 → Ambient) D=(![A,B,D] : Fin 3 → Ambient) := by
      funext q
      fin_cases q <;> rfl
    simpa only [heq] using hh
  apply Projective.collinear_nonzero_coefficients A B D hspan
  · intro hm
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hm
    exact (LinearIndependent.pair_iff' hA).mp hAD a ha
  · intro hm
    obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp hm
    exact (LinearIndependent.pair_iff' hB).mp hBD b hb

lemma permMatrix_add (σ : Equiv.Perm (Fin 4)) (A B : Ambient) :
    permMatrix σ (A+B)=permMatrix σ A+permMatrix σ B := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma collinear_collision_impossible (L : Submodule ℂ Ambient)
    (h3 : Module.finrank ℂ L=3) (hL : Level L)
    (A : Fin 4 → Ambient) (hA : Directions L A)
    (i j k : Fin 4) (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (hijL : LinearIndependent ℂ ![A i,A j])
    (hikL : LinearIndependent ℂ ![A i,A k])
    (hjkL : LinearIndependent ℂ ![A j,A k])
    (hdep : ¬LinearIndependent ℂ ![A i,A j,A k]) : False := by
  obtain ⟨a,b,ha,hb,hD⟩ := last_dependent_triple_coefficients (A i) (A j) (A k)
    (hA i).2.1 (hA j).2.1 hijL hikL hjkL hdep
  obtain ⟨σ,hσ0,hσ1,hσ2⟩ := perm_first_three i j k hij hik hjk
  let U : Ambient := a • A i
  let V : Ambient := b • A j
  have hU : U∈L := L.smul_mem a (hA i).1
  have hV : V∈L := L.smul_mem b (hA j).1
  have hUne : U≠0 := smul_ne_zero ha (hA i).2.1
  have hVne : V≠0 := smul_ne_zero hb (hA j).2.1
  have hUV : U+V=A k := hD.symm
  have hM0 (q : Fin 4) : permMatrix σ U 0 q=0 := by
    change a*A i (σ 0,σ q)=0
    rw [hσ0,(hA i).2.2,mul_zero]
  have hN1 (q : Fin 4) : permMatrix σ V 1 q=0 := by
    change b*A j (σ 1,σ q)=0
    rw [hσ1,(hA j).2.2,mul_zero]
  have hMN : permMatrix σ U+permMatrix σ V=permMatrix σ (A k) := by
    rw [←permMatrix_add,hUV]
  have hMN2 (q : Fin 4) : permMatrix σ U 2 q+permMatrix σ V 2 q=0 := by
    have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 2 q) hMN
    change permMatrix σ U 2 q+permMatrix σ V 2 q=permMatrix σ (A k) 2 q at he
    rw [he]
    change A k (σ 2,σ q)=0
    rw [hσ2]
    exact (hA k).2.2 (σ q)
  have hMNne : permMatrix σ U+permMatrix σ V≠0 := by
    rw [hMN]
    exact permMatrix_ne_zero σ _ (hA k).2.1
  have hsU := permMatrix_symmetric L hL σ U hU
  have hsV := permMatrix_symmetric L hL σ V hV
  have hpUV (x y : ℂ) : Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1:ℂ)+x*permMatrix σ U r s+y*permMatrix σ V r s)=24 := by
    simpa only [zero_mul,add_zero] using level_three_reindex L hL σ U V U hU hV hU x y 0
  obtain ⟨hleaf0,hleaf1,hleaf2⟩ := Overlap.three_collinear_leaf_rows
    (permMatrix σ U) (permMatrix σ V) hsU hsV hM0 hN1 hMN2
    (permMatrix_ne_zero σ U hUne) (permMatrix_ne_zero σ V hVne) hMNne hpUV
  have hspan (T : Ambient) (hT : T∈L) : ∃ p q : ℂ, T=p • U+q • V := by
    obtain ⟨p,q,heq⟩ := ArrowheadMatrix.three_collinear_zero_rows_third_in_span
      (permMatrix σ U) (permMatrix σ V) (permMatrix σ T) hsU hsV
      (permMatrix_symmetric L hL σ T hT) hM0 hN1 hMN2
      (level_three_reindex L hL σ U V T hU hV hT) hleaf0 hleaf1 hleaf2
    refine ⟨p,q,?_⟩
    funext x
    rcases x with ⟨r,s⟩
    have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M (σ.symm r) (σ.symm s)) heq
    simpa only [permMatrix,Matrix.of_apply,Equiv.apply_symm_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using he
  exact Projective.no_three_dimensional_pair_span L h3 U V hspan

lemma refutation_of_three_geometric_obstructions
    (hfull : ∀ (L : Submodule ℂ Ambient), Module.finrank ℂ L=3 → Level L →
      ∀ i : Fin 4, Function.Surjective (rowDifference L i) → False)
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
  apply conditional_refutation hfull _ _ _ hrepeated hframe
  · intro L h3 hL A hA i j k hij hik hjk hj hk
    exact triple_collision_impossible L hL A hA i j k hij hik hjk hj hk
  · intro L h3 hL A hA σ h01 h23
    exact double_collision_impossible L h3 hL A hA σ h01 h23
  · intro L h3 hL A hA i j k hij hik hjk hijL hikL hjkL hdep
    exact collinear_collision_impossible L h3 hL A hA i j k hij hik hjk hijL hikL hjkL hdep

end PEqualNP.Outside.L_gct_231.GlobalCover
