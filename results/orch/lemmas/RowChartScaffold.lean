import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.NormNum

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
