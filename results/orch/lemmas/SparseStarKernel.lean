import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace PEqualNP.Outside.L_gct_231_aux.SparseStar
def sparseStar : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0,1,-1,0],![1,0,0,0],![-1,0,0,0],![0,0,0,0]]

end PEqualNP.Outside.L_gct_231_aux.SparseStar

namespace PEqualNP.Outside.L_gct_231_aux.SparseStar

lemma ternary_range_le_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : V →ₗ[ℂ] (Fin 3 → ℂ)) (d : ℂ)
    (hQ : ∀ T, (F T 0)^2-6*(F T 2)*(F T 1)+2*d^2*(F T 2)^2=0) :
    Module.finrank ℂ F.range≤1 := by
  classical
  have hP (T U : V) : F T 0*F U 0-
      3*(F T 2*F U 1+F T 1*F U 2)+2*d^2*F T 2*F U 2=0 := by
    have hT := hQ T
    have hU := hQ U
    have hTU := hQ (T+U)
    simp only [map_add,Pi.add_apply] at hTU
    linear_combination (1/2:ℂ)*(hTU-hT-hU)
  have hminor (T U : V) : F T 0*F U 2-F U 0*F T 2=0 := by
    have hT := hQ T
    have hU := hQ U
    have hTU := hP T U
    have hh : (F T 0*F U 2-F U 0*F T 2)^2=0 := by
      linear_combination (F U 2)^2*hT+(F T 2)^2*hU-2*(F T 2)*(F U 2)*hTU
    exact eq_zero_of_pow_eq_zero hh
  by_cases hex : ∃ T, F T 2≠0
  · obtain ⟨T,hT⟩ := hex
    have hmem (U : V) : F U∈Submodule.span ℂ ({F T} : Set (Fin 3 → ℂ)) := by
      have hm := hminor T U
      have hp := hP T U
      have hq := hQ T
      have hy0 : (3*F T 2)*(F T 1*F U 2-F U 1*F T 2)=0 := by
        linear_combination F T 2*hp-F U 2*hq+F T 0*hm
      have hy : F T 1*F U 2-F U 1*F T 2=0 :=
        (mul_eq_zero.mp hy0).resolve_left (mul_ne_zero (by norm_num) hT)
      apply Submodule.mem_span_singleton.mpr
      refine ⟨F U 2/F T 2,?_⟩
      funext i
      fin_cases i
      · change (F U 2/F T 2)*F T 0=F U 0
        field_simp [hT]
        linear_combination hm
      · change (F U 2/F T 2)*F T 1=F U 1
        field_simp [hT]
        linear_combination hy
      · change (F U 2/F T 2)*F T 2=F U 2
        exact div_mul_cancel₀ _ hT
    have hle : F.range≤Submodule.span ℂ ({F T} : Set (Fin 3 → ℂ)) := by
      rintro Z ⟨U,rfl⟩
      exact hmem U
    have hn : F T≠0 := by
      intro hz
      exact hT (congrFun hz 2)
    have hdim := Submodule.finrank_mono hle
    simpa only [finrank_span_singleton hn] using hdim
  · have hk (T : V) : F T 2=0 := by
      by_contra h
      exact hex ⟨T,h⟩
    have hx (T : V) : F T 0=0 := by
      have hh : (F T 0)^2=0 := by
        simpa only [hk,pow_two,mul_zero,zero_mul,add_zero,sub_zero] using hQ T
      exact eq_zero_of_pow_eq_zero hh
    let v : Fin 3 → ℂ := ![0,1,0]
    have hle : F.range≤Submodule.span ℂ ({v} : Set (Fin 3 → ℂ)) := by
      rintro Z ⟨T,rfl⟩
      apply Submodule.mem_span_singleton.mpr
      refine ⟨F T 1,?_⟩
      funext i
      fin_cases i <;> simp [v,hx,hk]
    have hn : v≠0 := by
      intro hz
      have he := congrFun hz 1
      norm_num [v] at he
    have hdim := Submodule.finrank_mono hle
    simpa only [finrank_span_singleton hn] using hdim

lemma injective_surjective_two {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (E : V →ₗ[ℂ] (Fin 2 → ℂ))
    (hD : Module.finrank ℂ V=2) (hI : Function.Injective E) : Function.Surjective E := by
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℂ)
    (V := V) (V₂ := Fin 2 → ℂ) (f := E)
    (by simpa only [Module.finrank_fin_fun] using hD)).mp hI

set_option maxHeartbeats 200000 in
set_option maxRecDepth 100000 in
lemma sparse_star_mem_of_small_quotient
    (L : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ)) (hL : Module.finrank ℂ L=3)
    (F : L →ₗ[ℂ] (Fin 3 → ℂ)) (hF : Module.finrank ℂ F.range≤1)
    (hk : ∀ T : L, F T=0 → (T : Matrix (Fin 4) (Fin 4) ℂ)=
      ![![0,T.val 0 1,T.val 0 2,-T.val 0 1-T.val 0 2],
        ![T.val 0 1,0,0,0],![T.val 0 2,0,0,0],![-T.val 0 1-T.val 0 2,0,0,0]]) :
    sparseStar∈L := by
  classical
  let E : F.ker →ₗ[ℂ] (Fin 2 → ℂ) :=
    { toFun := fun T => ![T.val.val 0 1,T.val.val 0 2]
      map_add' := by intro T U; funext i; fin_cases i <;> rfl
      map_smul' := by intro c T; funext i; fin_cases i <;> rfl }
  have hEi : Function.Injective E := by
    intro T U he
    have h0 : T.val.val 0 1=U.val.val 0 1 := congrFun he 0
    have h1 : T.val.val 0 2=U.val.val 0 2 := congrFun he 1
    apply Subtype.ext
    apply Subtype.ext
    rw [hk T.val (LinearMap.mem_ker.mp T.property),hk U.val (LinearMap.mem_ker.mp U.property)]
    rw [h0,h1]
  have hK := F.finrank_range_add_finrank_ker
  rw [hL] at hK
  have hEle := LinearMap.finrank_le_finrank_of_injective (R := ℂ) (f := E) hEi
  rw [Module.finrank_fin_fun] at hEle
  have hdim : Module.finrank ℂ F.ker=2 := by omega
  have hEs : Function.Surjective E := injective_surjective_two (V := F.ker) E hdim hEi
  obtain ⟨T,hT⟩ := hEs ![1,-1]
  have h0 : T.val.val 0 1=1 := congrFun hT 0
  have h1 : T.val.val 0 2= -1 := congrFun hT 1
  have he : T.val.val=sparseStar := by
    rw [hk T.val (LinearMap.mem_ker.mp T.property)]
    simp [h0,h1,sparseStar] <;> rfl
  rw [←he]
  exact T.val.property

end PEqualNP.Outside.L_gct_231_aux.SparseStar
