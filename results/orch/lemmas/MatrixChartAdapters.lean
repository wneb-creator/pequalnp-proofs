import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin



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


namespace PEqualNP.Outside.L_gct_231.Projective

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

lemma dependent_triple_nonzero_coefficients (A B D : V)
    (hAB : LinearIndependent ℂ ![A,B])
    (hAD : LinearIndependent ℂ ![A,D])
    (hBD : LinearIndependent ℂ ![B,D])
    (hDAB : ¬ LinearIndependent ℂ ![D,A,B]) :
    ∃ a b : ℂ, a≠0 ∧ b≠0 ∧ D=a • A+b • B := by
  classical
  have hrange : Set.range (![A,B] : Fin 2 → V)=({A,B} : Set V) := by
    ext x
    simp [eq_comm,or_comm]
  have hspan : D ∈ Submodule.span ℂ ({A,B} : Set V) := by
    by_contra hn
    apply hDAB
    apply linearIndependent_finCons.mpr
    exact ⟨hAB,by simpa only [hrange] using hn⟩
  obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hspan
  have hA : A≠0 := LinearIndependent.ne_zero 0 hAB
  have hB : B≠0 := LinearIndependent.ne_zero 1 hAB
  refine ⟨a,b,?_,?_,he.symm⟩
  · intro ha
    have hbD : b • B=D := by simpa only [ha,zero_smul,zero_add] using he
    exact (LinearIndependent.pair_iff' hB).mp hBD b hbD
  · intro hb
    have haD : a • A=D := by simpa only [hb,zero_smul,add_zero] using he
    exact (LinearIndependent.pair_iff' hA).mp hAD a haD

lemma linearIndependent_nonzero_scaling {ι : Type*} [Fintype ι]
    (v : ι → V) (hv : LinearIndependent ℂ v)
    (a : ι → ℂ) (ha : ∀ i, a i≠0) :
    LinearIndependent ℂ (fun i => a i • v i) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  have hsum : ∑ j, (g j*a j) • v j=0 := by
    simpa only [smul_smul] using hg
  have hi := Fintype.linearIndependent_iff.mp hv (fun j => g j*a j) hsum i
  exact (mul_eq_zero.mp hi).resolve_right (ha i)

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

def permMatrixLinear (σ : Equiv.Perm (Fin 4)) :
    Ambient →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ where
  toFun := permMatrix σ
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

lemma permMatrixLinear_injective (σ : Equiv.Perm (Fin 4)) : Function.Injective (permMatrixLinear σ) := by
  intro T S heq
  change permMatrix σ T=permMatrix σ S at heq
  funext p
  rcases p with ⟨r,s⟩
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M (σ.symm r) (σ.symm s)) heq
  simpa only [permMatrix,Matrix.of_apply,Equiv.apply_symm_apply] using he

lemma permMatrix_independent_three (σ : Equiv.Perm (Fin 4)) (A B C : Ambient)
    (hI : LinearIndependent ℂ ![A,B,C]) :
    LinearIndependent ℂ ![permMatrix σ A,permMatrix σ B,permMatrix σ C] := by
  have hh := hI.map' (permMatrixLinear σ) (LinearMap.ker_eq_bot.mpr (permMatrixLinear_injective σ))
  convert hh using 1
  funext i
  fin_cases i <;> rfl

def RepeatedMatrixObstruction : Prop :=
  ∀ A B C : Matrix (Fin 4) (Fin 4) ℂ,
    (∀ r s : Fin 4, A r s=A s r) →
    (∀ r s : Fin 4, B r s=B s r) →
    (∀ r s : Fin 4, C r s=C s r) →
    (∀ j : Fin 4, A 0 j=0) → (∀ j : Fin 4, A 1 j=0) →
    (∀ j : Fin 4, B 2 j=0) → (∀ j : Fin 4, C 3 j=0) →
    LinearIndependent ℂ ![A,B,C] →
    (∀ U V W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1:ℂ)+U*A r s+V*B r s+W*C r s)=24) → False

def FrameMatrixObstruction : Prop :=
  ∀ A B C : Matrix (Fin 4) (Fin 4) ℂ,
    (∀ r s : Fin 4, A r s=A s r) →
    (∀ r s : Fin 4, B r s=B s r) →
    (∀ r s : Fin 4, C r s=C s r) →
    (∀ j : Fin 4, A 0 j=0) → (∀ j : Fin 4, B 1 j=0) →
    (∀ j : Fin 4, C 2 j=0) → (∀ j : Fin 4, A 3 j+B 3 j+C 3 j=0) →
    LinearIndependent ℂ ![A,B,C] →
    (∀ U V W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1:ℂ)+U*A r s+V*B r s+W*C r s)=24) → False

lemma repeated_of_matrix_obstruction (hrep : RepeatedMatrixObstruction)
    (L : Submodule ℂ Ambient) (hL : Level L)
    (D : Fin 4 → Ambient) (hD : Directions L D) (σ : Equiv.Perm (Fin 4))
    (heq : directionLine (D (σ 0))=directionLine (D (σ 1)))
    (hI : LinearIndependent ℂ ![D (σ 0),D (σ 2),D (σ 3)]) : False := by
  have hr1 := row_zero_of_same_line _ _ (σ 1) heq (hD (σ 1)).2.2
  exact hrep (permMatrix σ (D (σ 0))) (permMatrix σ (D (σ 2))) (permMatrix σ (D (σ 3)))
    (permMatrix_symmetric L hL σ _ (hD (σ 0)).1)
    (permMatrix_symmetric L hL σ _ (hD (σ 2)).1)
    (permMatrix_symmetric L hL σ _ (hD (σ 3)).1)
    (fun j => (hD (σ 0)).2.2 (σ j)) (fun j => hr1 (σ j))
    (fun j => (hD (σ 2)).2.2 (σ j)) (fun j => (hD (σ 3)).2.2 (σ j))
    (permMatrix_independent_three σ _ _ _ hI)
    (level_three_reindex L hL σ _ _ _ (hD (σ 0)).1 (hD (σ 2)).1 (hD (σ 3)).1)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma frame_of_matrix_obstruction (hframe : FrameMatrixObstruction)
    (L : Submodule ℂ Ambient) (h3 : Module.finrank ℂ L=3) (hL : Level L)
    (D : Fin 4 → Ambient) (hD : Directions L D)
    (hI : ∀ i j k : Fin 4, i≠j → i≠k → j≠k → LinearIndependent ℂ ![D i,D j,D k]) : False := by
  let d : Fin 4 → L := fun i => ⟨D i,(hD i).1⟩
  have hId (i j k : Fin 4) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
      LinearIndependent ℂ ![d i,d j,d k] := by
    apply LinearIndependent.of_comp L.subtype
    convert hI i j k hij hik hjk using 1
    funext q
    fin_cases q <;> rfl
  obtain ⟨a,b,c,ha,hb,hc,heq⟩ := Projective.frame_nonzero_coefficients h3 (d 0) (d 1) (d 2) (d 3)
    (hId 0 1 2 (by decide) (by decide) (by decide))
    (hId 3 1 2 (by decide) (by decide) (by decide))
    (hId 0 3 2 (by decide) (by decide) (by decide))
    (hId 0 1 3 (by decide) (by decide) (by decide))
  have heqD : D 3=a • D 0+b • D 1+c • D 2 := congrArg Subtype.val heq
  let U : Ambient := a • D 0
  let V : Ambient := b • D 1
  let W : Ambient := c • D 2
  have hU : U∈L := L.smul_mem a (hD 0).1
  have hV : V∈L := L.smul_mem b (hD 1).1
  have hW : W∈L := L.smul_mem c (hD 2).1
  have hIuvw : LinearIndependent ℂ ![U,V,W] := by
    have hh := Projective.linearIndependent_nonzero_scaling (![D 0,D 1,D 2] : Fin 3 → Ambient)
      (hI 0 1 2 (by decide) (by decide) (by decide)) (![a,b,c] : Fin 3 → ℂ)
      (by intro q; fin_cases q; exact ha; exact hb; exact hc)
    convert hh using 1
    funext q
    fin_cases q <;> rfl
  apply hframe (permMatrix (Equiv.refl _) U) (permMatrix (Equiv.refl _) V) (permMatrix (Equiv.refl _) W)
    (permMatrix_symmetric L hL _ U hU) (permMatrix_symmetric L hL _ V hV)
    (permMatrix_symmetric L hL _ W hW) _ _ _ _
    (permMatrix_independent_three _ U V W hIuvw) (level_three_reindex L hL _ U V W hU hV hW)
  · intro j
    change a*D 0 (0,j)=0
    rw [(hD 0).2.2,mul_zero]
  · intro j
    change b*D 1 (1,j)=0
    rw [(hD 1).2.2,mul_zero]
  · intro j
    change c*D 2 (2,j)=0
    rw [(hD 2).2.2,mul_zero]
  · intro j
    have he := congrFun heqD (3,j)
    change D 3 (3,j)=a*D 0 (3,j)+b*D 1 (3,j)+c*D 2 (3,j) at he
    change a*D 0 (3,j)+b*D 1 (3,j)+c*D 2 (3,j)=0
    rw [←he]
    exact (hD 3).2.2 j

end PEqualNP.Outside.L_gct_231.GlobalCover
