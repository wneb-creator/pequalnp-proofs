import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

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
