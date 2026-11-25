import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

namespace PEqualNP.Outside.L_gct_231_aux.PlaneOperatorOverlap

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem overlap_of_dependent (O : V →ₗ[ℂ] V) (B C : V)
    (hBC : LinearIndependent ℂ ![B,C])
    (hdep : ¬ LinearIndependent ℂ ![B,C,O B,O C]) :
    ∃ v : V, v ≠ 0 ∧ v ∈ Submodule.span ℂ ({B,C} : Set V) ∧
      O v ∈ Submodule.span ℂ ({B,C} : Set V) := by
  classical
  rw [Fintype.linearIndependent_iff] at hdep
  push_neg at hdep
  obtain ⟨g,hg,i,hi⟩ := hdep
  have hrel : g 0 • B + g 1 • C + (g 2 • O B + g 3 • O C) = 0 := by
    simpa [Fin.sum_univ_four,add_assoc] using hg
  let v : V := g 2 • B + g 3 • C
  have hv : v ≠ 0 := by
    intro hz
    have hz23 : ∑ j : Fin 2, (![g 2,g 3] : Fin 2 → ℂ) j •
        (![B,C] : Fin 2 → V) j = 0 := by
      simpa [Fin.sum_univ_two,v] using hz
    have h2 : g 2 = 0 := by
      simpa using Fintype.linearIndependent_iff.mp hBC (![g 2,g 3]) hz23 0
    have h3 : g 3 = 0 := by
      simpa using Fintype.linearIndependent_iff.mp hBC (![g 2,g 3]) hz23 1
    have hz01 : ∑ j : Fin 2, (![g 0,g 1] : Fin 2 → ℂ) j •
        (![B,C] : Fin 2 → V) j = 0 := by
      simpa [Fin.sum_univ_two,h2,h3] using hrel
    have h0 : g 0 = 0 := by
      simpa using Fintype.linearIndependent_iff.mp hBC (![g 0,g 1]) hz01 0
    have h1 : g 1 = 0 := by
      simpa using Fintype.linearIndependent_iff.mp hBC (![g 0,g 1]) hz01 1
    apply hi
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hvspan : v ∈ Submodule.span ℂ ({B,C} : Set V) :=
    Submodule.mem_span_pair.mpr ⟨g 2,g 3,rfl⟩
  have hsum : g 0 • B + g 1 • C ∈ Submodule.span ℂ ({B,C} : Set V) :=
    Submodule.mem_span_pair.mpr ⟨g 0,g 1,rfl⟩
  have hmap : O v = -(g 0 • B + g 1 • C) := by
    have hz : g 0 • B + g 1 • C + O v = 0 := by
      simpa [v,map_add,map_smul,add_assoc] using hrel
    calc
      O v = (g 0 • B + g 1 • C + O v) - (g 0 • B + g 1 • C) := by abel
      _ = -(g 0 • B + g 1 • C) := by rw [hz,zero_sub]
  refine ⟨v,hv,hvspan,?_⟩
  rw [hmap]
  exact Submodule.neg_mem _ hsum

theorem overlap_of_finrank_le_three [FiniteDimensional ℂ V]
    (O : V →ₗ[ℂ] V) (B C : V) (N : Submodule ℂ V)
    (hBC : LinearIndependent ℂ ![B,C])
    (hB : B ∈ N) (hC : C ∈ N) (hOB : O B ∈ N) (hOC : O C ∈ N)
    (hN : Module.finrank ℂ N ≤ 3) :
    ∃ v : V, v ≠ 0 ∧ v ∈ Submodule.span ℂ ({B,C} : Set V) ∧
      O v ∈ Submodule.span ℂ ({B,C} : Set V) := by
  apply overlap_of_dependent O B C hBC
  intro hli
  let vN : Fin 4 → N := ![⟨B,hB⟩,⟨C,hC⟩,⟨O B,hOB⟩,⟨O C,hOC⟩]
  have heq : N.subtype ∘ vN = (![B,C,O B,O C] : Fin 4 → V) := by
    funext i
    fin_cases i <;> rfl
  have hliN : LinearIndependent ℂ vN :=
    LinearIndependent.of_comp N.subtype (by rw [heq]; exact hli)
  have hfour : 4 ≤ Module.finrank ℂ N := by
    simpa only [Fintype.card_fin] using hliN.fintype_card_le_finrank
  exact (by norm_num : ¬ (4 : ℕ) ≤ 3) (hfour.trans hN)

end PEqualNP.Outside.L_gct_231_aux.PlaneOperatorOverlap
