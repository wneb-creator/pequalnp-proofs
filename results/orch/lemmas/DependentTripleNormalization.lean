import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation

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
