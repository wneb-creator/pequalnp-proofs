import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin

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
