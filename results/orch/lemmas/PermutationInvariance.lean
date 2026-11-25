import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

def entryPermute (σ : Equiv.Perm (Fin 4)) :
    (Fin 4 × Fin 4 → ℂ) ≃ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun V p := V (σ p.1,σ p.2)
  invFun V p := V (σ.symm p.1,σ.symm p.2)
  left_inv V := by
    funext p
    simp
  right_inv V := by
    funext p
    simp
  map_add' V W := rfl
  map_smul' c V := rfl

lemma entryPermute_apply (σ : Equiv.Perm (Fin 4))
    (V : Fin 4 × Fin 4 → ℂ) (i j : Fin 4) :
    entryPermute σ V (i,j)=V (σ i,σ j) := rfl

lemma entryPermute_symmetric (σ : Equiv.Perm (Fin 4))
    (V : Fin 4 × Fin 4 → ℂ)
    (h : ∀ i j : Fin 4, V (i,j)=V (j,i)) :
    ∀ i j : Fin 4, entryPermute σ V (i,j)=entryPermute σ V (j,i) := by
  intro i j
  exact h (σ i) (σ j)

lemma entryPermute_hollow (σ : Equiv.Perm (Fin 4))
    (V : Fin 4 × Fin 4 → ℂ) (h : ∀ i : Fin 4, V (i,i)=0) :
    ∀ i : Fin 4, entryPermute σ V (i,i)=0 := by
  intro i
  exact h (σ i)

lemma entryPermute_permanent (σ : Equiv.Perm (Fin 4))
    (V : Fin 4 × Fin 4 → ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+entryPermute σ V (i,j)) =
      Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j)) := by
  change Matrix.permanent
    (((Matrix.of fun (i j : Fin 4) => 1+V (i,j)).submatrix σ id).submatrix id σ) = _
  rw [Matrix.permanent_permute_rows,Matrix.permanent_permute_cols]

def entryPermuteSubmodule (σ : Equiv.Perm (Fin 4))
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) : Submodule ℂ (Fin 4 × Fin 4 → ℂ) :=
  L.map (entryPermute σ).toLinearMap

lemma entryPermuteSubmodule_finrank (σ : Equiv.Perm (Fin 4))
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) :
    Module.finrank ℂ (entryPermuteSubmodule σ L)=Module.finrank ℂ L := by
  exact LinearEquiv.finrank_map_eq (entryPermute σ) L

lemma entryPermute_mem_iff (σ : Equiv.Perm (Fin 4))
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (V : Fin 4 × Fin 4 → ℂ) :
    entryPermute σ V ∈ entryPermuteSubmodule σ L ↔ V ∈ L := by
  constructor
  · rintro ⟨W,hW,he⟩
    have hWV : W=V := (entryPermute σ).injective he
    simpa [hWV] using hW
  · intro hV
    exact ⟨V,hV,rfl⟩

lemma entryPermuteSubmodule_symmetric (σ : Equiv.Perm (Fin 4))
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (h : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i)) :
    ∀ V ∈ entryPermuteSubmodule σ L, ∀ i j : Fin 4, V (i,j)=V (j,i) := by
  rintro V ⟨W,hW,rfl⟩ i j
  exact h W hW (σ i) (σ j)

lemma entryPermuteSubmodule_hollow (σ : Equiv.Perm (Fin 4))
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (h : ∀ V ∈ L, ∀ i : Fin 4, V (i,i)=0) :
    ∀ V ∈ entryPermuteSubmodule σ L, ∀ i : Fin 4, V (i,i)=0 := by
  rintro V ⟨W,hW,rfl⟩ i
  exact h W hW (σ i)

lemma entryPermuteSubmodule_permanent (σ : Equiv.Perm (Fin 4))
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (h : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    ∀ V ∈ entryPermuteSubmodule σ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24 := by
  rintro V ⟨W,hW,rfl⟩
  change Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
    1+entryPermute σ W (i,j))=24
  exact (entryPermute_permanent σ W).trans (h W hW)

def hollowWittMatrix (u : Fin 5 → ℂ) : Fin 4 × Fin 4 → ℂ :=
  fun p => hollowMatrix (u 0+u 4) (u 1+u 4)
    (-u 0-u 1-u 2-u 3-5*u 4) (u 4) (u 3+u 4) (u 2+u 4) p.1 p.2

def triangleCoordinatePerm (k : Fin 4) : Equiv.Perm (Fin 4) :=
  ![1,Equiv.swap 2 3,
    Equiv.swap 1 2 * Equiv.swap 2 3,
    Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3] k

def leadingTriangleMinor (U V : Fin 4 × Fin 4 → ℂ) : ℂ :=
  (U (0,1)-U (1,2))*(V (0,2)-V (1,2))-
    (V (0,1)-V (1,2))*(U (0,2)-U (1,2))

lemma leadingTriangleMinor_permute_witt (u v : Fin 5 → ℂ) (k : Fin 4) :
    leadingTriangleMinor (entryPermute (triangleCoordinatePerm k) (hollowWittMatrix u))
      (entryPermute (triangleCoordinatePerm k) (hollowWittMatrix v)) =
      ![u 0*v 1-u 1*v 0,
        (u 0-u 3)*(-v 0-v 1-v 2-2*v 3-6*v 4)-
          (v 0-v 3)*(-u 0-u 1-u 2-2*u 3-6*u 4),
        (u 1-u 2)*(-v 0-v 1-2*v 2-v 3-6*v 4)-
          (v 1-v 2)*(-u 0-u 1-2*u 2-u 3-6*u 4),
        -(u 2*v 3-u 3*v 2)] k := by
  fin_cases k <;>
    simp [leadingTriangleMinor,entryPermute,triangleCoordinatePerm,hollowWittMatrix,
      hollowMatrix,Equiv.Perm.mul_apply,Equiv.swap_apply_def] <;>
    ring

end PEqualNP.Outside.L_gct_231
