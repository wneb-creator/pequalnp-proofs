import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

def hadamardSigns : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,1,1; 1,1,-1,-1; 1,-1,1,-1; 1,-1,-1,1]

noncomputable def hadamardTransform :
    (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun V p := (∑ i : Fin 4, ∑ j : Fin 4,
    hadamardSigns p.1 i * V (i,j) * hadamardSigns p.2 j) / 4
  map_add' V W := by
    funext p
    simp [Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib,add_div]
  map_smul' z V := by
    funext p
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp [hadamardSigns,Fin.sum_univ_succ]
    ring

set_option maxHeartbeats 1600000 in
lemma hadamardTransform_involution (V : Fin 4 × Fin 4 → ℂ) :
    hadamardTransform (hadamardTransform V)=V := by
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [hadamardTransform,hadamardSigns,Fin.sum_univ_succ] <;> ring

lemma hadamardTransform_symmetric (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j)=V (j,i)) :
    ∀ i j : Fin 4, hadamardTransform V (i,j)=hadamardTransform V (j,i) := by
  intro i j
  change (∑ a : Fin 4, ∑ b : Fin 4,
    hadamardSigns i a * V (a,b) * hadamardSigns j b) / 4 =
    (∑ a : Fin 4, ∑ b : Fin 4,
      hadamardSigns j a * V (a,b) * hadamardSigns i b) / 4
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [hs b a]
  ring

lemma hadamardTransform_zero_zero (V : Fin 4 × Fin 4 → ℂ) :
    hadamardTransform V (0,0)=(∑ i : Fin 4, ∑ j : Fin 4, V (i,j))/4 := by
  simp [hadamardTransform,hadamardSigns,Fin.sum_univ_succ]

lemma hadamardTransform_trace (V : Fin 4 × Fin 4 → ℂ) :
    (∑ i : Fin 4, hadamardTransform V (i,i))=∑ i : Fin 4, V (i,i) := by
  simp [hadamardTransform,hadamardSigns,Fin.sum_univ_succ]
  ring

noncomputable def hadamardB : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun V := ![hadamardTransform V (1,1),hadamardTransform V (2,2),hadamardTransform V (3,3)]
  map_add' := by intros; ext i; fin_cases i <;> simp
  map_smul' := by intros; ext i; fin_cases i <;> simp

noncomputable def hadamardP : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun V := ![3*hadamardTransform V (0,1)+hadamardTransform V (2,3),
    3*hadamardTransform V (0,2)+hadamardTransform V (1,3),
    3*hadamardTransform V (0,3)+hadamardTransform V (1,2)]
  map_add' := by intros; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intros; ext i; fin_cases i <;> simp <;> ring

noncomputable def hadamardD : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun V := ![hadamardTransform V (0,1)+hadamardTransform V (2,3),
    hadamardTransform V (0,2)+hadamardTransform V (1,3),
    hadamardTransform V (0,3)+hadamardTransform V (1,2)]
  map_add' := by intros; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intros; ext i; fin_cases i <;> simp <;> ring

noncomputable def hadamardCoordinateMatrix (B P D : Fin 3 → ℂ) : Fin 4 × Fin 4 → ℂ :=
  fun p => (!![0,(P 0-D 0)/2,(P 1-D 1)/2,(P 2-D 2)/2;
    (P 0-D 0)/2,B 0,(3*D 2-P 2)/2,(3*D 1-P 1)/2;
    (P 1-D 1)/2,(3*D 2-P 2)/2,B 1,(3*D 0-P 0)/2;
    (P 2-D 2)/2,(3*D 1-P 1)/2,(3*D 0-P 0)/2,B 2] : Matrix (Fin 4) (Fin 4) ℂ) p.1 p.2

noncomputable def hadamardReconstruct (B P D : Fin 3 → ℂ) : Fin 4 × Fin 4 → ℂ :=
  hadamardTransform (hadamardCoordinateMatrix B P D)

lemma hadamardCoordinateMatrix_coordinates (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (ht : (∑ i : Fin 4, ∑ j : Fin 4, V (i,j))=0) :
    hadamardCoordinateMatrix (hadamardB V) (hadamardP V) (hadamardD V)=hadamardTransform V := by
  have hsym := hadamardTransform_symmetric V hs
  have h00 : hadamardTransform V (0,0)=0 := by rw [hadamardTransform_zero_zero,ht]; norm_num
  have h10 := hsym 1 0
  have h20 := hsym 2 0
  have h30 := hsym 3 0
  have h21 := hsym 2 1
  have h31 := hsym 3 1
  have h32 := hsym 3 2
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [hadamardCoordinateMatrix,hadamardB,hadamardP,hadamardD,
      h00,h10,h20,h30,h21,h31,h32] <;> ring

lemma hadamard_reconstruction (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (ht : (∑ i : Fin 4, ∑ j : Fin 4, V (i,j))=0) :
    hadamardReconstruct (hadamardB V) (hadamardP V) (hadamardD V)=V := by
  unfold hadamardReconstruct
  rw [hadamardCoordinateMatrix_coordinates V hs ht,hadamardTransform_involution]

lemma hadamard_trace_coordinates (V : Fin 4 × Fin 4 → ℂ)
    (ht : (∑ i : Fin 4, ∑ j : Fin 4, V (i,j))=0) :
    (∑ i : Fin 3, hadamardB V i)=∑ i : Fin 4, V (i,i) := by
  have h00 : hadamardTransform V (0,0)=0 := by rw [hadamardTransform_zero_zero,ht]; norm_num
  have hh := hadamardTransform_trace V
  simpa [hadamardB,Fin.sum_univ_succ,h00] using hh

lemma hadamard_reconstruct_diagonal (B P D : Fin 3 → ℂ) :
    (fun i : Fin 4 => hadamardReconstruct B P D (i,i)) =
      ![(B 0+B 1+B 2)/4+(D 0+D 1+D 2)/2,
        (B 0+B 1+B 2)/4+(D 0-D 1-D 2)/2,
        (B 0+B 1+B 2)/4+(-D 0+D 1-D 2)/2,
        (B 0+B 1+B 2)/4+(-D 0-D 1+D 2)/2] := by
  funext i
  fin_cases i <;>
    simp [hadamardReconstruct,hadamardTransform,hadamardCoordinateMatrix,
      hadamardSigns,Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 1600000 in
lemma permanent_level_entry_sum_zero (V : Fin 4 × Fin 4 → ℂ)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+z*V (i,j))=24) :
    (∑ i : Fin 4, ∑ j : Fin 4, V (i,j))=0 := by
  have h1 := hp 1
  have hn1 := hp (-1)
  have h2 := hp 2
  have hn2 := hp (-2)
  rw [permanent_four] at h1 hn1 h2 hn2
  simp only [Matrix.of_apply] at h1 hn1 h2 hn2
  simp [Fin.sum_univ_succ]
  linear_combination h1/9-hn1/9-h2/72+hn2/72

lemma level_flat_entry_sum_zero
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24)
    (V : Fin 4 × Fin 4 → ℂ) (hV : V ∈ L) :
    (∑ i : Fin 4, ∑ j : Fin 4, V (i,j))=0 := by
  apply permanent_level_entry_sum_zero V
  intro z
  simpa only [Pi.smul_apply,smul_eq_mul] using hp _ (L.smul_mem z hV)

end PEqualNP.Outside.L_gct_231
