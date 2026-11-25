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

lemma hadamardD_zero_constant_diagonal (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (ht : (∑ i : Fin 4, ∑ j : Fin 4, V (i,j))=0)
    (hD : hadamardD V=0) :
    ∀ i : Fin 4, V (i,i)=(hadamardB V 0+hadamardB V 1+hadamardB V 2)/4 := by
  have hd := hadamard_reconstruct_diagonal (hadamardB V) (hadamardP V) (hadamardD V)
  rw [hadamard_reconstruction V hs ht] at hd
  intro i
  have hi := congrFun hd i
  fin_cases i <;> simpa [hD] using hi

lemma hadamardD_injective_on_full_diagonal_rank
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates)=Module.finrank ℂ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    Function.Injective (hadamardD.domRestrict L) := by
  let F := matrixDiagonalCoordinates.domRestrict L
  have hr : Module.finrank ℂ (LinearMap.range F)=Module.finrank ℂ L := by
    change Module.finrank ℂ (LinearMap.range (matrixDiagonalCoordinates.domRestrict L)) = _
    rw [LinearMap.range_domRestrict]
    exact hd
  have hk : Module.finrank ℂ (LinearMap.ker F)=0 := by
    have hn := F.finrank_range_add_finrank_ker
    omega
  have hF : Function.Injective F :=
    LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)
  have hzero (V : L) (hD : hadamardD V.val=0) : V=0 := by
    have hc := hadamardD_zero_constant_diagonal V.val (hs V.val V.property)
      (level_flat_entry_sum_zero L hp V.val V.property) hD
    have hr0 := level_flat_constant_diagonal_zero L hs hp V.val V.property
      ((hadamardB V.val 0+hadamardB V.val 1+hadamardB V.val 2)/4) hc
    apply hF
    change matrixDiagonalCoordinates V.val=matrixDiagonalCoordinates 0
    funext i
    change V.val (i,i)=0
    rw [hc i,hr0]
  intro V W he
  apply sub_eq_zero.mp
  apply hzero (V-W)
  change (hadamardD.domRestrict L) (V-W)=0
  rw [map_sub,he,sub_self]

lemma hadamardD_bijective_on_rank_three_flat
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : Module.finrank ℂ L=3)
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates)=3)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    Function.Bijective (hadamardD.domRestrict L) := by
  have hinj := hadamardD_injective_on_full_diagonal_rank L (hd.trans hL.symm) hs hp
  refine ⟨hinj,?_⟩
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [LinearMap.finrank_range_of_inj hinj,hL]
  simp

noncomputable def hadamardTrace : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] ℂ where
  toFun V := ∑ i : Fin 4, V (i,i)
  map_add' := by intros; simp [Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum]

lemma hadamardTrace_permute (σ : Equiv.Perm (Fin 4)) (V : Fin 4 × Fin 4 → ℂ) :
    hadamardTrace (entryPermute σ V)=hadamardTrace V := by
  exact Equiv.sum_comp σ (fun i => V (i,i))

lemma hadamardD_swap13 (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j)=V (j,i)) :
    hadamardD (entryPermute (Equiv.swap (1 : Fin 4) 3) V)=
      ![hadamardD V 2,hadamardD V 1,hadamardD V 0] := by
  have h10 := hs 1 0
  have h20 := hs 2 0
  have h30 := hs 3 0
  have h21 := hs 2 1
  have h31 := hs 3 1
  have h32 := hs 3 2
  funext i
  fin_cases i <;>
    simp [hadamardD,hadamardTransform,hadamardSigns,entryPermute,
      Equiv.swap_apply_def,Fin.sum_univ_succ,h10,h20,h30,h21,h31,h32] <;> ring

lemma hadamardD_swap23 (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j)=V (j,i)) :
    hadamardD (entryPermute (Equiv.swap (2 : Fin 4) 3) V)=
      ![hadamardD V 0,hadamardD V 2,hadamardD V 1] := by
  have h10 := hs 1 0
  have h20 := hs 2 0
  have h30 := hs 3 0
  have h21 := hs 2 1
  have h31 := hs 3 1
  have h32 := hs 3 2
  funext i
  fin_cases i <;>
    simp [hadamardD,hadamardTransform,hadamardSigns,entryPermute,
      Equiv.swap_apply_def,Fin.sum_univ_succ,h10,h20,h30,h21,h31,h32] <;> ring

lemma rank_three_flat_has_trace_pivot_basis
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : Module.finrank ℂ L=3)
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates)=3)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    ∃ σ : Equiv.Perm (Fin 4),
      ∃ U ∈ entryPermuteSubmodule σ L, ∃ V ∈ entryPermuteSubmodule σ L,
      ∃ W ∈ entryPermuteSubmodule σ L,
      hadamardD U=![1,0,0] ∧ hadamardD V=![0,1,0] ∧ hadamardD W=![0,0,1] ∧
      (hadamardTrace W ≠ 0 ∨ (hadamardTrace U=0 ∧ hadamardTrace V=0)) := by
  have hsurj := (hadamardD_bijective_on_rank_three_flat L hL hd hs hp).2
  obtain ⟨X,hX⟩ := hsurj ![1,0,0]
  obtain ⟨Y,hY⟩ := hsurj ![0,1,0]
  obtain ⟨Z,hZ⟩ := hsurj ![0,0,1]
  change hadamardD X.val=![1,0,0] at hX
  change hadamardD Y.val=![0,1,0] at hY
  change hadamardD Z.val=![0,0,1] at hZ
  have hid (htrace : hadamardTrace Z.val ≠ 0 ∨
      (hadamardTrace X.val=0 ∧ hadamardTrace Y.val=0)) :
      ∃ σ : Equiv.Perm (Fin 4),
        ∃ U ∈ entryPermuteSubmodule σ L, ∃ V ∈ entryPermuteSubmodule σ L,
        ∃ W ∈ entryPermuteSubmodule σ L,
        hadamardD U=![1,0,0] ∧ hadamardD V=![0,1,0] ∧ hadamardD W=![0,0,1] ∧
        (hadamardTrace W ≠ 0 ∨ (hadamardTrace U=0 ∧ hadamardTrace V=0)) := by
    refine ⟨Equiv.refl _,X.val,?_,Y.val,?_,Z.val,?_,hX,hY,hZ,htrace⟩
    · exact ⟨X.val,X.property,rfl⟩
    · exact ⟨Y.val,Y.property,rfl⟩
    · exact ⟨Z.val,Z.property,rfl⟩
  by_cases htz : hadamardTrace Z.val=0
  · by_cases hty : hadamardTrace Y.val=0
    · by_cases htx : hadamardTrace X.val=0
      · exact hid (Or.inr ⟨htx,hty⟩)
      · let σ := Equiv.swap (1 : Fin 4) 3
        refine ⟨σ,entryPermute σ Z.val,?_,entryPermute σ Y.val,?_,
          entryPermute σ X.val,?_,?_,?_,?_,Or.inl ?_⟩
        · exact (entryPermute_mem_iff σ L Z.val).mpr Z.property
        · exact (entryPermute_mem_iff σ L Y.val).mpr Y.property
        · exact (entryPermute_mem_iff σ L X.val).mpr X.property
        · simpa [σ,hZ] using hadamardD_swap13 Z.val (hs Z.val Z.property)
        · simpa [σ,hY] using hadamardD_swap13 Y.val (hs Y.val Y.property)
        · simpa [σ,hX] using hadamardD_swap13 X.val (hs X.val X.property)
        · simpa only [hadamardTrace_permute] using htx
    · let σ := Equiv.swap (2 : Fin 4) 3
      refine ⟨σ,entryPermute σ X.val,?_,entryPermute σ Z.val,?_,
        entryPermute σ Y.val,?_,?_,?_,?_,Or.inl ?_⟩
      · exact (entryPermute_mem_iff σ L X.val).mpr X.property
      · exact (entryPermute_mem_iff σ L Z.val).mpr Z.property
      · exact (entryPermute_mem_iff σ L Y.val).mpr Y.property
      · simpa [σ,hX] using hadamardD_swap23 X.val (hs X.val X.property)
      · simpa [σ,hZ] using hadamardD_swap23 Z.val (hs Z.val Z.property)
      · simpa [σ,hY] using hadamardD_swap23 Y.val (hs Y.val Y.property)
      · simpa only [hadamardTrace_permute] using hty
  · exact hid (Or.inl htz)

lemma rank_three_flat_has_hadamard_incidence_basis
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : Module.finrank ℂ L=3)
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates)=3)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    ∃ σ : Equiv.Perm (Fin 4), ∃ k l : ℂ,
      ∃ A ∈ entryPermuteSubmodule σ L, ∃ B ∈ entryPermuteSubmodule σ L,
      ∃ W ∈ entryPermuteSubmodule σ L,
      hadamardD A=![1,0,k] ∧ hadamardD B=![0,1,l] ∧ hadamardD W=![0,0,1] ∧
      hadamardTrace A=0 ∧ hadamardTrace B=0 := by
  obtain ⟨σ,U,hU,V,hV,W,hW,hDU,hDV,hDW,htr⟩ :=
    rank_three_flat_has_trace_pivot_basis L hL hd hs hp
  rcases htr with hw | ⟨hu,hv⟩
  · let k := -hadamardTrace U/hadamardTrace W
    let l := -hadamardTrace V/hadamardTrace W
    let A := U+k • W
    let B := V+l • W
    refine ⟨σ,k,l,A,?_,B,?_,W,hW,?_,?_,hDW,?_,?_⟩
    · exact (entryPermuteSubmodule σ L).add_mem hU ((entryPermuteSubmodule σ L).smul_mem k hW)
    · exact (entryPermuteSubmodule σ L).add_mem hV ((entryPermuteSubmodule σ L).smul_mem l hW)
    · simp [A,map_add,map_smul,hDU,hDW]
    · simp [B,map_add,map_smul,hDV,hDW]
    · simp [A,k,map_add,map_smul,hw]
    · simp [B,l,map_add,map_smul,hw]
  · exact ⟨σ,0,0,U,hU,V,hV,W,hW,hDU,hDV,hDW,hu,hv⟩

lemma rank_three_flat_hadamard_incidence_family
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : Module.finrank ℂ L=3)
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates)=3)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    ∃ (σ : Equiv.Perm (Fin 4)) (k l : ℂ) (BA BB BW PA PB PW : Fin 3 → ℂ),
      (∑ i : Fin 3, BA i)=0 ∧ (∑ i : Fin 3, BB i)=0 ∧
      ∀ s t u : ℂ,
        hadamardReconstruct (s • BA+t • BB+u • BW) (s • PA+t • PB+u • PW)
          ![s,t,k*s+l*t+u] ∈ entryPermuteSubmodule σ L ∧
        Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
          1+hadamardReconstruct (s • BA+t • BB+u • BW) (s • PA+t • PB+u • PW)
            ![s,t,k*s+l*t+u] (i,j))=24 := by
  obtain ⟨σ,k,l,A,hA,B,hB,W,hW,hDA,hDB,hDW,htrA,htrB⟩ :=
    rank_three_flat_has_hadamard_incidence_basis L hL hd hs hp
  let L' := entryPermuteSubmodule σ L
  have hs' := entryPermuteSubmodule_symmetric σ L hs
  have hp' := entryPermuteSubmodule_permanent σ L hp
  refine ⟨σ,k,l,hadamardB A,hadamardB B,hadamardB W,
    hadamardP A,hadamardP B,hadamardP W,?_,?_,?_⟩
  · exact (hadamard_trace_coordinates A (level_flat_entry_sum_zero L' hp' A hA)).trans htrA
  · exact (hadamard_trace_coordinates B (level_flat_entry_sum_zero L' hp' B hB)).trans htrB
  · intro s t u
    let T := s • A+t • B+u • W
    have hT : T ∈ L' := L'.add_mem (L'.add_mem (L'.smul_mem s hA) (L'.smul_mem t hB))
      (L'.smul_mem u hW)
    have hD : hadamardD T=![s,t,k*s+l*t+u] := by
      simp only [T,map_add,map_smul,hDA,hDB,hDW]
      funext i
      fin_cases i <;> simp <;> ring
    have hrec := hadamard_reconstruction T (hs' T hT) (level_flat_entry_sum_zero L' hp' T hT)
    rw [hD] at hrec
    simp only [T,map_add,map_smul] at hrec
    constructor
    · rw [hrec]
      exact hT
    · rw [hrec]
      exact hp' T hT

end PEqualNP.Outside.L_gct_231
