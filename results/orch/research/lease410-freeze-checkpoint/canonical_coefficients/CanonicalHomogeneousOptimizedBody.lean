def canonicalHadamardQuadratic (B P D : Fin 3 → ℂ) : ℂ :=
  (B 0)^2 + (B 1)^2 + (B 2)^2 - (P 0)^2 - (P 1)^2 - (P 2)^2 + 3*(D 0)^2 + 3*(D 1)^2 + 3*(D 2)^2

def canonicalHadamardCubic (B P D : Fin 3 → ℂ) : ℂ :=
  2*(B 0)*(B 1)*(B 2) + (B 0)*(P 0)^2 - 4*(B 0)*(P 0)*(D 0) + (B 0)*(P 1)^2 - 4*(B 0)*(P 1)*(D 1)
    + (B 0)*(P 2)^2 - 4*(B 0)*(P 2)*(D 2) + 5*(B 0)*(D 0)^2 + 3*(B 0)*(D 1)^2 + 3*(B 0)*(D 2)^2
    + (B 1)*(P 0)^2 - 4*(B 1)*(P 0)*(D 0) + (B 1)*(P 1)^2 - 4*(B 1)*(P 1)*(D 1) + (B 1)*(P 2)^2
    - 4*(B 1)*(P 2)*(D 2) + 3*(B 1)*(D 0)^2 + 5*(B 1)*(D 1)^2 + 3*(B 1)*(D 2)^2 + (B 2)*(P 0)^2
    - 4*(B 2)*(P 0)*(D 0) + (B 2)*(P 1)^2 - 4*(B 2)*(P 1)*(D 1) + (B 2)*(P 2)^2 - 4*(B 2)*(P 2)*(D 2)
    + 3*(B 2)*(D 0)^2 + 3*(B 2)*(D 1)^2 + 5*(B 2)*(D 2)^2 - 2*(P 0)*(P 1)*(P 2) + 6*(P 0)*(P 1)*(D 2)
    + 6*(P 0)*(P 2)*(D 1) - 14*(P 0)*(D 1)*(D 2) + 6*(P 1)*(P 2)*(D 0) - 14*(P 1)*(D 0)*(D 2)
    - 14*(P 2)*(D 0)*(D 1) + 30*(D 0)*(D 1)*(D 2)

def canonicalHadamardQuartic (B P D : Fin 3 → ℂ) : ℂ :=
  3*(B 0)^4 + 2*(B 0)^2*(B 1)^2 + 2*(B 0)^2*(B 2)^2 - 2*(B 0)^2*(P 0)^2 - 2*(B 0)^2*(P 1)^2
    + 16*(B 0)^2*(P 1)*(D 1) - 2*(B 0)^2*(P 2)^2 + 16*(B 0)^2*(P 2)*(D 2) + 6*(B 0)^2*(D 0)^2
    - 26*(B 0)^2*(D 1)^2 - 26*(B 0)^2*(D 2)^2 + 4*(B 0)*(B 1)*(P 0)^2 - 16*(B 0)*(B 1)*(P 0)*(D 0)
    + 4*(B 0)*(B 1)*(P 1)^2 - 16*(B 0)*(B 1)*(P 1)*(D 1) + 4*(B 0)*(B 1)*(P 2)^2
    - 16*(B 0)*(B 1)*(P 2)*(D 2) + 12*(B 0)*(B 1)*(D 0)^2 + 12*(B 0)*(B 1)*(D 1)^2
    + 20*(B 0)*(B 1)*(D 2)^2 + 4*(B 0)*(B 2)*(P 0)^2 - 16*(B 0)*(B 2)*(P 0)*(D 0) + 4*(B 0)*(B 2)*(P 1)^2
    - 16*(B 0)*(B 2)*(P 1)*(D 1) + 4*(B 0)*(B 2)*(P 2)^2 - 16*(B 0)*(B 2)*(P 2)*(D 2)
    + 12*(B 0)*(B 2)*(D 0)^2 + 20*(B 0)*(B 2)*(D 1)^2 + 12*(B 0)*(B 2)*(D 2)^2
    - 8*(B 0)*(P 0)*(P 1)*(P 2) + 8*(B 0)*(P 0)*(P 1)*(D 2) + 8*(B 0)*(P 0)*(P 2)*(D 1)
    + 8*(B 0)*(P 0)*(D 1)*(D 2) + 24*(B 0)*(P 1)*(P 2)*(D 0) - 40*(B 0)*(P 1)*(D 0)*(D 2)
    - 40*(B 0)*(P 2)*(D 0)*(D 1) + 56*(B 0)*(D 0)*(D 1)*(D 2) + 3*(B 1)^4 + 2*(B 1)^2*(B 2)^2
    - 2*(B 1)^2*(P 0)^2 + 16*(B 1)^2*(P 0)*(D 0) - 2*(B 1)^2*(P 1)^2 - 2*(B 1)^2*(P 2)^2
    + 16*(B 1)^2*(P 2)*(D 2) - 26*(B 1)^2*(D 0)^2 + 6*(B 1)^2*(D 1)^2 - 26*(B 1)^2*(D 2)^2
    + 4*(B 1)*(B 2)*(P 0)^2 - 16*(B 1)*(B 2)*(P 0)*(D 0) + 4*(B 1)*(B 2)*(P 1)^2
    - 16*(B 1)*(B 2)*(P 1)*(D 1) + 4*(B 1)*(B 2)*(P 2)^2 - 16*(B 1)*(B 2)*(P 2)*(D 2)
    + 20*(B 1)*(B 2)*(D 0)^2 + 12*(B 1)*(B 2)*(D 1)^2 + 12*(B 1)*(B 2)*(D 2)^2
    - 8*(B 1)*(P 0)*(P 1)*(P 2) + 8*(B 1)*(P 0)*(P 1)*(D 2) + 24*(B 1)*(P 0)*(P 2)*(D 1)
    - 40*(B 1)*(P 0)*(D 1)*(D 2) + 8*(B 1)*(P 1)*(P 2)*(D 0) + 8*(B 1)*(P 1)*(D 0)*(D 2)
    - 40*(B 1)*(P 2)*(D 0)*(D 1) + 56*(B 1)*(D 0)*(D 1)*(D 2) + 3*(B 2)^4 - 2*(B 2)^2*(P 0)^2
    + 16*(B 2)^2*(P 0)*(D 0) - 2*(B 2)^2*(P 1)^2 + 16*(B 2)^2*(P 1)*(D 1) - 2*(B 2)^2*(P 2)^2
    - 26*(B 2)^2*(D 0)^2 - 26*(B 2)^2*(D 1)^2 + 6*(B 2)^2*(D 2)^2 - 8*(B 2)*(P 0)*(P 1)*(P 2)
    + 24*(B 2)*(P 0)*(P 1)*(D 2) + 8*(B 2)*(P 0)*(P 2)*(D 1) - 40*(B 2)*(P 0)*(D 1)*(D 2)
    + 8*(B 2)*(P 1)*(P 2)*(D 0) - 40*(B 2)*(P 1)*(D 0)*(D 2) + 8*(B 2)*(P 2)*(D 0)*(D 1)
    + 56*(B 2)*(D 0)*(D 1)*(D 2) + 2*(P 0)^4 - 16*(P 0)^3*(D 0) + 4*(P 0)^2*(P 1)^2
    - 16*(P 0)^2*(P 1)*(D 1) + 4*(P 0)^2*(P 2)^2 - 16*(P 0)^2*(P 2)*(D 2) + 52*(P 0)^2*(D 0)^2
    + 12*(P 0)^2*(D 1)^2 + 12*(P 0)^2*(D 2)^2 - 16*(P 0)*(P 1)^2*(D 0) + 64*(P 0)*(P 1)*(D 0)*(D 1)
    - 16*(P 0)*(P 2)^2*(D 0) + 64*(P 0)*(P 2)*(D 0)*(D 2) - 80*(P 0)*(D 0)^3 - 48*(P 0)*(D 0)*(D 1)^2
    - 48*(P 0)*(D 0)*(D 2)^2 + 2*(P 1)^4 - 16*(P 1)^3*(D 1) + 4*(P 1)^2*(P 2)^2 - 16*(P 1)^2*(P 2)*(D 2)
    + 12*(P 1)^2*(D 0)^2 + 52*(P 1)^2*(D 1)^2 + 12*(P 1)^2*(D 2)^2 - 16*(P 1)*(P 2)^2*(D 1)
    + 64*(P 1)*(P 2)*(D 1)*(D 2) - 48*(P 1)*(D 0)^2*(D 1) - 80*(P 1)*(D 1)^3 - 48*(P 1)*(D 1)*(D 2)^2
    + 2*(P 2)^4 - 16*(P 2)^3*(D 2) + 12*(P 2)^2*(D 0)^2 + 12*(P 2)^2*(D 1)^2 + 52*(P 2)^2*(D 2)^2
    - 48*(P 2)*(D 0)^2*(D 2) - 48*(P 2)*(D 1)^2*(D 2) - 80*(P 2)*(D 2)^3 + 50*(D 0)^4
    + 28*(D 0)^2*(D 1)^2 + 28*(D 0)^2*(D 2)^2 + 50*(D 1)^4 + 28*(D 1)^2*(D 2)^2 + 50*(D 2)^4

noncomputable def canonicalHadamardMatrix (B P D : Fin 3 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(B 0+B 1+B 2+2*D 0+2*D 1+2*D 2)/4,(B 0-B 1-B 2+2*P 0-4*D 0)/4,(-B 0+B 1-B 2+2*P 1-4*D 1)/4,(-B 0-B 1+B 2+2*P 2-4*D 2)/4;
    (B 0-B 1-B 2+2*P 0-4*D 0)/4,(B 0+B 1+B 2+2*D 0-2*D 1-2*D 2)/4,(-B 0-B 1+B 2-2*P 2+4*D 2)/4,(-B 0+B 1-B 2-2*P 1+4*D 1)/4;
    (-B 0+B 1-B 2+2*P 1-4*D 1)/4,(-B 0-B 1+B 2-2*P 2+4*D 2)/4,(B 0+B 1+B 2-2*D 0+2*D 1-2*D 2)/4,(B 0-B 1-B 2-2*P 0+4*D 0)/4;
    (-B 0-B 1+B 2+2*P 2-4*D 2)/4,(-B 0+B 1-B 2-2*P 1+4*D 1)/4,(B 0-B 1-B 2-2*P 0+4*D 0)/4,(B 0+B 1+B 2-2*D 0-2*D 1+2*D 2)/4]

lemma canonical_reconstruct_entry (B P D : Fin 3 → ℂ) (i j : Fin 4) :
    hadamardReconstruct B P D (i,j)=canonicalHadamardMatrix B P D i j := by
  fin_cases i <;> fin_cases j <;>
    simp [hadamardReconstruct,hadamardTransform,hadamardCoordinateMatrix,
      hadamardSigns,Fin.sum_univ_succ,canonicalHadamardMatrix] <;> ring

set_option maxHeartbeats 2400000 in
lemma canonical_hadamard_radial_permanent (B P D : Fin 3 → ℂ) (z : ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+hadamardReconstruct (z • B) (z • P) (z • D) (i,j)) =
      24+canonicalHadamardQuadratic B P D*z^2+
        canonicalHadamardCubic B P D/2*z^3+canonicalHadamardQuartic B P D/32*z^4 := by
  simp_rw [canonical_reconstruct_entry]
  rw [permanent_four]
  simp [canonicalHadamardMatrix,canonicalHadamardQuadratic,
    canonicalHadamardCubic,canonicalHadamardQuartic]
  ring

lemma canonical_hadamard_homogeneous_zero (B P D : Fin 3 → ℂ)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+hadamardReconstruct (z • B) (z • P) (z • D) (i,j))=24) :
    canonicalHadamardQuadratic B P D=0 ∧ canonicalHadamardCubic B P D=0 ∧
      canonicalHadamardQuartic B P D=0 := by
  have hh : ∀ z : ℂ, (0:ℂ)*z+canonicalHadamardQuadratic B P D*z^2+
      (canonicalHadamardCubic B P D/2)*z^3+
      (canonicalHadamardQuartic B P D/32)*z^4=0 := by
    intro z
    have h := hp z
    rw [canonical_hadamard_radial_permanent] at h
    linear_combination h
  obtain ⟨_,h2,h3,h4⟩ := quartic_all_coefficients _ _ _ _ hh
  refine ⟨h2,?_,?_⟩
  · linear_combination 2*h3
  · linear_combination 32*h4

def canonicalCoefficientCoordinates (v : Fin 9 → ℂ) (s t u : ℂ) : Fin 3 → ℂ :=
  ![v 0*s+v 1*t+v 2*u,v 3*s+v 4*t+v 5*u,v 6*s+v 7*t+v 8*u]

lemma canonicalCoefficientCoordinates_scale (v : Fin 9 → ℂ) (s t u z : ℂ) :
    canonicalCoefficientCoordinates v (z*s) (z*t) (z*u)=
      z • canonicalCoefficientCoordinates v s t u := by
  funext i
  fin_cases i <;> simp [canonicalCoefficientCoordinates] <;> ring

lemma canonical_family_homogeneous_zero (p b : Fin 9 → ℂ)
    (hp : ∀ s t u : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+hadamardReconstruct (canonicalCoefficientCoordinates b s t u)
        (canonicalCoefficientCoordinates p s t u) ![s,t,u] (i,j))=24) :
    ∀ s t u : ℂ,
      canonicalHadamardQuadratic (canonicalCoefficientCoordinates b s t u)
        (canonicalCoefficientCoordinates p s t u) ![s,t,u]=0 ∧
      canonicalHadamardCubic (canonicalCoefficientCoordinates b s t u)
        (canonicalCoefficientCoordinates p s t u) ![s,t,u]=0 ∧
      canonicalHadamardQuartic (canonicalCoefficientCoordinates b s t u)
        (canonicalCoefficientCoordinates p s t u) ![s,t,u]=0 := by
  intro s t u
  apply canonical_hadamard_homogeneous_zero
  intro z
  have h := hp (z*s) (z*t) (z*u)
  rw [canonicalCoefficientCoordinates_scale,canonicalCoefficientCoordinates_scale] at h
  have hd : (![z*s,z*t,z*u] : Fin 3 → ℂ)=z • ![s,t,u] := by
    funext i
    fin_cases i <;> simp
  rw [hd] at h
  exact h

lemma rank_three_flat_canonical_hadamard_family
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : Module.finrank ℂ L=3)
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates)=3)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    ∃ p b : Fin 9 → ℂ, ∀ s t u : ℂ,
      Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
        1+hadamardReconstruct (canonicalCoefficientCoordinates b s t u)
          (canonicalCoefficientCoordinates p s t u) ![s,t,u] (i,j))=24 := by
  obtain ⟨_,honto⟩ := hadamardD_bijective_on_rank_three_flat L hL hd hs hp
  obtain ⟨X,hX⟩ := honto ![1,0,0]
  obtain ⟨Y,hY⟩ := honto ![0,1,0]
  obtain ⟨Z,hZ⟩ := honto ![0,0,1]
  change hadamardD X.val=![1,0,0] at hX
  change hadamardD Y.val=![0,1,0] at hY
  change hadamardD Z.val=![0,0,1] at hZ
  let p : Fin 9 → ℂ := ![hadamardP X.val 0,hadamardP Y.val 0,hadamardP Z.val 0,
    hadamardP X.val 1,hadamardP Y.val 1,hadamardP Z.val 1,
    hadamardP X.val 2,hadamardP Y.val 2,hadamardP Z.val 2]
  let b : Fin 9 → ℂ := ![hadamardB X.val 0,hadamardB Y.val 0,hadamardB Z.val 0,
    hadamardB X.val 1,hadamardB Y.val 1,hadamardB Z.val 1,
    hadamardB X.val 2,hadamardB Y.val 2,hadamardB Z.val 2]
  refine ⟨p,b,?_⟩
  intro s t u
  let T := s • X.val+t • Y.val+u • Z.val
  have hT : T ∈ L := L.add_mem (L.add_mem (L.smul_mem s X.property)
    (L.smul_mem t Y.property)) (L.smul_mem u Z.property)
  have hD : hadamardD T=![s,t,u] := by
    dsimp [T]
    rw [map_add,map_add,map_smul,map_smul,map_smul,hX,hY,hZ]
    funext i
    fin_cases i <;> simp
  have hB : hadamardB T=canonicalCoefficientCoordinates b s t u := by
    dsimp [T]
    rw [map_add,map_add,map_smul,map_smul,map_smul]
    funext i
    fin_cases i <;> simp [b,canonicalCoefficientCoordinates] <;> ring
  have hP : hadamardP T=canonicalCoefficientCoordinates p s t u := by
    dsimp [T]
    rw [map_add,map_add,map_smul,map_smul,map_smul]
    funext i
    fin_cases i <;> simp [p,canonicalCoefficientCoordinates] <;> ring
  have hr := hadamard_reconstruction T (hs T hT) (level_flat_entry_sum_zero L hp T hT)
  rw [hB,hP,hD] at hr
  rw [hr]
  exact hp T hT

