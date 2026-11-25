import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

lemma diagonal_rank_two_has_tracezero_pair
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : Module.finrank ℂ L = 3)
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates) = 2) :
    ∃ H ∈ L, ∃ V ∈ L, H ≠ 0 ∧
      (∀ i : Fin 4, H (i,i)=0) ∧
      (∃ i : Fin 4, V (i,i) ≠ 0) ∧
      (∑ i : Fin 4, V (i,i))=0 := by
  let F := matrixDiagonalCoordinates.domRestrict L
  have hrF : Module.finrank ℂ (LinearMap.range F) = 2 := by
    change Module.finrank ℂ
      (LinearMap.range (matrixDiagonalCoordinates.domRestrict L)) = 2
    rw [LinearMap.range_domRestrict]
    exact hd
  have hkF : 0 < Module.finrank ℂ (LinearMap.ker F) := by
    have hn := F.finrank_range_add_finrank_ker
    omega
  letI : Nontrivial (LinearMap.ker F) := Module.nontrivial_of_finrank_pos hkF
  obtain ⟨h, hh⟩ := exists_ne (0 : LinearMap.ker F)
  have hHne : h.val.val ≠ 0 := by
    intro he
    apply hh
    apply Subtype.ext
    apply Subtype.ext
    exact he
  have hHz : ∀ i : Fin 4, h.val.val (i,i)=0 := by
    intro i
    have he : F h.val=0 := h.property
    exact congrFun he i
  let D := L.map matrixDiagonalCoordinates
  let G : D →ₗ[ℂ] ℂ :=
    { toFun := fun d => ∑ i : Fin 4, d.val i
      map_add' := by intros; simp [Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.mul_sum] }
  have hrG : Module.finrank ℂ (LinearMap.range G) ≤ 1 := by
    have hb := Submodule.finrank_le (LinearMap.range G)
    simpa using hb
  have hkG : 0 < Module.finrank ℂ (LinearMap.ker G) := by
    have hn := G.finrank_range_add_finrank_ker
    change Module.finrank ℂ D=2 at hd
    omega
  letI : Nontrivial (LinearMap.ker G) := Module.nontrivial_of_finrank_pos hkG
  obtain ⟨d, hdne⟩ := exists_ne (0 : LinearMap.ker G)
  have hdval : d.val.val ≠ 0 := by
    intro he
    apply hdne
    apply Subtype.ext
    apply Subtype.ext
    exact he
  obtain ⟨V,hV,hVD⟩ := d.val.property
  have hVdiag : ∃ i : Fin 4, V (i,i) ≠ 0 := by
    by_contra he
    push Not at he
    apply hdval
    rw [← hVD]
    funext i
    exact he i
  have hVtrace : (∑ i : Fin 4, V (i,i))=0 := by
    have he : G d.val=0 := d.property
    change (∑ i : Fin 4, d.val.val i)=0 at he
    rw [← hVD] at he
    exact he
  exact ⟨h.val.val,h.val.property,V,hV,hHne,hHz,hVdiag,hVtrace⟩

lemma no_diagonal_rank_two_three_flat_of_tracezero_star_classification
    (hclass : ∀ H V : Fin 4 × Fin 4 → ℂ,
      H ≠ 0 → (∀ i : Fin 4, H (i,i)=0) →
      (∃ i : Fin 4, V (i,i) ≠ 0) → (∑ i : Fin 4, V (i,i))=0 →
      (∀ i j : Fin 4, H (i,j)=H (j,i)) →
      (∀ i j : Fin 4, V (i,j)=V (j,i)) →
      (∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
        1+a*H (i,j)+z*V (i,j))=24) →
      ∃ (σ : Equiv.Perm (Fin 4)) (a b : ℂ),
        starMatrix a b ≠ 0 ∧ entryPermute σ H=starMatrix a b)
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : Module.finrank ℂ L = 3)
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates) = 2)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) : False := by
  obtain ⟨H,hH,V,hV,hHne,hHz,hVdiag,hVtrace⟩ :=
    diagonal_rank_two_has_tracezero_pair L hL hd
  have hpair : ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*H (i,j)+z*V (i,j))=24 := by
    intro a z
    have he := hp _ (L.add_mem (L.smul_mem a hH) (L.smul_mem z hV))
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_assoc] using he
  obtain ⟨σ,a,b,hne,heq⟩ := hclass H V hHne hHz hVdiag hVtrace (hs H hH) (hs V hV) hpair
  have hm : starMatrix a b ∈ entryPermuteSubmodule σ L := by
    rw [← heq]
    exact (entryPermute_mem_iff σ L H).mpr hH
  have hb := containing_nonzero_starMatrix_finrank_le_two
    (entryPermuteSubmodule σ L) a b hne hm
    (entryPermuteSubmodule_symmetric σ L hs)
    (entryPermuteSubmodule_permanent σ L hp)
  rw [entryPermuteSubmodule_finrank] at hb
  omega

def NormalizedIncidentOppositeEdge : Prop :=
  ∀ H V : Fin 4 × Fin 4 → ℂ,
    (∀ i j : Fin 4, H (i,j)=H (j,i)) →
    (∀ i j : Fin 4, V (i,j)=V (j,i)) →
    (∀ i : Fin 4, H (i,i)=0) →
    (∑ i : Fin 4, V (i,i))=0 →
    V (0,0)=1 → H (0,1)=1 → V (0,1)=0 →
    (∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*H (i,j)+z*V (i,j))=24) → H (2,3)=0

lemma incident_edge_product_zero
    (hincident : NormalizedIncidentOppositeEdge)
    (H V : Fin 4 × Fin 4 → ℂ)
    (hHs : ∀ i j : Fin 4, H (i,j)=H (j,i))
    (hVs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hHz : ∀ i : Fin 4, H (i,i)=0)
    (hVtrace : (∑ i : Fin 4, V (i,i))=0) (hV00 : V (0,0) ≠ 0)
    (hp : ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*H (i,j)+z*V (i,j))=24) : H (0,1)*H (2,3)=0 := by
  by_cases hH01 : H (0,1)=0
  · simp [hH01]
  let A := (H (0,1))⁻¹ • H
  let B := (V (0,0))⁻¹ • V - ((V (0,0))⁻¹*V (0,1)) • A
  have hAs : ∀ i j : Fin 4, A (i,j)=A (j,i) := by
    intro i j
    change (H (0,1))⁻¹*H (i,j)=(H (0,1))⁻¹*H (j,i)
    rw [hHs i j]
  have hBs : ∀ i j : Fin 4, B (i,j)=B (j,i) := by
    intro i j
    change (V (0,0))⁻¹*V (i,j)-((V (0,0))⁻¹*V (0,1))*A (i,j)=
      (V (0,0))⁻¹*V (j,i)-((V (0,0))⁻¹*V (0,1))*A (j,i)
    rw [hVs i j,hAs i j]
  have hAz : ∀ i : Fin 4, A (i,i)=0 := by intro i; simp [A,hHz]
  have hA01 : A (0,1)=1 := by simp [A,hH01]
  have hB00 : B (0,0)=1 := by simp [B,hAz,hV00]
  have hB01 : B (0,1)=0 := by simp [B,hA01]
  have hBtrace : (∑ i : Fin 4, B (i,i))=0 := by
    simp [B,hAz,← Finset.mul_sum,hVtrace]
  have hpair : ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*A (i,j)+z*B (i,j))=24 := by
    intro a z
    have heq : (Matrix.of fun (i j : Fin 4) => 1+a*A (i,j)+z*B (i,j))=
        Matrix.of fun (i j : Fin 4) =>
          1+((a-z*((V (0,0))⁻¹*V (0,1)))*(H (0,1))⁻¹)*H (i,j)+
            (z*(V (0,0))⁻¹)*V (i,j) := by
      ext i j
      simp [A,B]
      ring
    rw [heq]
    exact hp _ _
  have hA23 := hincident A B hAs hBs hAz hBtrace hB00 hA01 hB01 hpair
  have hH23 : H (2,3)=0 := by
    change (H (0,1))⁻¹*H (2,3)=0 at hA23
    exact (mul_eq_zero.mp hA23).resolve_left (inv_ne_zero hH01)
  simp [hH23]

lemma level_pair_permutation
    (σ : Equiv.Perm (Fin 4)) (H V : Fin 4 × Fin 4 → ℂ)
    (hp : ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*H (i,j)+z*V (i,j))=24) :
    ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*entryPermute σ H (i,j)+z*entryPermute σ V (i,j))=24 := by
  intro a z
  have he := entryPermute_permanent σ (fun p => a*H p+z*V p)
  have hb : Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+(a*H (i,j)+z*V (i,j)))=24 := by simpa only [add_assoc] using hp a z
  simpa only [entryPermute_apply,add_assoc] using he.trans hb

lemma incident_opposite_products_zero
    (hincident : NormalizedIncidentOppositeEdge)
    (H V : Fin 4 × Fin 4 → ℂ)
    (hHs : ∀ i j : Fin 4, H (i,j)=H (j,i))
    (hVs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hHz : ∀ i : Fin 4, H (i,i)=0)
    (hVtrace : (∑ i : Fin 4, V (i,i))=0) (hV00 : V (0,0) ≠ 0)
    (hp : ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*H (i,j)+z*V (i,j))=24) :
    H (0,1)*H (2,3)=0 ∧ H (0,2)*H (1,3)=0 ∧ H (0,3)*H (1,2)=0 := by
  have hperm (σ : Equiv.Perm (Fin 4)) (hσ0 : σ 0=0) :
      H (σ 0,σ 1)*H (σ 2,σ 3)=0 := by
    have hV00' : entryPermute σ V (0,0) ≠ 0 := by
      simpa only [entryPermute_apply,hσ0] using hV00
    have htrace : (∑ i : Fin 4, entryPermute σ V (i,i))=0 := by
      change (∑ i : Fin 4, V (σ i,σ i))=0
      exact (Equiv.sum_comp σ (fun i => V (i,i))).trans hVtrace
    exact incident_edge_product_zero hincident (entryPermute σ H) (entryPermute σ V)
      (entryPermute_symmetric σ H hHs) (entryPermute_symmetric σ V hVs)
      (entryPermute_hollow σ H hHz) htrace hV00' (level_pair_permutation σ H V hp)
  refine ⟨incident_edge_product_zero hincident H V hHs hVs hHz hVtrace hV00 hp,?_,?_⟩
  · have h := hperm (Equiv.swap (1 : Fin 4) 2) (by decide)
    simpa [Equiv.swap_apply_def] using h
  · have h := hperm (Equiv.swap (1 : Fin 4) 3) (by decide)
    simpa [Equiv.swap_apply_def,hHs 2 1] using h

lemma hollow_star_support_of_opposite_products (a b c d e f : ℂ)
    (haf : a*f=0) (hbe : b*e=0) (hcd : c*d=0)
    (hT : a*b*d+a*c*e+b*c*f+d*e*f=0) :
    (d=0 ∧ e=0 ∧ f=0) ∨ (b=0 ∧ c=0 ∧ f=0) ∨
    (a=0 ∧ c=0 ∧ e=0) ∨ (a=0 ∧ b=0 ∧ d=0) := by
  by_cases ha : a=0
  · by_cases hb : b=0
    · by_cases hc : c=0
      · have hdef : d*e*f=0 := by simpa [ha,hb,hc] using hT
        rcases mul_eq_zero.mp hdef with hde | hf
        · rcases mul_eq_zero.mp hde with hd | he
          · exact Or.inr (Or.inr (Or.inr ⟨ha,hb,hd⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨ha,hc,he⟩))
        · exact Or.inr (Or.inl ⟨hb,hc,hf⟩)
      · have hd : d=0 := (mul_eq_zero.mp hcd).resolve_left hc
        exact Or.inr (Or.inr (Or.inr ⟨ha,hb,hd⟩))
    · have he : e=0 := (mul_eq_zero.mp hbe).resolve_left hb
      by_cases hc : c=0
      · exact Or.inr (Or.inr (Or.inl ⟨ha,hc,he⟩))
      · have hd : d=0 := (mul_eq_zero.mp hcd).resolve_left hc
        have hbcf : b*c*f=0 := by simpa [ha,he] using hT
        have hf : f=0 := (mul_eq_zero.mp hbcf).resolve_left (mul_ne_zero hb hc)
        exact Or.inl ⟨hd,he,hf⟩
  · have hf : f=0 := (mul_eq_zero.mp haf).resolve_left ha
    have hsum : b*d+c*e=0 := by
      have hh : a*(b*d+c*e)=0 := by linear_combination hT-(b*c+d*e)*hf
      exact (mul_eq_zero.mp hh).resolve_left ha
    have hbd : b*d=0 := by
      have hh : (b*d)^2=0 := by linear_combination b*d*hsum-c*d*hbe
      exact eq_zero_of_pow_eq_zero hh
    have hce : c*e=0 := by linear_combination hsum-hbd
    by_cases hb : b=0
    · by_cases hc : c=0
      · exact Or.inr (Or.inl ⟨hb,hc,hf⟩)
      · have hd : d=0 := (mul_eq_zero.mp hcd).resolve_left hc
        have he : e=0 := (mul_eq_zero.mp hce).resolve_left hc
        exact Or.inl ⟨hd,he,hf⟩
    · have hd : d=0 := (mul_eq_zero.mp hbd).resolve_left hb
      have he : e=0 := (mul_eq_zero.mp hbe).resolve_left hb
      exact Or.inl ⟨hd,he,hf⟩

lemma hollow_opposite_scalar_permuted_star (a b c d e f : ℂ)
    (hS : a+b+c+d+e+f=0)
    (haf : a*f=0) (hbe : b*e=0) (hcd : c*d=0)
    (hT : a*b*d+a*c*e+b*c*f+d*e*f=0) :
    ∃ (σ : Equiv.Perm (Fin 4)) (u v : ℂ),
      entryPermute σ (fun p => hollowMatrix a b c d e f p.1 p.2)=starMatrix u v := by
  rcases hollow_star_support_of_opposite_products a b c d e f haf hbe hcd hT with
    ⟨hd,he,hf⟩ | ⟨hb,hc,hf⟩ | ⟨ha,hc,he⟩ | ⟨ha,hb,hd⟩
  · have hc : c = -a-b := by linear_combination hS-hd-he-hf
    refine ⟨Equiv.refl _,a,b,?_⟩
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,hollowMatrix,starMatrix,hc,hd,he,hf]
  · have he : e = -a-d := by linear_combination hS-hb-hc-hf
    refine ⟨Equiv.swap 0 1,a,d,?_⟩
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,Equiv.swap_apply_def,hollowMatrix,starMatrix,hb,hc,he,hf]
  · have hf : f = -d-b := by linear_combination hS-ha-hc-he
    refine ⟨Equiv.swap 0 2,d,b,?_⟩
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,Equiv.swap_apply_def,hollowMatrix,starMatrix,ha,hc,he,hf]
  · have hc : c = -e-f := by linear_combination hS-ha-hb-hd
    refine ⟨Equiv.swap 0 3,e,f,?_⟩
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [entryPermute,Equiv.swap_apply_def,hollowMatrix,starMatrix,ha,hb,hc,hd]

lemma hollow_opposite_products_permuted_star (H : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, H (i,j)=H (j,i))
    (hz : ∀ i : Fin 4, H (i,i)=0) (hne : H ≠ 0)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+z*H (i,j))=24)
    (haf : H (0,1)*H (2,3)=0) (hbe : H (0,2)*H (1,3)=0) (hcd : H (0,3)*H (1,2)=0) :
    ∃ (σ : Equiv.Perm (Fin 4)) (a b : ℂ),
      starMatrix a b ≠ 0 ∧ entryPermute σ H=starMatrix a b := by
  have hrec : H=(fun p => hollowMatrix (H (0,1)) (H (0,2)) (H (0,3))
      (H (1,2)) (H (1,3)) (H (2,3)) p.1 p.2) := by
    funext p
    exact hollow_reconstruction H hs hz p.1 p.2
  have hp' : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+z*hollowMatrix (H (0,1)) (H (0,2)) (H (0,3))
        (H (1,2)) (H (1,3)) (H (2,3)) i j)=24 := by
    intro z
    convert hp z using 1
    congr 1
    funext i j
    change 1+z*hollowMatrix (H (0,1)) (H (0,2)) (H (0,3))
      (H (1,2)) (H (1,3)) (H (2,3)) i j=1+z*H (i,j)
    rw [hollow_reconstruction H hs hz i j]
  have hS := (hollow_coefficient_constraints _ _ _ _ _ _ hp').1
  have hC := hollow_coefficient_cubic_zero _ _ _ _ _ _ hp'
  have hT : H (0,1)*H (0,2)*H (1,2)+H (0,1)*H (0,3)*H (1,3)+
      H (0,2)*H (0,3)*H (2,3)+H (1,2)*H (1,3)*H (2,3)=0 := by
    dsimp [hollowCubic] at hC
    linear_combination hC/2-
      (H (0,1)+H (0,2)+H (0,3)+H (1,2)+H (1,3)+H (2,3))*(haf+hbe+hcd)
  obtain ⟨σ,a,b,heq⟩ := hollow_opposite_scalar_permuted_star _ _ _ _ _ _ hS haf hbe hcd hT
  have he : entryPermute σ H=starMatrix a b := by rw [hrec]; exact heq
  refine ⟨σ,a,b,?_,he⟩
  intro hzero
  apply hne
  apply (entryPermute σ).injective
  rw [he,hzero,map_zero]

lemma tracezero_pair_star_of_normalized_incident
    (hincident : NormalizedIncidentOppositeEdge)
    (H V : Fin 4 × Fin 4 → ℂ)
    (hHne : H ≠ 0) (hHz : ∀ i : Fin 4, H (i,i)=0)
    (hVdiag : ∃ i : Fin 4, V (i,i) ≠ 0)
    (hVtrace : (∑ i : Fin 4, V (i,i))=0)
    (hHs : ∀ i j : Fin 4, H (i,j)=H (j,i))
    (hVs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*H (i,j)+z*V (i,j))=24) :
    ∃ (σ : Equiv.Perm (Fin 4)) (a b : ℂ),
      starMatrix a b ≠ 0 ∧ entryPermute σ H=starMatrix a b := by
  obtain ⟨i,hi⟩ := hVdiag
  let σ := Equiv.swap (0 : Fin 4) i
  have hσ : σ 0=i := by simp [σ]
  let H' := entryPermute σ H
  let V' := entryPermute σ V
  have hHne' : H' ≠ 0 := by
    intro he
    apply hHne
    apply (entryPermute σ).injective
    simpa only [map_zero] using he
  have hHsym := entryPermute_symmetric σ H hHs
  have hVsym := entryPermute_symmetric σ V hVs
  have hHz' := entryPermute_hollow σ H hHz
  have hV00 : V' (0,0) ≠ 0 := by simpa only [V',entryPermute_apply,hσ] using hi
  have hVtr : (∑ i : Fin 4, V' (i,i))=0 := by
    change (∑ i : Fin 4, V (σ i,σ i))=0
    exact (Equiv.sum_comp σ (fun i => V (i,i))).trans hVtrace
  have hpair := level_pair_permutation σ H V hp
  obtain ⟨haf,hbe,hcd⟩ := incident_opposite_products_zero hincident H' V'
    hHsym hVsym hHz' hVtr hV00 hpair
  have hline : ∀ z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+z*H' (i,j))=24 := by
    intro z
    simpa only [zero_mul,add_zero] using hpair z 0
  obtain ⟨τ,a,b,hne,heq⟩ := hollow_opposite_products_permuted_star H'
    hHsym hHz' hHne' hline haf hbe hcd
  refine ⟨σ*τ,a,b,hne,?_⟩
  calc
    entryPermute (σ*τ) H=entryPermute τ (entryPermute σ H) := by
      funext p
      rcases p with ⟨j,k⟩
      simp [entryPermute_apply,Equiv.Perm.mul_apply]
    _=starMatrix a b := heq

lemma no_rank_two_diagonal_three_flat_of_normalized_incident
    (hincident : NormalizedIncidentOppositeEdge)
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : Module.finrank ℂ L=3)
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates)=2)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) : False := by
  exact no_diagonal_rank_two_three_flat_of_tracezero_star_classification
    (tracezero_pair_star_of_normalized_incident hincident) L hL hd hs hp

end PEqualNP.Outside.L_gct_231
