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

end PEqualNP.Outside.L_gct_231
