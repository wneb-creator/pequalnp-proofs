import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

lemma finrank_le_two_of_zero_coordinate_kernel
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (p q : Fin 4 × Fin 4)
    (hk : ∀ V ∈ L, V p=0 → V q=0 → V=0) : Module.finrank ℂ L ≤ 2 := by
  let F : L →ₗ[ℂ] (Fin 2 → ℂ) :=
    { toFun := fun V => ![V.val p,V.val q]
      map_add' := by intros; ext i; fin_cases i <;> simp
      map_smul' := by intros; ext i; fin_cases i <;> simp }
  have hker : ∀ V : L, F V=0 → V=0 := by
    intro V hV
    apply Subtype.ext
    have hp : V.val p=0 := by simpa [F] using congrFun hV 0
    have hq : V.val q=0 := by simpa [F] using congrFun hV 1
    exact hk V.val V.property hp hq
  have hF : Function.Injective F := by
    intro V W h
    apply sub_eq_zero.mp
    apply hker (V-W)
    rw [map_sub,h,sub_self]
  have hd := Submodule.finrank_le (LinearMap.range F)
  rw [LinearMap.finrank_range_of_inj hF] at hd
  simpa using hd

lemma containing_nonstar1_plane_finrank_le_two
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hc : ∀ a b : ℂ, nonstarPlane1 a b ∈ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) : Module.finrank ℂ L ≤ 2 := by
  apply finrank_le_two_of_zero_coordinate_kernel L (0,1) (1,3)
  intro V hV h01 h13
  apply nonstar1_normalized_zero V (hs V hV) h01 h13
  intro a b z
  have h := hp _ (L.add_mem (hc a b) (L.smul_mem z hV))
  simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_assoc] using h

lemma containing_nonstar2_plane_finrank_le_two
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hc : ∀ a b : ℂ, nonstarPlane2 a b ∈ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) : Module.finrank ℂ L ≤ 2 := by
  apply finrank_le_two_of_zero_coordinate_kernel L (0,1) (0,2)
  intro V hV h01 h02
  apply nonstar2_normalized_zero V (hs V hV) h01 h02
  intro a b z
  have h := hp _ (L.add_mem (hc a b) (L.smul_mem z hV))
  simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_assoc] using h

def canonicalHollowPlane (k : Fin 3) (a b : ℂ) : Fin 4 × Fin 4 → ℂ :=
  ![starMatrix a b,nonstarPlane1 a b,nonstarPlane2 a b] k

lemma containing_canonical_hollow_plane_finrank_le_two
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (k : Fin 3)
    (hc : ∀ a b : ℂ, canonicalHollowPlane k a b ∈ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) : Module.finrank ℂ L ≤ 2 := by
  fin_cases k
  · apply containing_star_plane_finrank_le_two L ?_ hs hp
    rintro V ⟨v,rfl⟩
    simpa [canonicalHollowPlane,starMap] using hc (v 0) (v 1)
  · apply containing_nonstar1_plane_finrank_le_two L ?_ hs hp
    intro a b
    simpa [canonicalHollowPlane] using hc a b
  · apply containing_nonstar2_plane_finrank_le_two L ?_ hs hp
    intro a b
    simpa [canonicalHollowPlane] using hc a b

lemma hollow_coefficient_cubic_zero (a b c d e f : ℂ)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+z*hollowMatrix a b c d e f i j)=24) : hollowCubic a b c d e f=0 := by
  obtain ⟨hs,_⟩ := hollow_coefficient_constraints a b c d e f hp
  have h₁ := hp 1
  have h₂ := hp (-1)
  rw [permanent_hollow_scaled] at h₁ h₂
  linear_combination h₁/2-h₂/2-12*hs

lemma hollow_member_cubic_zero (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hz : ∀ V ∈ L, ∀ i : Fin 4, V (i,i)=0)
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24)
    (V : Fin 4 × Fin 4 → ℂ) (hV : V ∈ L) :
    hollowCubic (V (0,1)) (V (0,2)) (V (0,3)) (V (1,2)) (V (1,3)) (V (2,3))=0 := by
  apply hollow_coefficient_cubic_zero
  intro z
  have h := hp (z • V) (L.smul_mem z hV)
  convert h using 1
  congr 1
  funext i j
  change 1+z*hollowMatrix _ _ _ _ _ _ i j=1+z*V (i,j)
  rw [hollow_reconstruction V (hs V hV) (hz V hV) i j]

end PEqualNP.Outside.L_gct_231
