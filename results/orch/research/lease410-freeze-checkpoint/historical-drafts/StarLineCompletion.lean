import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

lemma star_line_cone (t : ℂ) (V : Fin 4 × Fin 4 → ℂ)
    (ht1 : t+1 ≠ 0) (ht2 : t+2 ≠ 0)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ a z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + starMatrix a (t*a) (i,j) +
        z * V (i,j)) = 24) :
    (starLineU t (V (1,2)) (V (1,3)) (V (2,2)) (V (2,3)))^2 =
      starLineV t (V (1,2)) (V (2,2)) (V (2,3)) *
      starLineW t (V (1,2)) (V (2,2)) (V (2,3)) := by
  obtain ⟨h1,h2,hq⟩ := star_line_constraints t V hs hp
  have hc := star_line_congruence t (V (1,1)) (V (1,2)) (V (1,3))
    (V (2,2)) (V (2,3)) (V (3,3)) ht1 ht2 h1 h2
  rw [hq] at hc
  linear_combination -hc / 2

lemma star_line_zero_coordinates (t : ℂ) (V : Fin 4 × Fin 4 → ℂ)
    (ht : t ≠ 0) (ht1 : t+1 ≠ 0) (ht2 : t+2 ≠ 0)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ a z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + starMatrix a (t*a) (i,j) +
        z * V (i,j)) = 24)
    (hU : starLineU t (V (1,2)) (V (1,3)) (V (2,2)) (V (2,3)) = 0)
    (hV : starLineV t (V (1,2)) (V (2,2)) (V (2,3)) = 0)
    (hW : starLineW t (V (1,2)) (V (2,2)) (V (2,3)) = 0) :
    V = starMatrix (V (0,1)) (V (0,2)) := by
  obtain ⟨h1,h2,_⟩ := star_line_constraints t V hs hp
  have hb := star_line_coordinate_kernel t (V (1,1)) (V (1,2)) (V (1,3))
    (V (2,2)) (V (2,3)) (V (3,3)) ht ht1 ht2 h1 h2 hU hV hW
  apply constant_lower_block_is_star V hs hb
  intro z
  have hzstar : starMatrix (0 : ℂ) (t*0) = 0 := by
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [starMatrix]
  simpa only [hzstar, Pi.zero_apply, add_zero] using hp 0 z

def starConePair : LinearMap.BilinForm ℂ (Fin 3 → ℂ) :=
  LinearMap.mk₂ ℂ (fun v w => 2*v 0*w 0-v 1*w 2-v 2*w 1)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)

lemma starConePair_symmetric (v w : Fin 3 → ℂ) :
    starConePair v w = starConePair w v := by
  simp only [starConePair, LinearMap.mk₂_apply]
  ring

lemma starConePair_nondegenerate : starConePair.Nondegenerate := by
  have hleft : ∀ v, (∀ w, starConePair v w = 0) → v = 0 := by
    intro v h
    have h₀ : v 0 = 0 := by
      have hz := h ![1,0,0]
      simp [starConePair] at hz
      exact hz
    have h₁ : v 1 = 0 := by simpa [starConePair] using h ![0,0,1]
    have h₂ : v 2 = 0 := by simpa [starConePair] using h ![0,1,0]
    funext i
    fin_cases i <;> simp_all
  exact ⟨hleft, fun v h => hleft v fun w => (starConePair_symmetric v w).trans (h w)⟩

lemma star_cone_finrank_le_one (W : Submodule ℂ (Fin 3 → ℂ))
    (hq : ∀ v ∈ W, (v 0)^2 = v 1*v 2) : Module.finrank ℂ W ≤ 1 := by
  have hle : W ≤ starConePair.orthogonal W := by
    intro v hv w hw
    have hvq := hq v hv
    have hwq := hq w hw
    have hav := hq (v+w) (W.add_mem hv hw)
    simp only [Pi.add_apply] at hav
    simp only [starConePair, LinearMap.mk₂_apply]
    linear_combination hav - hvq - hwq
  have hd := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal starConePair_nondegenerate] at hd
  have hdim : Module.finrank ℂ (Fin 3 → ℂ) = 3 := by simp
  rw [hdim] at hd
  omega

def starLineCoordinates (t : ℂ) : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun V := ![starLineU t (V (1,2)) (V (1,3)) (V (2,2)) (V (2,3)),
    starLineV t (V (1,2)) (V (2,2)) (V (2,3)),
    starLineW t (V (1,2)) (V (2,2)) (V (2,3))]
  map_add' := by
    intro V W
    ext k
    fin_cases k <;> simp [starLineU,starLineV,starLineW] <;> ring
  map_smul' := by
    intro c V
    ext k
    fin_cases k <;> simp [starLineU,starLineV,starLineW] <;> ring

lemma star_line_closed_family (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (t : ℂ) (hA : starMatrix 1 t ∈ L)
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + V (i,j)) = 24)
    (V : Fin 4 × Fin 4 → ℂ) (hV : V ∈ L) (a z : ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1 + starMatrix a (t*a) (i,j) + z * V (i,j)) = 24 := by
  have heq : (fun p => starMatrix a (t*a) p + z * V p) =
      a • starMatrix 1 t + z • V := by
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [starMatrix] <;> ring
  have hm : (fun p => starMatrix a (t*a) p + z * V p) ∈ L := by
    rw [heq]
    exact L.add_mem (L.smul_mem a hA) (L.smul_mem z hV)
  simpa only [add_assoc] using hp _ hm

lemma star_line_image_finrank_le_one (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (t : ℂ) (ht1 : t+1 ≠ 0) (ht2 : t+2 ≠ 0)
    (hA : starMatrix 1 t ∈ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + V (i,j)) = 24) :
    Module.finrank ℂ (L.map (starLineCoordinates t)) ≤ 1 := by
  apply star_cone_finrank_le_one
  rintro v ⟨V,hV,rfl⟩
  simpa [starLineCoordinates] using star_line_cone t V ht1 ht2 (hs V hV)
    (star_line_closed_family L t hA hp V hV)

lemma star_line_kernel_is_star (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (t : ℂ) (ht : t ≠ 0) (ht1 : t+1 ≠ 0) (ht2 : t+2 ≠ 0)
    (hA : starMatrix 1 t ∈ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + V (i,j)) = 24) :
    L ⊓ LinearMap.ker (starLineCoordinates t) ≤ LinearMap.range starMap := by
  rintro V ⟨hV,hker⟩
  have hh : starLineCoordinates t V = 0 := hker
  have hU := congrFun hh 0
  have hV' := congrFun hh 1
  have hW := congrFun hh 2
  simp [starLineCoordinates] at hU hV' hW
  have hstar := star_line_zero_coordinates t V ht ht1 ht2 (hs V hV)
    (star_line_closed_family L t hA hp V hV) hU hV' hW
  refine ⟨![V (0,1),V (0,2)],?_⟩
  simpa [starMap] using hstar.symm

lemma containing_star_plane_finrank_le_two (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hstar : LinearMap.range starMap ≤ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + V (i,j)) = 24) :
    Module.finrank ℂ L ≤ 2 := by
  have hle : L ≤ LinearMap.range starMap := by
    intro V hV
    have heq : V = starMatrix (V (0,1)) (V (0,2)) := by
      apply star_two_plane_maximal V (hs V hV)
      intro a b z
      have hm : starMatrix a b ∈ L := hstar ⟨![a,b],by simp [starMap]⟩
      have hz := hp _ (L.add_mem hm (L.smul_mem z hV))
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_assoc] using hz
    refine ⟨![V (0,1),V (0,2)],?_⟩
    simpa [starMap] using heq.symm
  have hd := Submodule.finrank_mono hle
  simpa only [starMap_finrank] using hd

lemma finrank_le_two_of_small_image
    (L S : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (F : L →ₗ[ℂ] (Fin 3 → ℂ))
    (hS : Module.finrank ℂ S = 2)
    (hrange : Module.finrank ℂ (LinearMap.range F) ≤ 1)
    (hker : (LinearMap.ker F).map L.subtype ≤ S)
    (hmax : S ≤ L → Module.finrank ℂ L ≤ 2) : Module.finrank ℂ L ≤ 2 := by
  have hkdim : Module.finrank ℂ (LinearMap.ker F) ≤ 2 := by
    have h := Submodule.finrank_mono hker
    simpa only [Submodule.finrank_map_subtype_eq, hS] using h
  by_cases hk : Module.finrank ℂ (LinearMap.ker F) ≤ 1
  · have hn := F.finrank_range_add_finrank_ker
    omega
  · have hk2 : Module.finrank ℂ (LinearMap.ker F) = 2 := by omega
    have heq : (LinearMap.ker F).map L.subtype = S :=
      Submodule.eq_of_le_of_finrank_eq hker (by
        rw [Submodule.finrank_map_subtype_eq, hk2, hS])
    have hsL : S ≤ L := by
      rw [← heq]
      rintro x ⟨y, hy, rfl⟩
      exact y.property
    exact hmax hsL

lemma containing_generic_star_line_finrank_le_two
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (t : ℂ) (ht : t ≠ 0) (ht1 : t+1 ≠ 0) (ht2 : t+2 ≠ 0)
    (hA : starMatrix 1 t ∈ L)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + V (i,j)) = 24) :
    Module.finrank ℂ L ≤ 2 := by
  apply finrank_le_two_of_small_image L (LinearMap.range starMap)
    ((starLineCoordinates t).domRestrict L) starMap_finrank
  · rw [LinearMap.range_domRestrict]
    exact star_line_image_finrank_le_one L t ht1 ht2 hA hs hp
  · rintro V ⟨v,hv,rfl⟩
    apply star_line_kernel_is_star L t ht ht1 ht2 hA hs hp
    exact ⟨v.property,hv⟩
  · intro hstar
    exact containing_star_plane_finrank_le_two L hstar hs hp

end PEqualNP.Outside.L_gct_231
