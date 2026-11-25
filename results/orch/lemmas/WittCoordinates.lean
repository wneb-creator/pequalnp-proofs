import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

def hollowWittCoordinates : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ) where
  toFun V := ![V (0,1)-V (1,2),V (0,2)-V (1,2),
    V (2,3)-V (1,2),V (1,3)-V (1,2),V (1,2)]
  map_add' := by intros; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intros; ext i; fin_cases i <;> simp <;> ring

def wittMatrix : (Fin 5 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun u := fun p => hollowMatrix (u 0+u 4) (u 1+u 4)
    (-u 0-u 1-u 2-u 3-5*u 4) (u 4) (u 3+u 4) (u 2+u 4) p.1 p.2
  map_add' := by
    intros
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [hollowMatrix] <;> ring
  map_smul' := by
    intros
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [hollowMatrix] <;> ring

def wittCubic (u : Fin 5 → ℂ) : ℂ :=
  hollowCubic (u 0+u 4) (u 1+u 4) (-u 0-u 1-u 2-u 3-5*u 4)
    (u 4) (u 3+u 4) (u 2+u 4)

lemma hollowWittCoordinates_wittMatrix (u : Fin 5 → ℂ) :
    hollowWittCoordinates (wittMatrix u)=u := by
  funext i
  fin_cases i <;> simp [hollowWittCoordinates,wittMatrix,hollowMatrix]

lemma wittMatrix_hollowWittCoordinates (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j)=V (j,i)) (hz : ∀ i : Fin 4, V (i,i)=0)
    (hS : V (0,1)+V (0,2)+V (0,3)+V (1,2)+V (1,3)+V (2,3)=0) :
    wittMatrix (hollowWittCoordinates V)=V := by
  funext p
  rcases p with ⟨i,j⟩
  change hollowMatrix _ _ _ _ _ _ i j=V (i,j)
  rw [hollow_reconstruction V hs hz i j]
  fin_cases i <;> fin_cases j <;>
    simp [hollowWittCoordinates,hollowMatrix] <;>
    solve
    | ring
    | linear_combination hS
    | linear_combination -hS

lemma wittQ_hollowWittCoordinates (V : Fin 4 × Fin 4 → ℂ)
    (hS : V (0,1)+V (0,2)+V (0,3)+V (1,2)+V (1,3)+V (2,3)=0) :
    wittQ (hollowWittCoordinates V)=V (0,1)*V (2,3)+V (0,2)*V (1,3)+V (0,3)*V (1,2) := by
  dsimp [wittQ,hollowWittCoordinates]
  linear_combination -V (1,2)*hS

lemma wittCubic_eq_matrix_cubic (u : Fin 5 → ℂ) :
    wittCubic u=hollowCubic ((wittMatrix u) (0,1)) ((wittMatrix u) (0,2))
      ((wittMatrix u) (0,3)) ((wittMatrix u) (1,2)) ((wittMatrix u) (1,3))
      ((wittMatrix u) (2,3)) := by simp [wittCubic,wittMatrix,hollowMatrix]

lemma hollow_witt_image_finrank
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hz : ∀ V ∈ L, ∀ i : Fin 4, V (i,i)=0)
    (hS : ∀ V ∈ L, V (0,1)+V (0,2)+V (0,3)+V (1,2)+V (1,3)+V (2,3)=0) :
    Module.finrank ℂ (L.map hollowWittCoordinates)=Module.finrank ℂ L := by
  let F := hollowWittCoordinates.domRestrict L
  have hF : Function.Injective F := by
    intro V W h
    apply Subtype.ext
    change hollowWittCoordinates V.val=hollowWittCoordinates W.val at h
    have hV := wittMatrix_hollowWittCoordinates V.val (hs _ V.property)
      (hz _ V.property) (hS _ V.property)
    have hW := wittMatrix_hollowWittCoordinates W.val (hs _ W.property)
      (hz _ W.property) (hS _ W.property)
    rw [← hV,← hW,h]
  have hd := LinearMap.finrank_range_of_inj hF
  change Module.finrank ℂ (LinearMap.range (hollowWittCoordinates.domRestrict L))=
    Module.finrank ℂ L at hd
  rw [LinearMap.range_domRestrict] at hd
  exact hd

lemma hollow_witt_image_constraints
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hz : ∀ V ∈ L, ∀ i : Fin 4, V (i,i)=0)
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    (∀ u ∈ L.map hollowWittCoordinates, wittQ u=0) ∧
    (∀ u ∈ L.map hollowWittCoordinates, wittCubic u=0) := by
  constructor
  · rintro u ⟨V,hV,rfl⟩
    obtain ⟨hS,hq⟩ := hollow_member_constraints L hs hz hp V hV
    rw [wittQ_hollowWittCoordinates V hS]
    exact hq
  · rintro u ⟨V,hV,rfl⟩
    have hS := (hollow_member_constraints L hs hz hp V hV).1
    rw [wittCubic_eq_matrix_cubic,
      wittMatrix_hollowWittCoordinates V (hs _ hV) (hz _ hV) hS]
    exact hollow_member_cubic_zero L hs hz hp V hV

lemma witt_polar_zero_of_submodule (W : Submodule ℂ (Fin 5 → ℂ))
    (hq : ∀ u ∈ W, wittQ u=0) (u v : Fin 5 → ℂ) (hu : u ∈ W) (hv : v ∈ W) :
    wittPolar u v=0 := by
  have h₁ := hq u hu
  have h₂ := hq v hv
  have h₃ := hq (u+v) (W.add_mem hu hv)
  dsimp [wittQ,wittPolar] at h₁ h₂ h₃ ⊢
  linear_combination h₃-h₁-h₂

lemma witt_submodule_has_triangle_chart (W : Submodule ℂ (Fin 5 → ℂ))
    (hq : ∀ u ∈ W, wittQ u=0) (hd : 2 ≤ Module.finrank ℂ W) :
    ∃ u ∈ W, ∃ v ∈ W, ∃ k : Fin 4, wittTriangleMinor u v k ≠ 0 := by
  obtain ⟨f,hf⟩ := exists_linearIndependent_of_le_finrank hd
  have hi := hf.map_injOn W.subtype (fun _ _ _ _ h => Subtype.ext h)
  have heq : W.subtype ∘ f=![((f 0).val),((f 1).val)] := by
    funext i
    fin_cases i <;> rfl
  rw [heq] at hi
  refine ⟨(f 0).val,(f 0).property,(f 1).val,(f 1).property,?_⟩
  apply hollow_triangle_covers_independent_pair _ _ (hq _ (f 0).property)
    (hq _ (f 1).property) ?_ hi
  exact witt_polar_zero_of_submodule W hq _ _ (f 0).property (f 1).property

def evenChartVector (A B K s t : ℂ) : Fin 5 → ℂ :=
  ![s,t,3*A*(A*s+B*t)+K*t,3*B*(A*s+B*t)-K*s,A*s+B*t]

lemma evenChartVector_linear_combination (A B K s t : ℂ) :
    evenChartVector A B K s t =
      s • ![1,0,3*A^2,3*A*B-K,A]+t • ![0,1,3*A*B+K,3*B^2,B] := by
  funext i
  fin_cases i <;> simp [evenChartVector] <;> ring

set_option maxHeartbeats 4000000 in
lemma wittCubic_evenChartVector (A B K s t : ℂ) :
    wittCubic (evenChartVector A B K s t) =
      -2*((A+1)*ogrG A B K*s^3+ogrF A B K*s^2*t+
        ogrF B A (-K)*s*t^2+(B+1)*ogrG B A (-K)*t^3) := by
  simp [wittCubic,evenChartVector,hollowCubic,ogrG,ogrF]
  ring

lemma even_chart_cubic_classification (A B K : ℂ)
    (hc : ∀ s t : ℂ, wittCubic (evenChartVector A B K s t)=0) :
    ogrEvenRoots A B K := by
  have h10 := hc 1 0
  have h01 := hc 0 1
  have h11 := hc 1 1
  have h1m := hc 1 (-1)
  rw [wittCubic_evenChartVector] at h10 h01 h11 h1m
  apply hollow_even_chart_classification A B K
  · linear_combination -h10/2
  · linear_combination (h1m-h11)/4+h01/2
  · linear_combination -(h11+h1m)/4+h10/2
  · linear_combination -h01/2

lemma isotropic_normalized_pair_classified (W : Submodule ℂ (Fin 5 → ℂ))
    (hq : ∀ u ∈ W, wittQ u=0) (hc : ∀ u ∈ W, wittCubic u=0)
    (u v : Fin 5 → ℂ) (hu : u ∈ W) (hv : v ∈ W)
    (hu0 : u 0=1) (hu1 : u 1=0) (hv0 : v 0=0) (hv1 : v 1=1) :
    ∃ A B K : ℂ, ogrEvenRoots A B K ∧
      u=![1,0,3*A^2,3*A*B-K,A] ∧ v=![0,1,3*A*B+K,3*B^2,B] := by
  obtain ⟨A,B,K,hU,hV⟩ := isotropic_even_chart_normal_form u v hu0 hu1 hv0 hv1
    (hq u hu) (hq v hv) (witt_polar_zero_of_submodule W hq u v hu hv)
  refine ⟨A,B,K,?_,hU,hV⟩
  apply even_chart_cubic_classification A B K
  intro s t
  apply hc
  rw [evenChartVector_linear_combination,← hU,← hV]
  exact W.add_mem (W.smul_mem s hu) (W.smul_mem t hv)

end PEqualNP.Outside.L_gct_231
