import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

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

end PEqualNP.Outside.L_gct_231
