import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

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

end PEqualNP.Outside.L_gct_231
