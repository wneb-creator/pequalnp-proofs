import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

lemma incident_star_support (b c d e : ℂ)
    (hbd : b*d=0) (hce : c*e=0) (hR : b*e+c*d=0) :
    (d=0 ∧ e=0) ∨ (b=0 ∧ c=0) := by
  by_cases hb : b=0
  · by_cases hc : c=0
    · exact Or.inr ⟨hb,hc⟩
    · have he : e=0 := (mul_eq_zero.mp hce).resolve_left hc
      have hd : d=0 := (mul_eq_zero.mp (by simpa [hb] using hR)).resolve_left hc
      exact Or.inl ⟨hd,he⟩
  · have hd : d=0 := (mul_eq_zero.mp hbd).resolve_left hb
    have he : e=0 := (mul_eq_zero.mp (by simpa [hd] using hR)).resolve_left hb
    exact Or.inl ⟨hd,he⟩

lemma incident_hollow_is_permuted_star (b c d e f : ℂ)
    (hf : f=0) (hbd : b*d=0) (hce : c*e=0) (hR : b*e+c*d=0)
    (hS : 1+b+c+d+e+f=0) :
    ∃ (σ : Equiv.Perm (Fin 4)) (a t : ℂ), starMatrix a t ≠ 0 ∧
      entryPermute σ (fun p => hollowMatrix 1 b c d e f p.1 p.2)=starMatrix a t := by
  rcases incident_star_support b c d e hbd hce hR with ⟨hd,he⟩ | ⟨hb,hc⟩
  · have hc : c = -1-b := by linear_combination hS-hd-he-hf
    refine ⟨Equiv.refl _,1,b,?_,?_⟩
    · intro h
      have hh := congrFun h (0,1)
      norm_num [starMatrix] at hh
    · funext p
      rcases p with ⟨i,j⟩
      fin_cases i <;> fin_cases j <;>
        simp [entryPermute,hollowMatrix,starMatrix,hc,hd,he,hf]
  · have he : e = -1-d := by linear_combination hS-hb-hc-hf
    refine ⟨Equiv.swap 0 1,1,d,?_,?_⟩
    · intro h
      have hh := congrFun h (0,1)
      norm_num [starMatrix] at hh
    · funext p
      rcases p with ⟨i,j⟩
      fin_cases i <;> fin_cases j <;>
        simp [entryPermute,Equiv.swap_apply_def,hollowMatrix,starMatrix,hb,hc,he,hf]

set_option maxHeartbeats 800000 in
lemma diagonal_edge_normalizing_permutation (i j k : Fin 4) (hjk : j ≠ k) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0=i ∧
      ((σ 0=j ∧ σ 1=k) ∨ (σ 0=k ∧ σ 1=j) ∨
       (σ 1=j ∧ σ 2=k) ∨ (σ 1=k ∧ σ 2=j)) := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first | exact False.elim (hjk rfl) | decide

lemma normalize_hollow_tracezero_pair
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (H V : Fin 4 × Fin 4 → ℂ)
    (hH : H ∈ L) (hV : V ∈ L) (hHne : H ≠ 0)
    (hHz : ∀ i : Fin 4, H (i,i)=0)
    (hHs : ∀ i j : Fin 4, H (i,j)=H (j,i))
    (hVdiag : ∃ i : Fin 4, V (i,i) ≠ 0)
    (hVtrace : (∑ i : Fin 4, V (i,i))=0) :
    ∃ σ : Equiv.Perm (Fin 4),
      ∃ A ∈ entryPermuteSubmodule σ L, ∃ B ∈ entryPermuteSubmodule σ L,
      A ≠ 0 ∧ (∀ i : Fin 4, A (i,i)=0) ∧
      (∑ i : Fin 4, B (i,i))=0 ∧ B (0,0)=1 ∧
      ((A (0,1)=1 ∧ B (0,1)=0) ∨ (A (1,2)=1 ∧ B (1,2)=0)) := by
  obtain ⟨i,hi⟩ := hVdiag
  have hex : ∃ j k : Fin 4, H (j,k) ≠ 0 := by
    by_contra he
    push Not at he
    apply hHne
    funext p
    exact he p.1 p.2
  obtain ⟨j,k,hjk⟩ := hex
  have hjkne : j ≠ k := by
    rintro rfl
    exact hjk (hHz j)
  obtain ⟨σ,hσ,hcases⟩ := diagonal_edge_normalizing_permutation i j k hjkne
  let H' := entryPermute σ H
  let V' := entryPermute σ V
  let L' := entryPermuteSubmodule σ L
  have hH' : H' ∈ L' := (entryPermute_mem_iff σ L H).mpr hH
  have hV' : V' ∈ L' := (entryPermute_mem_iff σ L V).mpr hV
  have hHz' : ∀ i : Fin 4, H' (i,i)=0 := entryPermute_hollow σ H hHz
  have hV00 : V' (0,0) ≠ 0 := by simpa [V',entryPermute_apply,hσ] using hi
  have hVtr : (∑ i : Fin 4, V' (i,i))=0 := by
    change (∑ i : Fin 4, V (σ i,σ i))=0
    exact (Equiv.sum_comp σ (fun i => V (i,i))).trans hVtrace
  have hpivot : H' (0,1) ≠ 0 ∨ H' (1,2) ≠ 0 := by
    rcases hcases with ⟨h0,h1⟩ | ⟨h0,h1⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩
    · left
      simpa [H',entryPermute_apply,h0,h1] using hjk
    · left
      simpa [H',entryPermute_apply,h0,h1,hHs k j] using hjk
    · right
      simpa [H',entryPermute_apply,h1,h2] using hjk
    · right
      simpa [H',entryPermute_apply,h1,h2,hHs k j] using hjk
  have make (p : Fin 4 × Fin 4) (hp : H' p ≠ 0) :
      ∃ A ∈ L', ∃ B ∈ L', A ≠ 0 ∧ (∀ i : Fin 4, A (i,i)=0) ∧
        (∑ i : Fin 4, B (i,i))=0 ∧ B (0,0)=1 ∧ A p=1 ∧ B p=0 := by
    let A := (H' p)⁻¹ • H'
    let B := (V' (0,0))⁻¹ • V' - ((V' (0,0))⁻¹*V' p) • A
    have hA : A ∈ L' := L'.smul_mem _ hH'
    have hB : B ∈ L' := L'.sub_mem (L'.smul_mem _ hV') (L'.smul_mem _ hA)
    have hAz : ∀ i : Fin 4, A (i,i)=0 := by intro i; simp [A,hHz']
    have hAp : A p=1 := by simp [A,hp]
    have hAne : A ≠ 0 := by
      intro he
      have hh := congrFun he p
      rw [hAp] at hh
      norm_num at hh
    have hBtr : (∑ i : Fin 4, B (i,i))=0 := by
      simp [B,hAz,← Finset.mul_sum,hVtr]
    have hB00 : B (0,0)=1 := by simp [B,hAz,hV00]
    have hBp : B p=0 := by simp [B,hAp]
    exact ⟨A,hA,B,hB,hAne,hAz,hBtr,hB00,hAp,hBp⟩
  rcases hpivot with h01 | h12
  · obtain ⟨A,hA,B,hB,hAne,hAz,hBtr,hB00,hAp,hBp⟩ := make (0,1) h01
    exact ⟨σ,A,hA,B,hB,hAne,hAz,hBtr,hB00,Or.inl ⟨hAp,hBp⟩⟩
  · obtain ⟨A,hA,B,hB,hAne,hAz,hBtr,hB00,hAp,hBp⟩ := make (1,2) h12
    exact ⟨σ,A,hA,B,hB,hAne,hAz,hBtr,hB00,Or.inr ⟨hAp,hBp⟩⟩

end PEqualNP.Outside.L_gct_231
