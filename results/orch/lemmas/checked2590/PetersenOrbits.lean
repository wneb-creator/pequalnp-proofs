import PetersenGeometry

namespace PEqualNP.Outside.L_meta_2590_aux.Surplus

def IsAut (σ : Equiv.Perm (Fin 10)) : Prop := ∀ u v : Fin 10, Adj (σ u) (σ v) ↔ Adj u v

theorem pg_isAut_of {σ : Equiv.Perm (Fin 10)}
    (h : ∀ u v : Fin 10, pg_adjB (σ u) (σ v) = pg_adjB u v) : IsAut σ := fun u v => by
  rw [← pg_adjB_iff, ← pg_adjB_iff u v, h]

theorem isAut_one : IsAut 1 := fun _ _ => Iff.rfl

theorem isAut_mul {σ τ : Equiv.Perm (Fin 10)} (hσ : IsAut σ) (hτ : IsAut τ) : IsAut (σ * τ) :=
  fun u v => (hσ (τ u) (τ v)).trans (hτ u v)

theorem isAut_inv {σ : Equiv.Perm (Fin 10)} (hσ : IsAut σ) : IsAut σ⁻¹ := fun u v => by
  rw [Equiv.Perm.inv_def]
  have h := hσ (σ.symm u) (σ.symm v)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  exact h.symm
theorem indep_image_aut {σ : Equiv.Perm (Fin 10)} (hσ : IsAut σ) {I : Finset (Fin 10)}
    (hI : IsIndep I) : IsIndep (I.image σ) := by
  intro u hu v hv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
  rw [hσ a b]; exact hI a ha b hb

def canonI : List (Finset (Fin 10)) := [{0}, {0, 2}, {1, 3, 5}, {1, 4, 5}, {2, 4, 5, 6}]

def pg_rep (n : Fin 6) : Finset (Fin 10) := ((∅ : Finset (Fin 10)) :: canonI).getD n.val ∅

theorem pg_rep_of_mem {R : Finset (Fin 10)} (h : R ∈ canonI) :
    ∃ n : Fin 6, n ≠ 0 ∧ pg_rep n = R := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h
  have hi' : i < 5 := hi
  refine ⟨⟨i + 1, by omega⟩, by simp [Fin.ext_iff], ?_⟩
  show ((∅ : Finset (Fin 10)) :: canonI).getD (i + 1) ∅ = canonI[i]
  rw [List.getD_cons_succ]; exact List.getD_eq_getElem _ _ hi


abbrev pg_ind (I : Finset (Fin 10)) : Prop := ∀ u ∈ I, ∀ v ∈ I, pg_adjB u v = false

theorem pg_ind_iff {I : Finset (Fin 10)} : pg_ind I ↔ IsIndep I := by
  refine forall₂_congr fun u _ => forall₂_congr fun v _ => ?_
  rw [← pg_adjB_iff, Bool.not_eq_true]

theorem pg_rep_ind : ∀ n : Fin 6, pg_ind (pg_rep n) := by decide +kernel

theorem canonI_indep : ∀ R ∈ canonI, IsIndep R := by
  intro R h
  obtain ⟨n, -, rfl⟩ := pg_rep_of_mem h
  exact pg_ind_iff.mp (pg_rep_ind n)

def pg_ofList (l : List Nat) (v : Fin 10) : Fin 10 := Fin.ofNat 10 (l.getD v.val 0)
def pg_tab : List (List Nat) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [1, 0, 4, 3, 2, 6, 5, 9, 8, 7], [2, 1, 0, 4, 3, 7, 6, 5, 9, 8], [2, 3, 4, 0, 1, 7, 8, 9, 5, 6], [1, 2, 3, 4, 0, 6, 7, 8, 9, 5], [1, 2, 3, 8, 6, 0, 7, 4, 5, 9], [2, 1, 6, 8, 3, 7, 0, 9, 5, 4], [2, 3, 4, 9, 7, 1, 8, 0, 6, 5], [2, 3, 8, 5, 7, 1, 4, 6, 0, 9], [2, 3, 8, 6, 1, 7, 4, 5, 9, 0], [0, 4, 3, 2, 1, 5, 9, 8, 7, 6], [0, 1, 6, 8, 5, 4, 2, 9, 3, 7], [0, 4, 3, 8, 5, 1, 9, 2, 6, 7], [0, 4, 9, 7, 5, 1, 3, 6, 2, 8], [0, 4, 9, 6, 1, 5, 3, 7, 8, 2], [1, 0, 5, 8, 6, 2, 4, 7, 3, 9], [1, 0, 5, 7, 2, 6, 4, 8, 9, 3]]
def pg_fn (k : Fin 17) : Fin 10 → Fin 10 := pg_ofList (pg_tab.getD k.val [])

theorem pg_fn_inj : ∀ k : Fin 17, ∀ a b : Fin 10, pg_fn k a = pg_fn k b → a = b := by
  decide +kernel

theorem pg_fn_adj : ∀ k : Fin 17, ∀ u v : Fin 10,
    pg_adjB (pg_fn k u) (pg_fn k v) = pg_adjB u v := by decide +kernel

theorem pg_fn_aut (k : Fin 17) : ∃ τ : Equiv.Perm (Fin 10), IsAut τ ∧ ⇑τ = pg_fn k := by
  have hinj : Function.Injective (pg_fn k) := fun a b h => pg_fn_inj k a b h
  exact ⟨Equiv.ofBijective (pg_fn k) ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩,
    pg_isAut_of fun u v => pg_fn_adj k u v, rfl⟩

def pg_witTab : List (List Nat) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [0, 0, 0, 10, 0, 0, 11, 12, 13, 14], [0, 0, 0, 0, 0, 0, 1, 0, 15, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def pg_wit (n : Fin 6) (w : Fin 10) : Fin 17 := Fin.ofNat 17 ((pg_witTab.getD n.val []).getD w.val 0)
theorem pg_check : ∀ n : Fin 6, ∀ w : Fin 10, w ∉ pg_rep n →
    pg_ind (insert w (pg_rep n)) →
    (insert w (pg_rep n)).image (pg_fn (pg_wit n w)) ∈ canonI := by decide +kernel

theorem pg_step (R : Finset (Fin 10)) (hR : R = ∅ ∨ R ∈ canonI) (w : Fin 10) (hw : w ∉ R)
    (hI : IsIndep (insert w R)) :
    ∃ τ : Equiv.Perm (Fin 10), IsAut τ ∧ (insert w R).image τ ∈ canonI := by
  obtain ⟨n, rfl⟩ : ∃ n : Fin 6, pg_rep n = R := by
    rcases hR with rfl | hR
    · exact ⟨0, rfl⟩
    · obtain ⟨n, -, h⟩ := pg_rep_of_mem hR; exact ⟨n, h⟩
  obtain ⟨τ, hτ, he⟩ := pg_fn_aut (pg_wit n w)
  exact ⟨τ, hτ, by rw [he]; exact pg_check n w hw (pg_ind_iff.mpr hI)⟩

theorem pg_class (I : Finset (Fin 10)) : IsIndep I →
    I = ∅ ∨ ∃ σ : Equiv.Perm (Fin 10), IsAut σ ∧ I.image σ ∈ canonI := by
  induction I using Finset.induction_on with
  | empty => intro _; exact Or.inl rfl
  | insert v J hv ih =>
    intro hI
    have hJ : IsIndep J := fun u hu w hw =>
      hI u (Finset.mem_insert_of_mem hu) w (Finset.mem_insert_of_mem hw)
    obtain ⟨σ, hσ, R, hR, hJR⟩ : ∃ σ : Equiv.Perm (Fin 10), IsAut σ ∧
        ∃ R, (R = ∅ ∨ R ∈ canonI) ∧ J.image σ = R := by
      rcases ih hJ with h | ⟨σ, hσ, hm⟩
      · exact ⟨1, isAut_one, ∅, Or.inl rfl, by simp [h]⟩
      · exact ⟨σ, hσ, _, Or.inr hm, rfl⟩
    have h1 : (insert v J).image σ = insert (σ v) R := by rw [Finset.image_insert, hJR]
    have h2 : σ v ∉ R := by rw [← hJR]; simpa using hv
    have h3 : IsIndep (insert (σ v) R) := by rw [← h1]; exact indep_image_aut hσ hI
    obtain ⟨τ, hτ, hm⟩ := pg_step R hR (σ v) h2 h3
    refine Or.inr ⟨τ * σ, isAut_mul hτ hσ, ?_⟩
    rw [Equiv.Perm.coe_mul, ← Finset.image_image, h1]; exact hm


theorem indep_classification (I : Finset (Fin 10)) (hI : IsIndep I) (hne : I.Nonempty) :
    ∃ σ : Equiv.Perm (Fin 10), IsAut σ ∧ I.image σ ∈ canonI := by
  rcases pg_class I hI with h | h
  · exact absurd h hne.ne_empty
  · exact h

theorem indep_classification_card (I : Finset (Fin 10)) (hI : IsIndep I) (hne : I.Nonempty) :
    ∃ σ : Equiv.Perm (Fin 10), IsAut σ ∧ I.image σ ∈ canonI ∧ (I.image σ).card = I.card := by
  obtain ⟨σ, hσ, hm⟩ := indep_classification I hI hne
  exact ⟨σ, hσ, hm, Finset.card_image_of_injective _ σ.injective⟩


theorem canonI_cases (R : Finset (Fin 10)) (h : R ∈ canonI) :
  R = {0} ∨ R = {0, 2} ∨ R = {1, 3, 5} ∨ R = {1, 4, 5} ∨ R = {2, 4, 5, 6} := by
  simpa only [canonI, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using h

end PEqualNP.Outside.L_meta_2590_aux.Surplus
