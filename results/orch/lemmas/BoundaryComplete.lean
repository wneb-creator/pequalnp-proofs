import Mathlib

namespace PEqualNP.Outside.L_meta_2028.Boundary

lemma independent_extend {n : ℕ} (G : SimpleGraph (Fin n))
    (I : Finset (Fin n))
    (hI : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) :
    ∃ J : Finset (Fin n), I ⊆ J ∧
      (∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v) ∧
      ∀ u, u ∉ J → ∃ v ∈ J, G.Adj u v := by
  classical
  let A : Finset (Finset (Fin n)) := Finset.univ.filter fun J =>
    I ⊆ J ∧ ∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v
  have hA : A.Nonempty := by
    refine ⟨I, ?_⟩
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Finset.Subset.refl _, hI⟩
  obtain ⟨J, hJ, hmax⟩ := Finset.exists_max_image A Finset.card hA
  have hJ' : I ⊆ J ∧ ∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v :=
    (Finset.mem_filter.mp hJ).2
  refine ⟨J, hJ'.1, hJ'.2, ?_⟩
  intro u hu
  by_contra! hn
  have hins : ∀ a ∈ insert u J, ∀ b ∈ insert u J, ¬ G.Adj a b := by
    intro a ha b hb
    by_cases hau : a = u
    · subst a
      by_cases hbu : b = u
      · subst b
        exact G.loopless.irrefl u
      · exact hn b (by simpa only [Finset.mem_insert, hbu, false_or] using hb)
    · have haJ : a ∈ J := by
        simpa only [Finset.mem_insert, hau, false_or] using ha
      by_cases hbu : b = u
      · subst b
        exact fun hadj => hn a haJ hadj.symm
      · exact hJ'.2 a haJ b (by simpa only [Finset.mem_insert, hbu, false_or] using hb)
  have hmem : insert u J ∈ A := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hJ'.1.trans (Finset.subset_insert _ _), hins⟩
  have hcard := hmax (insert u J) hmem
  rw [Finset.card_insert_of_notMem hu] at hcard
  omega

lemma complete {n : ℕ} (G : SimpleGraph (Fin n))
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hedge : ∀ u v, G.Adj u v →
      f (fun i => decide (i = u ∨ i = v)) = true)
    (hind : ∀ I : Finset (Fin n),
      (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) →
      (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
      f (fun i => decide (i ∈ I)) = false) :
    ∀ x : Fin n → Bool,
      f x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  classical
  intro x
  constructor
  · intro hx
    by_contra! hno
    let I : Finset (Fin n) := Finset.univ.filter fun i => x i = true
    have hI : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v := by
      intro u hu v hv hadj
      exact hno u v hadj (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2
    obtain ⟨J, hIJ, hJ, hmax⟩ := independent_extend G I hI
    have hup : ∀ i, x i = true → decide (i ∈ J) = true := by
      intro i hi
      exact decide_eq_true (hIJ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
    have htrue := hmono x (fun i => decide (i ∈ J)) hup hx
    have hfalse := hind J hJ hmax
    rw [hfalse] at htrue
    cases htrue
  · rintro ⟨u, v, hadj, hu, hv⟩
    apply hmono (fun i => decide (i = u ∨ i = v)) x
    · intro i hi
      rcases of_decide_eq_true hi with rfl | rfl
      · exact hu
      · exact hv
    · exact hedge u v hadj

end PEqualNP.Outside.L_meta_2028.Boundary
