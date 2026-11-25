import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2732_aux.SelectedLabels

noncomputable def labels {α : Type*} [DecidableEq α] (k d : ℕ)
    (S : ℕ → Finset α) (Z : Finset α) (C : ℕ → Finset ℕ)
    (earlier : ∀ w q, q ∈ C w → q < w) (w : ℕ) : Finset α :=
  if w = d then Z else if w < k then S w else
    (C w).attach.biUnion fun q => labels k d S Z C earlier q.1
termination_by w
decreasing_by exact earlier _ _ q.2

lemma labels_dirty {α : Type*} [DecidableEq α] (k d : ℕ)
    (S : ℕ → Finset α) (Z : Finset α) (C : ℕ → Finset ℕ)
    (earlier : ∀ w q, q ∈ C w → q < w) :
    labels k d S Z C earlier d = Z := by
  rw [labels, ite_eq_left rfl]

lemma labels_base {α : Type*} [DecidableEq α] (k d : ℕ)
    (S : ℕ → Finset α) (Z : Finset α) (C : ℕ → Finset ℕ)
    (earlier : ∀ w q, q ∈ C w → q < w) (hdk : k ≤ d)
    (w : ℕ) (hw : w < k) : labels k d S Z C earlier w = S w := by
  have hwd : w ≠ d := by omega
  rw [labels, ite_eq_right hwd, ite_eq_left hw]

lemma child_label_subset {α : Type*} [DecidableEq α] (k d : ℕ)
    (S : ℕ → Finset α) (Z : Finset α) (C : ℕ → Finset ℕ)
    (earlier : ∀ w q, q ∈ C w → q < w)
    (base_empty : ∀ w < k, C w = ∅) (dirty_empty : C d = ∅)
    (w q : ℕ) (hq : q ∈ C w) :
    labels k d S Z C earlier q ⊆ labels k d S Z C earlier w := by
  have hwd : w ≠ d := by intro h; subst w; simp [dirty_empty] at hq
  have hwk : ¬ w < k := by intro h; simp [base_empty w h] at hq
  have heq : labels k d S Z C earlier w =
      (C w).attach.biUnion fun p => labels k d S Z C earlier p.1 := by
    rw [labels, ite_eq_right hwd, ite_eq_right hwk]
  rw [heq]
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨⟨q, hq⟩, Finset.mem_attach _ _, hx⟩

lemma labels_internal_subset {α : Type*} [DecidableEq α] (k d : ℕ)
    (S : ℕ → Finset α) (Z : Finset α) (C : ℕ → Finset ℕ)
    (earlier : ∀ w q, q ∈ C w → q < w)
    (base_empty : ∀ w < k, C w = ∅) (dirty_empty : C d = ∅)
    (w : ℕ) (hw : C w ≠ ∅) :
    labels k d S Z C earlier w ⊆ (C w).biUnion (labels k d S Z C earlier) := by
  have hwd : w ≠ d := by intro h; subst w; exact hw dirty_empty
  have hwk : ¬ w < k := by intro h; exact hw (base_empty w h)
  have heq : labels k d S Z C earlier w =
      (C w).attach.biUnion fun p => labels k d S Z C earlier p.1 := by
    rw [labels, ite_eq_right hwd, ite_eq_right hwk]
  rw [heq]
  intro x hx
  obtain ⟨p, _, hxp⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨p.1, p.2, hxp⟩

lemma labels_leaf_small {α : Type*} [DecidableEq α] (k d : ℕ)
    (S : ℕ → Finset α) (Z : Finset α) (C : ℕ → Finset ℕ)
    (earlier : ∀ w q, q ∈ C w → q < w)
    (small : ∀ w < k, (S w).card ≤ 1)
    (w : ℕ) (hw : C w = ∅) (hwd : w ≠ d) :
    (labels k d S Z C earlier w).card ≤ 1 := by
  by_cases hwk : w < k
  · rw [labels, ite_eq_right hwd, ite_eq_left hwk]
    exact small w hwk
  · rw [labels, ite_eq_right hwd, ite_eq_right hwk]
    have hempty : ((C w).attach.biUnion fun q => labels k d S Z C earlier q.1) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      obtain ⟨q, _, _⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨q, hq⟩ := q
      exact Finset.notMem_empty q (hw ▸ hq)
    rw [hempty, Finset.card_empty]
    omega

end PEqualNP.Outside.L_meta_2732_aux.SelectedLabels
