import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_meta_2583

lemma plane_point_degree (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, Nat.nsmul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

lemma incidence_card_left {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    ((A ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)).card
      = ∑ p ∈ A, (B.filter (fun w => I p w)).card := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.card_filter]

lemma incidence_card_right {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    ((A ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)).card
      = ∑ w ∈ B, (A.filter (fun p => I p w)).card := by
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.card_filter]

lemma regular_cover_card {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpt : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (A B : Finset (Fin N)) (hc : ∀ p w : Fin N, I p w → p ∈ A ∨ w ∈ B) :
    N ≤ A.card + B.card := by
  have hE : (((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = N * (q + 1) := by
    rw [incidence_card_right, Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, Nat.nsmul_eq_mul]
  have hA : ((A ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = A.card * (q + 1) := by
    rw [incidence_card_left, Finset.sum_congr rfl (fun p _ => hpt p), Finset.sum_const, Nat.nsmul_eq_mul]
  have hB : (((Finset.univ : Finset (Fin N)) ×ˢ B).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = B.card * (q + 1) := by
    rw [incidence_card_right, Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_const, Nat.nsmul_eq_mul]
  have hsub : ((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)
      ⊆ ((A ×ˢ (Finset.univ : Finset (Fin N))).filter (fun pw : Fin N × Fin N => I pw.1 pw.2))
        ∪ (((Finset.univ : Finset (Fin N)) ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)) := by
    rintro ⟨p, w⟩ h
    have hI : I p w := (Finset.mem_filter.mp h).2
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product]
    rcases hc p w hI with h1 | h1
    · exact Or.inl ⟨⟨h1, Finset.mem_univ _⟩, hI⟩
    · exact Or.inr ⟨⟨Finset.mem_univ _, h1⟩, hI⟩
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [hE, hA, hB, ← Nat.add_mul] at h
  exact Nat.le_of_mul_le_mul_right h (Nat.succ_pos q)

lemma plane_cover_card (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N)) (hcover : ∀ p l : Fin N, I p l → p ∈ A ∨ l ∈ B) :
    N ≤ A.card + B.card := by
  exact regular_cover_card q I hL (plane_point_degree q N I hq hN hL hU) A B hcover

lemma regular_incidence_matching (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hL : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hP : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1) :
    ∃ f : Fin N → Fin N, Function.Injective f ∧ ∀ p, I p (f p) := by
  classical
  let adj (p : Fin N) : Finset (Fin N) := Finset.univ.filter fun l => I p l
  have hall (S : Finset (Fin N)) : S.card ≤ (S.biUnion adj).card := by
    have hcover : ∀ p l : Fin N, I p l → p ∈ Finset.univ \ S ∨ l ∈ S.biUnion adj := by
      intro p l hpl
      by_cases hp : p ∈ S
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩⟩)
      · exact Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hp⟩)
    have h := regular_cover_card q I hL hP (Finset.univ \ S) (S.biUnion adj) hcover
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  obtain ⟨f, hf, ha⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' adj).mp hall
  exact ⟨f, hf, fun p => (Finset.mem_filter.mp (ha p)).2⟩

lemma plane_incidence_matching (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∃ f : Fin N → Fin N, Function.Injective f ∧ ∀ p, I p (f p) := by
  exact regular_incidence_matching q N I hL (plane_point_degree q N I hq hN hL hU)

lemma plane_incidence_perm (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∃ σ : Equiv.Perm (Fin N), ∀ p, I p (σ p) := by
  classical
  obtain ⟨f, hf, hi⟩ := plane_incidence_matching q N I hq hN hL hU
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, rfl⟩), hi⟩

lemma plane_no_rectangle (N : ℕ) (I : Fin N → Fin N → Prop)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬(I p l ∧ I p l' ∧ I p' l ∧ I p' l') := by
  rintro p p' l l' hp hl ⟨hpl, hpl', hp'l, hp'l'⟩
  exact hl ((hU p p' hp).unique ⟨hpl, hp'l⟩ ⟨hpl', hp'l'⟩)

lemma plane_matching_edges (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∃ M : Finset (Fin N × Fin N),
      (∀ e ∈ M, I e.1 e.2) ∧
      (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) ∧
      (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) ∧ M.card = N := by
  classical
  obtain ⟨σ, hσ⟩ := plane_incidence_perm q N I hq hN hL hU
  let pair (p : Fin N) : Fin N × Fin N := (p, σ p)
  have hi : Function.Injective pair := fun _ _ h => congrArg Prod.fst h
  refine ⟨Finset.univ.image pair, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    exact hσ p
  · intro e he f hf heq
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨p', _, rfl⟩ := Finset.mem_image.mp hf
    exact congrArg pair heq
  · intro e he f hf heq
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨p', _, rfl⟩ := Finset.mem_image.mp hf
    exact congrArg pair (σ.injective heq)
  · simp [Finset.card_image_of_injective _ hi]

end PEqualNP.Outside.L_meta_2583
