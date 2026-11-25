import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2583

lemma lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
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
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

lemma incidence_no_four_cycle {N : ℕ} (I : Fin N → Fin N → Prop)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l') := by
  intro p p' l l' hp hl
  rintro ⟨hpl, hpl', hp'l, hp'l'⟩
  exact hl ((hu p p' hp).unique ⟨hpl, hp'l⟩ ⟨hpl', hp'l'⟩)

lemma lines_meet_at_most_once {N : ℕ} (I : Fin N → Fin N → Prop)
    [DecidableRel I]
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (l m : Fin N) (hlm : l ≠ m) :
    (Finset.univ.filter (fun p => I p l ∧ I p m)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_contra hab
  exact hlm ((hu a b hab).unique ⟨ha.1, hb.1⟩ ⟨ha.2, hb.2⟩)

lemma each_line_has_point {q N : ℕ} (I : Fin N → Fin N → Prop)
    [DecidableRel I]
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (l : Fin N) : ∃ p : Fin N, I p l := by
  have hpos : 0 < (Finset.univ.filter (fun p => I p l)).card := by rw [hl]; omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  exact ⟨p, (Finset.mem_filter.mp hp).2⟩

lemma each_point_has_line {q N : ℕ} (I : Fin N → Fin N → Prop)
    [DecidableRel I] (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) : ∃ l : Fin N, I p l := by
  have hpos : 0 < (Finset.univ.filter (fun l => I p l)).card := by
    rw [lines_through q N I hq hN hl hu p]
    omega
  obtain ⟨l, hl⟩ := Finset.card_pos.mp hpos
  exact ⟨l, (Finset.mem_filter.mp hl).2⟩

end PEqualNP.Outside.L_meta_2583
