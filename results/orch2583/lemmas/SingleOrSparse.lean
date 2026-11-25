import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.SingleOrSparse

open Finset

def Incidence {P L : ℕ} (I : Fin P → Fin L → Prop)
    (A : Finset (Fin P)) (B : Finset (Fin L)) : Prop :=
  ∃ p ∈ A, ∃ l ∈ B, I p l

/-- Distinct lines through a point need distinct other points to meet them. -/
theorem pencil_cover_card {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (unique : ∀ a b : Fin P, a ≠ b → ∃! l : Fin L, I a l ∧ I b l)
    (p : Fin P) (A : Finset (Fin P)) (absent : p ∉ A)
    (cover : ∀ l : Fin L, I p l → ∃ a ∈ A, I a l) :
    (Finset.univ.filter (I p)).card ≤ A.card := by
  classical
  let S := Finset.univ.filter (I p)
  have supply : ∀ l ∈ S, ∃ a ∈ A, I a l := by
    intro l hl
    exact cover l (Finset.mem_filter.mp hl).2
  choose a ha using supply
  exact Finset.card_le_card_of_injOn
    (fun l => if hl : l ∈ S then a l hl else p)
    (by
      intro l hl
      change l ∈ S at hl
      change (if hl : l ∈ S then a l hl else p) ∈ A
      rw [dite_eq_left hl]
      exact (ha l hl).1)
    (by
      intro l hl m hm equal
      change l ∈ S at hl
      change m ∈ S at hm
      change (if hl : l ∈ S then a l hl else p) =
        (if hm : m ∈ S then a m hm else p) at equal
      rw [dite_eq_left hl, dite_eq_left hm] at equal
      have neq : p ≠ a l hl := by
        intro heq
        exact absent (heq ▸ (ha l hl).1)
      obtain ⟨r, hr, only⟩ := unique p (a l hl) neq
      have el : l = r := only l ⟨(Finset.mem_filter.mp hl).2, (ha l hl).2⟩
      have em : m = r := only m ⟨(Finset.mem_filter.mp hm).2, by
        rw [equal]
        exact (ha m hm).2⟩
      exact el.trans em.symm)

/-- A semantic cut at the only reader of point p. The sibling h is independent
  of p; K is the remaining context with the reader output exposed. -/
theorem sibling_false_cover {P L : ℕ} (I : Fin P → Fin L → Prop)
    (p : Fin P)
    (h : Finset (Fin P) → Finset (Fin L) → Bool)
    (K : Finset (Fin P) → Finset (Fin L) → Bool → Bool)
    (context_mono : ∀ A A' B B' t, A ⊆ A' → B ⊆ B' →
      K A B t = true → K A' B' t = true)
    (sibling_mono : ∀ A B B', B ⊆ B' → h A B = true → h A B' = true)
    (spec : ∀ A B, Incidence I A B ↔
      K (A.erase p) B (decide (p ∈ A) || h (A.erase p) B) = true)
    (A : Finset (Fin P)) (B : Finset (Fin L))
    (absent : p ∉ A) (negative : ¬ Incidence I A B) (sibling : h A B = true) :
    ∀ l : Fin L, I p l → ∃ a ∈ A, I a l := by
  intro l hl
  have pair : Incidence I {p} {l} := ⟨p, by simp, l, by simp, hl⟩
  have initial : K ∅ {l} true = true := by
    simpa using (spec {p} {l}).mp pair
  have raised : K A (insert l B) true = true :=
    context_mono ∅ A {l} (insert l B) true (Finset.empty_subset _)
      (by intro j hj; rw [Finset.mem_singleton] at hj; subst j; exact Finset.mem_insert_self l B)
      initial
  have hs : h A (insert l B) = true :=
    sibling_mono A B (insert l B) (Finset.subset_insert _ _) sibling
  have positive : Incidence I A (insert l B) := (spec A (insert l B)).mpr (by
    simpa only [Finset.erase_eq_of_notMem absent, decide_eq_false_iff_not.mpr absent,
      Bool.false_or, hs] using raised)
  obtain ⟨a, ha, j, hj, haj⟩ := positive
  rcases Finset.mem_insert.mp hj with rfl | hj
  · exact ⟨a, ha, haj⟩
  · exact False.elim (negative ⟨a, ha, j, hj, haj⟩)

/-- Thus a false input accepted by the sibling has at least q+1 points. -/
theorem sibling_false_card {P L q : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (unique : ∀ a b : Fin P, a ≠ b → ∃! l : Fin L, I a l ∧ I b l)
    (p : Fin P) (degree : (Finset.univ.filter (I p)).card = q + 1)
    (h : Finset (Fin P) → Finset (Fin L) → Bool)
    (K : Finset (Fin P) → Finset (Fin L) → Bool → Bool)
    (context_mono : ∀ A A' B B' t, A ⊆ A' → B ⊆ B' →
      K A B t = true → K A' B' t = true)
    (sibling_mono : ∀ A B B', B ⊆ B' → h A B = true → h A B' = true)
    (spec : ∀ A B, Incidence I A B ↔
      K (A.erase p) B (decide (p ∈ A) || h (A.erase p) B) = true)
    (A : Finset (Fin P)) (B : Finset (Fin L))
    (absent : p ∉ A) (negative : ¬ Incidence I A B) (sibling : h A B = true) :
    q + 1 ≤ A.card := by
  rw [← degree]
  exact pencil_cover_card I unique p A absent
    (sibling_false_cover I p h K context_mono sibling_mono spec A B absent negative sibling)

end PEqualNP.Outside.L_meta_2583_aux.SingleOrSparse
