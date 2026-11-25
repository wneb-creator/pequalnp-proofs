import MixedCoverGap
namespace PEqualNP.Outside.L_meta_2583.PlaneGeometry

def rectangleHits {N : Nat} (I : Fin N → Fin N → Prop) (p l : Fin N)
    (A B : Finset (Fin N)) : Prop :=
  (∃ a ∈ A, I a l) ∧ (∃ b ∈ B, I p b)

def hasIncidence {N : Nat} (I : Fin N → Fin N → Prop)
    (A B : Finset (Fin N)) : Prop := ∃ a ∈ A, ∃ b ∈ B, I a b

lemma rectangle_point_center {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p l : Fin N) (edge : I p l) (r : Fin N) :
    (∀ A B : Finset (Fin N), rectangleHits I p l A B → r ∈ A → hasIncidence I A B) ↔ r = p := by
  constructor
  · intro safe
    by_contra rp
    obtain ⟨m, hm, unique⟩ := hu p r (Ne.symm rp)
    have fresh : ∃ b : Fin N, I p b ∧ b ≠ l ∧ b ≠ m := by
      by_contra! no
      have sub : Finset.univ.filter (fun b => I p b) ⊆ ({l, m} : Finset (Fin N)) := by
        intro b hb
        have pb := (Finset.mem_filter.mp hb).2
        by_cases eq : b = l
        · simp [eq]
        · have eqm := no b pb eq
          simp [eqm]
      have bound := Finset.card_le_card sub
      rw [lines_through q N I (by omega) hN hl hu p] at bound
      have pair : ({l, m} : Finset (Fin N)).card ≤ 2 := by
        by_cases lm : l = m <;> simp [lm]
      omega
    obtain ⟨b, pb, bl, bm⟩ := fresh
    have rb : ¬ I r b := fun rb => bm (unique b ⟨pb, rb⟩)
    have ac : ((Finset.univ.filter (fun a => I a l)).erase p).card = q := by
      rw [Finset.card_erase_of_mem (by simp [edge]), hl l]
      rfl
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < ((Finset.univ.filter (fun a => I a l)).erase p).card by omega)
    have ap : a ≠ p := Finset.ne_of_mem_erase ha
    have al : I a l := (Finset.mem_filter.mp (Finset.mem_erase.mp ha).2).2
    have ab : ¬ I a b := fun ab => bl ((hu p a ap.symm).unique ⟨pb, ab⟩ ⟨edge, al⟩)
    have bad := safe {a, r} {b} ⟨⟨a, by simp, al⟩, ⟨b, by simp, pb⟩⟩ (by simp)
    obtain ⟨x, hx, y, hy, xy⟩ := bad
    simp only [Finset.mem_singleton] at hy
    subst y
    rcases Finset.mem_insert.mp hx with h | h
    · exact ab (h ▸ xy)
    · have xr := Finset.mem_singleton.mp h
      exact rb (xr ▸ xy)
  · intro equality A B hit hp
    subst r
    obtain ⟨b, hb, pb⟩ := hit.2
    exact ⟨p, hp, b, hb, pb⟩

lemma rectangle_line_center {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p l : Fin N) (edge : I p l) (r : Fin N) :
    (∀ A B : Finset (Fin N), rectangleHits I p l A B → r ∈ B → hasIncidence I A B) ↔ r = l := by
  have transpose := rectangle_point_center (fun x y => I y x) hq hN
    (lines_through q N I (by omega) hN hl hu)
    (fun x y ne => lines_intersect I (by omega) hN hl hu x y ne) l p edge r
  constructor
  · intro safe
    apply transpose.mp
    intro A B hit hr
    obtain ⟨a, ha, b, hb, ab⟩ := safe B A ⟨hit.2, hit.1⟩ hr
    exact ⟨b, hb, a, ha, ab⟩
  · intro equality A B hit hlB
    subst r
    obtain ⟨a, ha, al⟩ := hit.1
    exact ⟨a, ha, l, hlB, al⟩

lemma rectangle_selector_centers {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p l : Fin N) (edge : I p l) (P L : Finset (Fin N))
    (safe : ∀ A B : Finset (Fin N), rectangleHits I p l A B →
      ((A ∩ P).Nonempty ∨ (B ∩ L).Nonempty) → hasIncidence I A B) :
    P ⊆ {p} ∧ L ⊆ {l} := by
  constructor
  · intro r hr
    apply Finset.mem_singleton.mpr
    apply (rectangle_point_center I hq hN hl hu p l edge r).mp
    intro A B hit hA
    exact safe A B hit (Or.inl ⟨r, Finset.mem_inter.mpr ⟨hA, hr⟩⟩)
  · intro r hr
    apply Finset.mem_singleton.mpr
    apply (rectangle_line_center I hq hN hl hu p l edge r).mp
    intro A B hit hB
    exact safe A B hit (Or.inr ⟨r, Finset.mem_inter.mpr ⟨hB, hr⟩⟩)

end PEqualNP.Outside.L_meta_2583.PlaneGeometry
