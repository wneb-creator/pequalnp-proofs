import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585.Merge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma replacement_of_star_cover (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit) (own : List (ℕ × List ℕ))
    (hshape : ∀ s ∈ own, s.2 ≠ [] ∧
      ((s.1 < P ∧ ∀ b ∈ s.2, P ≤ b ∧ b < P + L) ∨
        P ≤ s.1 ∧ s.1 < P + L ∧ ∀ b ∈ s.2, b < P))
    (hcover : ∀ p : Fin P, ∀ l : Fin L, I p l ↔ ∃ s ∈ own,
      s.1 = p.val ∧ P + l.val ∈ s.2 ∨ s.1 = P + l.val ∧ p.val ∈ s.2)
    (hcost : (own.map (fun s => s.2.length)).sum + own.length - 1 ≤ C.size) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧
      (∀ y : Fin (P + L) → Bool, circuitFun (P + L) D y =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧
      D.size ≤ C.size ∧ IsReadK (P + L) D 1 := by
  have hgood : ∀ s ∈ own, s.2 ≠ [] ∧ s.1 < P + L ∧
      ∀ b ∈ s.2, b < P + L ∧ s.1 ≠ b := by
    intro s hs
    have h := hshape s hs
    refine ⟨h.1, ?_, ?_⟩
    · rcases h.2 with ⟨hc, _⟩ | ⟨_, hc, _⟩ <;> omega
    · intro b hb
      rcases h.2 with ⟨hc, hbs⟩ | ⟨hc, _, hbs⟩
      · have := hbs b hb
        constructor <;> omega
      · have := hbs b hb
        constructor <;> omega
  obtain ⟨D, hDv, hDf, hDs, hDr, _⟩ := family_exists (P + L) own hgood
  refine ⟨D, hDv, ?_, by rw [hDs]; exact hcost, hDr⟩
  intro y
  have readp (p : Fin P) :
      (List.ofFn y).getD p.val false = y (Fin.castAdd L p) := by
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; omega), List.getElem_ofFn]
    rfl
  have readl (l : Fin L) :
      (List.ofFn y).getD (P + l.val) false = y (Fin.natAdd P l) := by
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; omega), List.getElem_ofFn]
    rfl
  change D.eval (List.ofFn y) = _
  rw [hDf _ (by simp)]
  apply Bool.eq_iff_iff.mpr
  simp only [familyFun, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs, hc, b, hb, hbt⟩
    rcases (hshape s hs).2 with ⟨hsp, hbl⟩ | ⟨hsl, hsn, hbp⟩
    · have hbn := hbl b hb
      let p : Fin P := ⟨s.1, hsp⟩
      let l : Fin L := ⟨b - P, by omega⟩
      have hbeq : P + l.val = b := by dsimp [l]; omega
      have hi : I p l := (hcover p l).2 ⟨s, hs, Or.inl ⟨rfl, by rw [hbeq]; exact hb⟩⟩
      refine ⟨p, l, hi, ?_, ?_⟩
      · rw [← readp p]
        exact hc
      · rw [← readl l, hbeq]
        exact hbt
    · have hbn := hbp b hb
      let p : Fin P := ⟨b, hbn⟩
      let l : Fin L := ⟨s.1 - P, by omega⟩
      have hseq : P + l.val = s.1 := by dsimp [l]; omega
      have hi : I p l := (hcover p l).2 ⟨s, hs, Or.inr ⟨hseq.symm, hb⟩⟩
      refine ⟨p, l, hi, ?_, ?_⟩
      · rw [← readp p]
        exact hbt
      · rw [← readl l, hseq]
        exact hc
  · rintro ⟨p, l, hi, hp, hl⟩
    obtain ⟨s, hs, h⟩ := (hcover p l).1 hi
    rcases h with ⟨hc, hb⟩ | ⟨hc, hb⟩
    · refine ⟨s, hs, ?_, P + l.val, hb, ?_⟩
      · rw [hc, readp]
        exact hp
      · rw [readl]
        exact hl
    · refine ⟨s, hs, ?_, p.val, hb, ?_⟩
      · rw [hc, readl]
        exact hl
      · rw [readp]
        exact hp

end PEqualNP.Outside.L_meta_2585.Merge
