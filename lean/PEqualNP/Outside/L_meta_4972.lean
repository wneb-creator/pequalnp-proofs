import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4972 : ∀ (x1 x2 x3 : ℕ) (x4 : (Fin x2 → Bool) → ℕ → Finset ℕ),   x3 < x1 + x2 →     (∀ (x6 : Fin x2 → Bool), ∀ x7 < x1, x4 x6 x7 = {x7}) →       (∀ (x7 : Fin x2), ∃ x8 < x1 + ↑x7, ∃ x9 < x1 + ↑x7, (∀ (x10 : Fin x2 → Bool), x4 x10 (x1 + ↑x7) = x4 x10 x8 ∪ x4 x10 x9) ∨ (∀ (x10 : Fin x2 → Bool), x4 x10 (x1 + ↑x7) = if x10 x7 = Bool.true then x4 x10 x8 else x4 x10 x9) ∨ ∀ (x10 : Fin x2 → Bool), x4 x10 (x1 + ↑x7) = ∅) →         ∀ (x8 : Fin x2 → Bool) (x9 : ℕ),           have x10 : Fin x2 → Bool := fun (x10 : Fin x2) => if ↑x10 < x9 ∧ x4 x8 (x1 + ↑x10) ⊆ x4 x8 x3 then x8 x10 else Bool.false;           x4 x10 x3 ⊆ x4 (fun (x11 : Fin x2) => Bool.false) x3 ∪ x4 x8 x3 ∧ (x2 ≤ x9 → x4 x10 x3 = x4 x8 x3) := by
  intro x1 x2 x3 x4 hx3 hbase hgate x8 x9
  dsimp only
  let t : Fin x2 → Bool := fun g =>
    if g.val < x9 ∧ x4 x8 (x1 + g.val) ⊆ x4 x8 x3 then x8 g else Bool.false
  let f0 : Fin x2 → Bool := fun _ => Bool.false
  change x4 t x3 ⊆ x4 f0 x3 ∪ x4 x8 x3 ∧ (x2 ≤ x9 → x4 t x3 = x4 x8 x3)
  have hmain : ∀ w, w < x1 + x2 →
      (w < x1 + x9 → x4 x8 w ⊆ x4 x8 x3 → x4 t w = x4 x8 w) ∧
      (x4 t w ⊆ x4 f0 w ∪ x4 x8 x3) := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hw
      by_cases hlt : w < x1
      · refine ⟨fun _ _ => ?_, ?_⟩
        · rw [hbase t w hlt, hbase x8 w hlt]
        · rw [hbase t w hlt, hbase f0 w hlt]
          intro z hz
          exact Finset.mem_union.mpr (Or.inl hz)
      · have hg_lt : w - x1 < x2 := by omega
        let g : Fin x2 := ⟨w - x1, hg_lt⟩
        have hwg : w = x1 + g.val := by dsimp only [g]; omega
        rw [hwg]
        rcases hgate g with ⟨a, ha, b, hb, hcase⟩
        have ha_w : a < w := by omega
        have hb_w : b < w := by omega
        have iha := ih a ha_w (by omega)
        have ihb := ih b hb_w (by omega)
        have hpart1 : x1 + g.val < x1 + x9 → x4 x8 (x1 + g.val) ⊆ x4 x8 x3 →
            x4 t (x1 + g.val) = x4 x8 (x1 + g.val) := by
          intro hgk hsub
          have hak : a < x1 + x9 := by omega
          have hbk : b < x1 + x9 := by omega
          rcases hcase with hunion | hchoice | hempty
          · rw [hunion t, hunion x8]
            rw [hunion x8] at hsub
            rw [iha.1 hak (fun z hz => hsub (Finset.mem_union.mpr (Or.inl hz))),
                ihb.1 hbk (fun z hz => hsub (Finset.mem_union.mpr (Or.inr hz)))]
          · rw [hchoice t, hchoice x8]
            have htg : t g = x8 g := by
              dsimp only [t]
              exact if_pos ⟨by omega, hsub⟩
            rw [htg]
            rw [hchoice x8] at hsub
            cases hsg : x8 g
            · simp only [hsg, Bool.false_eq_true, ite_false] at hsub ⊢
              exact ihb.1 hbk hsub
            · simp only [hsg, ite_true] at hsub ⊢
              exact iha.1 hak hsub
          · rw [hempty t, hempty x8]
        refine ⟨hpart1, ?_⟩
        rcases hcase with hunion | hchoice | hempty
        · rw [hunion t, hunion f0]
          intro z hz
          rcases Finset.mem_union.mp hz with hza | hzb
          · rcases Finset.mem_union.mp (iha.2 hza) with h | h
            · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h)))
            · exact Finset.mem_union.mpr (Or.inr h)
          · rcases Finset.mem_union.mp (ihb.2 hzb) with h | h
            · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h)))
            · exact Finset.mem_union.mpr (Or.inr h)
        · cases htg : t g
          · rw [hchoice t, hchoice f0]
            simp only [htg, f0, Bool.false_eq_true, ite_false]
            exact ihb.2
          · have hcond : g.val < x9 ∧ x4 x8 (x1 + g.val) ⊆ x4 x8 x3 := by
              by_contra hnc
              have htf : t g = Bool.false := by
                dsimp only [t]
                exact if_neg hnc
              rw [htf] at htg
              cases htg
            have heq := hpart1 (by omega) hcond.2
            rw [heq]
            intro z hz
            exact Finset.mem_union.mpr (Or.inr (hcond.2 hz))
        · rw [hempty t]
          intro z hz
          simp at hz
  have hres := hmain x3 hx3
  refine ⟨hres.2, fun hge => hres.1 (by omega) (fun _ h => h)⟩
