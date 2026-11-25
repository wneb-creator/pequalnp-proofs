import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma coneStep_order (n : ℕ) (cs : List (List ℕ)) (g : Gate)
    (hc : ∀ i j : ℕ, i ∈ cs.getD j [] → i < j) :
    ∀ i j : ℕ, i ∈ (coneStep n cs g).getD j [] → i < j := by
  intro i j hi
  unfold coneStep at hi
  rcases Nat.lt_trichotomy j cs.length with hj | hj | hj
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj] at hi
    exact hc i j hi
  · subst j
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi
    obtain ⟨w, hw, hi⟩ := List.mem_flatMap.mp hi
    simp only [List.mem_filter, decide_eq_true_eq] at hw
    rcases List.mem_cons.mp hi with hi | hi
    · omega
    · have := hc i (w - n) hi
      omega
  · have hj' : (cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])]).length ≤ j := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj'] at hi
    exact False.elim (List.not_mem_nil hi)

lemma cones_fold_order (n : ℕ) (gs : List Gate) (cs : List (List ℕ))
    (hc : ∀ i j : ℕ, i ∈ cs.getD j [] → i < j) :
    ∀ i j : ℕ, i ∈ (gs.foldl (coneStep n) cs).getD j [] → i < j := by
  induction gs generalizing cs with
  | nil => exact hc
  | cons g gs ih =>
    exact ih (coneStep n cs g) (coneStep_order n cs g hc)

lemma cone_index_lt {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : i < j := by
  exact cones_fold_order n C.gates [] (by simp) i j h

lemma two_junk_ordered {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hj : (junk G C).card = 2) :
    ∃ g h : ℕ, g < h ∧ junk G C = {g, h} ∧
      (∀ k ∈ junk G C, ¬ InCone n C k g) ∧ ¬ InCone n C h g := by
  obtain ⟨a, b, hab, hjab⟩ := Finset.card_eq_two.mp hj
  have arrange : ∀ a b : ℕ, a < b → junk G C = {a, b} →
      ∃ g h : ℕ, g < h ∧ junk G C = {g, h} ∧
        (∀ k ∈ junk G C, ¬ InCone n C k g) ∧ ¬ InCone n C h g := by
    intro a b hab hjab
    refine ⟨a, b, hab, hjab, ?_, ?_⟩
    · intro k hk hcone
      have hlt := cone_index_lt hcone
      rw [hjab] at hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      omega
    · intro hcone
      have hlt := cone_index_lt hcone
      omega
  rcases Nat.lt_or_gt_of_ne hab with hab | hba
  · exact arrange a b hab hjab
  · exact arrange b a hba (by rw [hjab, Finset.pair_comm])

lemma mem_junk_characterization {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) :
    j ∈ junk G C ↔ j < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and ∧ ¬ BelowF G C j := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty BelowF
  constructor
  · rintro ⟨hj, hop, _, x, hx, hf⟩
    refine ⟨hj, hop, ?_⟩
    intro hb
    have := hb x hx
    simp_all
  · rintro ⟨hj, hop, hb⟩
    push Not at hb
    obtain ⟨x, hx, hf⟩ := hb
    refine ⟨hj, hop, hj, x, hx, ?_⟩
    cases h : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x <;> simp_all

lemma two_junk_nested_or_pure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ht : TopForm G C) (hj : (junk G C).card = 2) :
    ∃ g h : ℕ, g < h ∧ junk G C = {g, h} ∧
      (∀ k < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.and → ¬ InCone n C k g) ∧
      (InCone n C g h ∨ ∀ k < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.and → ¬ InCone n C k h) := by
  obtain ⟨g, h, hgh, hjs, hmin, _⟩ := two_junk_ordered G C hj
  have hgm : g ∈ junk G C := by rw [hjs]; simp
  have hhm : h ∈ junk G C := by rw [hjs]; simp
  have hgp := (mem_junk_characterization G C g).mp hgm
  have hhp := (mem_junk_characterization G C h).mp hhm
  refine ⟨g, h, hgh, hjs, ?_, ?_⟩
  · intro k hk hop hc
    by_cases hb : BelowF G C k
    · exact ht k hk g hgp.1 hop hb hgp.2.1 hc
    · exact hmin k ((mem_junk_characterization G C k).mpr ⟨hk, hop, hb⟩) hc
  · by_cases hc : InCone n C g h
    · exact Or.inl hc
    · right
      intro k hk hop hkh
      by_cases hb : BelowF G C k
      · exact ht k hk h hhp.1 hop hb hhp.2.1 hkh
      · have hkm := (mem_junk_characterization G C k).mpr ⟨hk, hop, hb⟩
        rw [hjs] at hkm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hkm
        rcases hkm with rfl | rfl
        · exact hc hkh
        · have := cone_index_lt hkh
          omega

end PEqualNP.Outside.L_meta_5012
