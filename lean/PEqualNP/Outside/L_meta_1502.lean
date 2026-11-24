import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1502

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem blocks {α : Type} [DecidableEq α] (A : Finset α → Prop)
    (hA : ∀ Y Y' : Finset α, A Y → Y' ⊆ Y → 2 ≤ Y'.card → A Y') (f : ℕ → Finset α) (s : Finset ℕ)
    (h : ∀ w ∈ s, (f w).card ≤ 1 ∨ A (f w)) :
    ∃ P : Finset (Finset α), (∀ Y ∈ P, Y.Nonempty ∧ (Y.card = 1 ∨ A Y)) ∧
      (∀ Y ∈ P, ∀ Y' ∈ P, Y ≠ Y' → Disjoint Y Y') ∧ P.biUnion id = s.biUnion f ∧
      P.card ≤ s.card := by
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨P, h1, h2, h3, h4⟩ := ih (fun w hw => h w (Finset.mem_insert_of_mem hw))
    by_cases h0 : f a \ s.biUnion f = ∅
    · refine ⟨P, h1, h2, ?_, ?_⟩
      · rw [h3, Finset.biUnion_insert]
        rw [Finset.sdiff_eq_empty_iff_subset] at h0
        exact (Finset.union_eq_right.2 h0).symm
      · rw [Finset.card_insert_of_notMem ha]
        omega
    · have hne : (f a \ s.biUnion f).Nonempty := Finset.nonempty_iff_ne_empty.2 h0
      refine ⟨insert (f a \ s.biUnion f) P, ?_, ?_, ?_, ?_⟩
      · intro Y hY
        rcases Finset.mem_insert.1 hY with rfl | hY
        · refine ⟨hne, ?_⟩
          have hsub : f a \ s.biUnion f ⊆ f a := Finset.sdiff_subset
          have hc := Finset.card_le_card hsub
          have hpos := hne.card_pos
          by_cases h2' : 2 ≤ (f a \ s.biUnion f).card
          · rcases h a (Finset.mem_insert_self a s) with hh | hh
            · omega
            · exact Or.inr (hA _ _ hh hsub h2')
          · left
            omega
        · exact h1 Y hY
      · have key : ∀ Y ∈ P, Disjoint (f a \ s.biUnion f) Y := by
          intro Y hY
          have hYs : Y ⊆ s.biUnion f := by
            rw [← h3]
            exact Finset.subset_biUnion_of_mem id hY
          exact Finset.disjoint_of_subset_right hYs Finset.sdiff_disjoint
        intro Y hY Y' hY' hne'
        rcases Finset.mem_insert.1 hY with rfl | hY <;>
          rcases Finset.mem_insert.1 hY' with rfl | hY'
        · exact absurd rfl hne'
        · exact key _ hY'
        · exact (key _ hY).symm
        · exact h2 Y hY Y' hY' hne'
      · rw [Finset.biUnion_insert, Finset.biUnion_insert, h3]
        simp
      · have hc1 := Finset.card_insert_le (f a \ s.biUnion f) P
        rw [Finset.card_insert_of_notMem ha]
        omega

theorem count (n : ℕ) (C : Circuit) (hlen : ∀ k, (gateAt C k).inputs.length ≤ 2)
    (Z : Finset ℕ) (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (gateAt C k).op = GateOp.or ∧ n + k' ∈ (gateAt C k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (gateAt C k).op = GateOp.or ∧ w ∈ (gateAt C k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (gateAt C (w - n)).op ≠ GateOp.or)))
    (I : Finset ℕ)
    (hI : ∀ k, k ∈ R → k ∉ Z → (gateAt C k).op = GateOp.or → k ∈ I) :
    stops.card ≤ I.card + 1 := by
  classical
  have hSI : (R.filter (fun k => k ∉ Z ∧ (gateAt C k).op = GateOp.or)) ⊆ I := by
    intro k hk
    rw [Finset.mem_filter] at hk
    exact hI k hk.1 hk.2.1 hk.2.2
  generalize hS : (R.filter (fun k => k ∉ Z ∧ (gateAt C k).op = GateOp.or)) = S at hSI
  have hSmem : ∀ k, k ∈ S ↔ k ∈ R ∧ k ∉ Z ∧ (gateAt C k).op = GateOp.or := by
    intro k
    rw [← hS, Finset.mem_filter]
  have hTc : (insert (n + r) (S.biUnion fun k => (gateAt C k).inputs.toFinset)).card
      ≤ S.card * 2 + 1 := by
    refine (Finset.card_insert_le _ _).trans ?_
    have := Finset.card_biUnion_le_card_mul S (fun k => (gateAt C k).inputs.toFinset) 2
      (fun k _ => (List.toFinset_card_le _).trans (hlen k))
    omega
  generalize hT : (insert (n + r) (S.biUnion fun k => (gateAt C k).inputs.toFinset)) = T at hTc
  have hTmem : ∀ w, w ∈ T ↔ w = n + r ∨ ∃ k ∈ S, w ∈ (gateAt C k).inputs := by
    intro w
    rw [← hT]
    simp
  have hreach : ∀ k, k ∈ R → n + k ∈ T := by
    intro k hk
    rcases Relation.ReflTransGen.cases_tail ((hR k).1 hk) with h | ⟨b, hb, hbk⟩
    · exact (hTmem _).2 (Or.inl (by rw [h]))
    · exact (hTmem _).2 (Or.inr ⟨b, (hSmem b).2 ⟨(hR b).2 hb, hbk.1, hbk.2.1⟩, hbk.2.2⟩)
  have himg : S.image (fun k => n + k) ⊆ T := by
    intro w hw
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hw
    exact hreach k ((hSmem k).1 hk).1
  have hst : stops ⊆ T \ S.image (fun k => n + k) := by
    intro w hw
    rw [Finset.mem_sdiff]
    rcases (hstops w).1 hw with ⟨hwn, k, hk, hkZ, hor, hin⟩ | ⟨hwn, hwR, hw2⟩
    · refine ⟨(hTmem _).2 (Or.inr ⟨k, (hSmem k).2 ⟨hk, hkZ, hor⟩, hin⟩), ?_⟩
      intro hmem
      obtain ⟨k', _, hk'⟩ := Finset.mem_image.1 hmem
      omega
    · refine ⟨?_, ?_⟩
      · have := hreach _ hwR
        rwa [show n + (w - n) = w by omega] at this
      · intro hmem
        obtain ⟨k', hk', hkw⟩ := Finset.mem_image.1 hmem
        have hk'' : k' = w - n := by omega
        subst hk''
        have := (hSmem _).1 hk'
        rcases hw2 with h | h
        · exact this.2.1 h
        · exact h this.2.2
  have hc1 := Finset.card_le_card hst
  have hc2 := Finset.card_sdiff_add_card_eq_card himg
  have hc3 : (S.image (fun k => n + k)).card = S.card :=
    Finset.card_image_of_injective _ (add_right_injective n)
  have hc4 := Finset.card_le_card hSI
  omega

theorem cover {α : Type} [DecidableEq α] (n : ℕ) (C : Circuit)
    (hback : ∀ k, ∀ i ∈ (gateAt C k).inputs, i < n + k)
    (f : ℕ → Finset α)
    (hf : ∀ k, (gateAt C k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (gateAt C k).inputs, u ∈ f w)
    (Z : Finset ℕ) (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (gateAt C k).op = GateOp.or ∧ n + k' ∈ (gateAt C k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (gateAt C k).op = GateOp.or ∧ w ∈ (gateAt C k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (gateAt C (w - n)).op ≠ GateOp.or))) :
    stops.biUnion f = f (n + r) := by
  have hdown : ∀ k, k ∈ R → f (n + k) ⊆ stops.biUnion f := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk u hu
      by_cases hs : k ∈ Z ∨ (gateAt C k).op ≠ GateOp.or
      · refine Finset.mem_biUnion.2 ⟨n + k, (hstops _).2 (Or.inr ⟨by omega, ?_, ?_⟩), hu⟩
        · rwa [Nat.add_sub_cancel_left]
        · rwa [Nat.add_sub_cancel_left]
      · have hkZ : k ∉ Z := fun h => hs (Or.inl h)
        have hor : (gateAt C k).op = GateOp.or := by
          by_contra h
          exact hs (Or.inr h)
        obtain ⟨w, hw, huw⟩ := (hf k hor u).1 hu
        by_cases hwn : w < n
        · exact Finset.mem_biUnion.2 ⟨w, (hstops _).2 (Or.inl ⟨hwn, k, hk, hkZ, hor, hw⟩), huw⟩
        · have hwk := hback k w hw
          have hweq : n + (w - n) = w := by omega
          have hwR : w - n ∈ R :=
            (hR _).2 (((hR k).1 hk).tail ⟨hkZ, hor, by rwa [hweq]⟩)
          exact ih (w - n) (by omega) hwR (by rwa [hweq])
  have hup : ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
    intro k hk
    have h := (hR k).1 hk
    clear hk
    induction h with
    | refl => exact Finset.Subset.refl _
    | tail _ hbc ih =>
      intro u hu
      exact ih ((hf _ hbc.2.1 u).2 ⟨_, hbc.2.2, hu⟩)
  apply Finset.Subset.antisymm
  · intro u hu
    obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.1 hu
    rcases (hstops w).1 hw with ⟨hwn, k, hk, hkZ, hor, hin⟩ | ⟨hwn, hwR, hw2⟩
    · exact hup k hk ((hf k hor u).2 ⟨w, hin, huw⟩)
    · have := hup _ hwR
      rw [show n + (w - n) = w by omega] at this
      exact this huw
  · exact hdown r ((hR r).2 Relation.ReflTransGen.refl)

theorem gateAt_ge (C : Circuit) (k : ℕ) (hk : C.gates.length ≤ k) :
    gateAt C k = ⟨GateOp.or, []⟩ := by
  unfold gateAt
  simp [List.getD, List.getElem?_eq_none hk]

theorem back_of (n : ℕ) (C : Circuit)
    (h : ∀ j < C.gates.length, ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    ∀ k, ∀ i ∈ (gateAt C k).inputs, i < n + k := by
  intro k i hi
  by_cases hk : k < C.gates.length
  · exact h k hk i hi
  · rw [gateAt_ge C k (by omega)] at hi
    simp at hi

theorem len_of (C : Circuit)
    (h : ∀ j < C.gates.length, (gateAt C j).inputs.length ≤ 2) :
    ∀ k, (gateAt C k).inputs.length ≤ 2 := by
  intro k
  by_cases hk : k < C.gates.length
  · exact h k hk
  · rw [gateAt_ge C k (by omega)]
    simp

theorem R_le (n : ℕ) (C : Circuit)
    (hback : ∀ k, ∀ i ∈ (gateAt C k).inputs, i < n + k)
    (Z : Finset ℕ) (r k : ℕ)
    (h : Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (gateAt C k).op = GateOp.or ∧ n + k' ∈ (gateAt C k).inputs) r k) : k ≤ r := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih =>
    have := hback _ _ hbc.2.2
    omega

theorem cover2 {α : Type} [DecidableEq α] (n : ℕ) (C : Circuit)
    (hback : ∀ k, ∀ i ∈ (gateAt C k).inputs, i < n + k)
    (f : ℕ → Finset α)
    (hf : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (gateAt C k).inputs, u ∈ f w)
    (Z : Finset ℕ) (r : ℕ) (hr : r < C.gates.length) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (gateAt C k).op = GateOp.or ∧ n + k' ∈ (gateAt C k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (gateAt C k).op = GateOp.or ∧ w ∈ (gateAt C k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (gateAt C (w - n)).op ≠ GateOp.or))) :
    stops.biUnion f = f (n + r) := by
  have hlt : ∀ k, k ∈ R → k < C.gates.length := fun k hk =>
    lt_of_le_of_lt (R_le n C hback Z r k ((hR k).1 hk)) hr
  have hdown : ∀ k, k ∈ R → f (n + k) ⊆ stops.biUnion f := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk u hu
      by_cases hs : k ∈ Z ∨ (gateAt C k).op ≠ GateOp.or
      · refine Finset.mem_biUnion.2 ⟨n + k, (hstops _).2 (Or.inr ⟨by omega, ?_, ?_⟩), hu⟩
        · rwa [Nat.add_sub_cancel_left]
        · rwa [Nat.add_sub_cancel_left]
      · have hkZ : k ∉ Z := fun h => hs (Or.inl h)
        have hor : (gateAt C k).op = GateOp.or := by
          by_contra h
          exact hs (Or.inr h)
        obtain ⟨w, hw, huw⟩ := (hf k (hlt k hk) hor u).1 hu
        by_cases hwn : w < n
        · exact Finset.mem_biUnion.2 ⟨w, (hstops _).2 (Or.inl ⟨hwn, k, hk, hkZ, hor, hw⟩), huw⟩
        · have hwk := hback k w hw
          have hweq : n + (w - n) = w := by omega
          have hwR : w - n ∈ R :=
            (hR _).2 (((hR k).1 hk).tail ⟨hkZ, hor, by rwa [hweq]⟩)
          exact ih (w - n) (by omega) hwR (by rwa [hweq])
  have hup : ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
    intro k hk
    have h := (hR k).1 hk
    clear hk
    induction h with
    | refl => exact Finset.Subset.refl _
    | tail hab hbc ih =>
      intro u hu
      exact ih ((hf _ (hlt _ ((hR _).2 hab)) hbc.2.1 u).2 ⟨_, hbc.2.2, hu⟩)
  apply Finset.Subset.antisymm
  · intro u hu
    obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.1 hu
    rcases (hstops w).1 hw with ⟨hwn, k, hk, hkZ, hor, hin⟩ | ⟨hwn, hwR, hw2⟩
    · exact hup k hk ((hf k (hlt k hk) hor u).2 ⟨w, hin, huw⟩)
    · have := hup _ hwR
      rw [show n + (w - n) = w by omega] at this
      exact this huw
  · exact hdown r ((hR r).2 Relation.ReflTransGen.refl)

theorem orSets_spec (n : ℕ) (gs : List Gate) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length ∧
    ∀ k < gs.length, ∀ g, g ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] ↔
      g = k ∨ ((gs.getD k ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + k ∧
          g ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g0 ih =>
    obtain ⟨hl, hs⟩ := ih
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize gs.foldl (PEqualNP.CleanedNonEdge.orStep n) [] = S at hl hs
    have hpre : ∀ i < gs.length,
        (PEqualNP.CleanedNonEdge.orStep n S g0).getD i [] = S.getD i [] := by
      intro i hi
      unfold PEqualNP.CleanedNonEdge.orStep
      exact List.getD_append _ _ _ _ (by omega)
    have hlast : ∀ g, g ∈ (PEqualNP.CleanedNonEdge.orStep n S g0).getD gs.length [] ↔
        g = gs.length ∨ (g0.op = GateOp.or ∧ ∃ w ∈ g0.inputs, n ≤ w ∧ w < n + gs.length ∧
          g ∈ S.getD (w - n) []) := by
      intro g
      unfold PEqualNP.CleanedNonEdge.orStep
      rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
      by_cases hop : g0.op = GateOp.or
      · simp [hop, and_assoc]
      · simp [hop]
    refine ⟨by simp [PEqualNP.CleanedNonEdge.orStep, hl], ?_⟩
    intro k hk g
    rw [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
    · rw [hpre k hk', List.getD_append _ _ _ _ hk', hs k hk' g]
      constructor
      · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hop, w, hw, h1, h2, by rwa [hpre _ (by omega)]⟩
      · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hop, w, hw, h1, h2, by rwa [hpre _ (by omega)] at h3⟩
    · rw [hlast g, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
      simp only [List.getD_cons_zero]
      constructor
      · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hop, w, hw, h1, h2, by rwa [hpre _ (by omega)]⟩
      · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hop, w, hw, h1, h2, by rwa [hpre _ (by omega)] at h3⟩

theorem orReaches_def (n : ℕ) (C : Circuit) (w g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C w g ↔
      n ≤ w ∧ g ∈ (C.gates.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [] :=
  Iff.rfl

theorem orReaches_iff (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) (g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        PEqualNP.CleanedNonEdge.OrReaches n C w g) := by
  rw [orReaches_def, Nat.add_sub_cancel_left, (orSets_spec n C.gates).2 k hk g]
  constructor
  · rintro ⟨_, h | ⟨hop, w, hw, h1, h2, h3⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, h1, h2, (orReaches_def n C w g).2 ⟨h1, h3⟩⟩
  · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
    · exact ⟨by omega, Or.inl h⟩
    · exact ⟨by omega, Or.inr ⟨hop, w, hw, h1, h2, ((orReaches_def n C w g).1 h3).2⟩⟩

theorem orIn_or (n : ℕ) (C : Circuit) (hback : ∀ k, ∀ i ∈ (gateAt C k).inputs, i < n + k)
    (k : ℕ) (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔
      ∃ w ∈ (gateAt C k).inputs, u ∈ PEqualNP.TopForm.orIn n C w := by
  have hmem : ∀ w, u ∈ PEqualNP.TopForm.orIn n C w ↔ ((u : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (u : ℕ) ∈ (gateAt C k).inputs) := by
    intro w
    unfold PEqualNP.TopForm.orIn
    simp
  constructor
  · intro h
    rcases (hmem _).1 h with h | ⟨k', hk', hr, hor', hin⟩
    · have := u.isLt
      omega
    · rcases (orReaches_iff n C k hk k').1 hr with h | ⟨_, w, hw, h1, h2, h3⟩
      · subst h
        exact ⟨u, hin, (hmem _).2 (Or.inl rfl)⟩
      · exact ⟨w, hw, (hmem _).2 (Or.inr ⟨k', hk', h3, hor', hin⟩)⟩
  · rintro ⟨w, hw, h⟩
    rcases (hmem _).1 h with h | ⟨k', hk', hr, hor', hin⟩
    · exact (hmem _).2 (Or.inr ⟨k, hk, (orReaches_iff n C k hk k).2 (Or.inl rfl), hor,
        by rw [h]; exact hw⟩)
    · exact (hmem _).2 (Or.inr ⟨k', hk', (orReaches_iff n C k hk k').2
        (Or.inr ⟨hor, w, hw, ((orReaches_def n C w k').1 hr).1, hback k w hw, hr⟩), hor', hin⟩)

theorem back (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) :
    ∀ k, ∀ i ∈ (gateAt C k).inputs, i < n + k :=
  back_of n C h.2.1

theorem len2 (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) :
    ∀ k, (gateAt C k).inputs.length ≤ 2 := by
  apply len_of
  intro j hj
  have hg : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  exact le_of_eq (h.2.2 _ hg)

end PEqualNP.Outside.L_meta_1502

theorem PEqualNP.Outside.L_meta_1502 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C →
  ∀ (Z : Finset ℕ) (r : ℕ), r < C.gates.length →
  ∀ (R : Finset ℕ), (∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      n + k' ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) r k) →
  ∀ (stops : Finset ℕ), (∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or))) →
  ∀ (A : Finset (Fin n) → Prop),
    (∀ Y Y' : Finset (Fin n), A Y → Y' ⊆ Y → 2 ≤ Y'.card → A Y') →
    (∀ w ∈ stops, (PEqualNP.TopForm.orIn n C w).card ≤ 1 ∨ A (PEqualNP.TopForm.orIn n C w)) →
    ∃ P : Finset (Finset (Fin n)),
      (∀ Y ∈ P, Y.Nonempty ∧ (Y.card = 1 ∨ A Y)) ∧
      (∀ Y ∈ P, ∀ Y' ∈ P, Y ≠ Y' → Disjoint Y Y') ∧
      P.biUnion id = PEqualNP.TopForm.orIn n C (n + r) ∧
      ∀ I : Finset ℕ, (∀ k, k ∈ R → k ∉ Z →
          (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or → k ∈ I) →
        P.card ≤ I.card + 1 := by
  intro n C hAO Z r hr R hR stops hstops A hA hSt
  have hback := PEqualNP.Outside.L_meta_1502.back n C hAO
  obtain ⟨P, h1, h2, h3, h4⟩ := PEqualNP.Outside.L_meta_1502.blocks A hA
    (fun w => PEqualNP.TopForm.orIn n C w) stops hSt
  refine ⟨P, h1, h2, ?_, ?_⟩
  · rw [h3]
    exact PEqualNP.Outside.L_meta_1502.cover2 n C hback
      (fun w => PEqualNP.TopForm.orIn n C w)
      (fun k hk hor u => PEqualNP.Outside.L_meta_1502.orIn_or n C hback k hk hor u)
      Z r hr R hR stops hstops
  · intro I hI
    exact h4.trans (PEqualNP.Outside.L_meta_1502.count n C
      (PEqualNP.Outside.L_meta_1502.len2 n C hAO) Z r R hR stops hstops I hI)
