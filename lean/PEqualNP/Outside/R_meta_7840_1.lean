import PEqualNP.Defs

open PEqualNP.AndCount

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_7840_1
    (hOneDirty :
      let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 =>
        a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      let bare := fun (C : AndCountCircuit 42) (k : Fin C.size) (e : Fin 42 × Fin 42) =>
        (e.1 ∈ C.leftVars k ∧ e.2 ∈ C.rightVars k) ∨ (e.2 ∈ C.leftVars k ∧ e.1 ∈ C.rightVars k)
      let isClean := fun (C : AndCountCircuit 42) (k : Fin C.size) =>
        ∀ u ∈ C.leftVars k, ∀ v ∈ C.rightVars k, G.Adj u v
      ∀ C : AndCountCircuit 42, C.WellFormed → C.Computes G → C.outVars = ∅ →
        (∀ i v, C.gateVal {v} i = false) → (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) →
        C.size ≤ 20 →
        (∃ i : Fin C.size, i ∉ C.outGates ∧ ¬ isClean C i ∧
          (∀ j : Fin C.size, j ≠ i → isClean C j) ∧
          ∃ S : Finset (Fin 42 × Fin 42), 10 ≤ S.card ∧
            ∀ e ∈ S, e.1.val < 21 ∧ G.Adj e.1 e.2 ∧ bare C i e ∧
              ∀ j : Fin C.size, j ≠ i → ¬ bare C j e) → False)
    (hMultiDirty :
      let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 =>
        a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      let bare := fun (C : AndCountCircuit 42) (k : Fin C.size) (e : Fin 42 × Fin 42) =>
        (e.1 ∈ C.leftVars k ∧ e.2 ∈ C.rightVars k) ∨ (e.2 ∈ C.leftVars k ∧ e.1 ∈ C.rightVars k)
      let isClean := fun (C : AndCountCircuit 42) (k : Fin C.size) =>
        ∀ u ∈ C.leftVars k, ∀ v ∈ C.rightVars k, G.Adj u v
      ∀ C : AndCountCircuit 42, C.WellFormed → C.Computes G → C.outVars = ∅ →
        (∀ i v, C.gateVal {v} i = false) → (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) →
        C.size ≤ 20 →
        (∃ i j : Fin C.size, i ≠ j ∧ i ∉ C.outGates ∧ j ∉ C.outGates ∧
          ¬ isClean C i ∧ ¬ isClean C j ∧
          ∃ S : Finset (Fin 42 × Fin 42), 6 ≤ S.card ∧
            ∀ e ∈ S, e.1.val < 21 ∧ G.Adj e.1 e.2 ∧ bare C i e ∧
              ∀ k : Fin C.size, isClean C k → ¬ bare C k e) → False) :
    have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x2.WellFormed → x2.Computes x1 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) → (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) → (∃ (x8 : Fin x2.size), ∃ x9 ∈ x2.leftVars x8, ∃ x10 ∈ x2.rightVars x8, ¬x1.Adj x9 x10) → (21 : ℕ) ≤ x2.size := by
  classical
  intro G C hWF hComp hOut hSing hDisj hHasDirty
  by_contra hlt
  have hle20 : C.size ≤ 20 := by omega
  let rel : Fin 42 → Fin 42 → Prop := fun a b =>
    a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
  have hAdj : ∀ a b : Fin 42, G.Adj a b ↔ a ≠ b ∧ (rel a b ∨ rel b a) := by
    intro a b
    exact SimpleGraph.fromRel_adj rel a b
  let E : Finset (Fin 42 × Fin 42) :=
    Finset.univ.filter fun e => e.1.val < 21 ∧ 21 ≤ e.2.val ∧ (e.2.val + 21 - e.1.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
  have hEcard : E.card = 105 := by decide +kernel
  have hDeg : ∀ v : Fin 42, (E.filter fun e => e.1 = v ∨ e.2 = v).card ≤ 5 := by decide +kernel
  have hNoC4 : ∀ a a' : Fin 42, a ≠ a' →
      (Finset.univ.filter fun b : Fin 42 =>
        ((a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∨
         (b.val < 21 ∧ 21 ≤ a.val ∧ (a.val + 21 - b.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))) ∧
        ((a'.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a'.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∨
         (b.val < 21 ∧ 21 ≤ a'.val ∧ (a'.val + 21 - b.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)))).card ≤ 1 := by
    decide +kernel
  let bare : Fin C.size → Fin 42 × Fin 42 → Prop := fun k e =>
    (e.1 ∈ C.leftVars k ∧ e.2 ∈ C.rightVars k) ∨ (e.2 ∈ C.leftVars k ∧ e.1 ∈ C.rightVars k)
  let isClean : Fin C.size → Prop := fun k =>
    ∀ u ∈ C.leftVars k, ∀ v ∈ C.rightVars k, G.Adj u v
  have hOutClean : ∀ i : Fin C.size, i ∈ C.outGates → isClean i := by
    intro i hiOut u hu v hv
    have hpos : 0 < C.size := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    have hgi : C.gateVal {u, v} i = true := by
      change C.gateValFuel {u, v} C.size i = true
      rw [hm]
      change (AndCountCircuit.sideTrue {u, v} (C.leftVars i) (C.leftGates i) i (C.gateValFuel {u, v} m) &&
        AndCountCircuit.sideTrue {u, v} (C.rightVars i) (C.rightGates i) i (C.gateValFuel {u, v} m)) = true
      rw [Bool.and_eq_true]
      constructor
      · change decide ((∃ x ∈ C.leftVars i, x ∈ ({u, v} : Finset (Fin 42))) ∨ _) = true
        rw [decide_eq_true_eq]
        exact Or.inl ⟨u, hu, Finset.mem_insert_self u {v}⟩
      · change decide ((∃ x ∈ C.rightVars i, x ∈ ({u, v} : Finset (Fin 42))) ∨ _) = true
        rw [decide_eq_true_eq]
        exact Or.inl ⟨v, hv, Finset.mem_insert_of_mem (Finset.mem_singleton_self v)⟩
    have hev : C.eval {u, v} = true := by
      change decide ((∃ x ∈ C.outVars, x ∈ ({u, v} : Finset (Fin 42))) ∨ ∃ j ∈ C.outGates, C.gateVal {u, v} j = true) = true
      rw [decide_eq_true_eq]
      exact Or.inr ⟨i, hiOut, hgi⟩
    obtain ⟨a, ha, b, hb, hab⟩ := (hComp {u, v}).mp hev
    have ha' := Finset.mem_insert.mp ha
    have hb' := Finset.mem_insert.mp hb
    obtain rfl | ha'' := ha'
    · obtain rfl | hb'' := hb'
      · exact False.elim (G.loopless.irrefl _ hab)
      · have hbe := Finset.mem_singleton.mp hb''
        rw [hbe] at hab
        exact hab
    · have hae := Finset.mem_singleton.mp ha''
      rw [hae] at hab
      obtain rfl | hb'' := hb'
      · exact G.symm.symm _ _ hab
      · have hbe := Finset.mem_singleton.mp hb''
        rw [hbe] at hab
        exact False.elim (G.loopless.irrefl _ hab)
  have hDirtyNotOut : ∀ i : Fin C.size, ¬ isClean i → i ∉ C.outGates := by
    intro i hnd hiOut
    exact hnd (hOutClean i hiOut)
  have hFuelBare : ∀ (U : Finset (Fin 42)) (d : ℕ) (i : Fin C.size),
      C.gateValFuel U d i = true →
      ∃ k : Fin C.size, ∃ a ∈ C.leftVars k, ∃ b ∈ C.rightVars k, a ∈ U ∧ b ∈ U := by
    intro U d
    induction d with
    | zero =>
      intro i h
      have h0 : C.gateValFuel U 0 i = false := rfl
      rw [h0] at h
      exact False.elim (Bool.false_ne_true h)
    | succ d ih =>
      intro i h
      have h0 : C.gateValFuel U (d + 1) i =
        (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U d) &&
         AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U d)) := rfl
      rw [h0, Bool.and_eq_true] at h
      obtain ⟨hl, hr⟩ := h
      have hside : ∀ (B : Finset (Fin 42)) (F : Finset (Fin C.size)),
          AndCountCircuit.sideTrue U B F i (C.gateValFuel U d) =
            decide ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ C.gateValFuel U d j = true) := fun _ _ => rfl
      rw [hside, decide_eq_true_eq] at hl hr
      obtain hl1 | hl2 := hl
      · obtain ⟨a, ha, haU⟩ := hl1
        obtain hr1 | hr2 := hr
        · obtain ⟨b, hb, hbU⟩ := hr1
          exact ⟨i, a, ha, b, hb, haU, hbU⟩
        · obtain ⟨j, _, _, hj⟩ := hr2
          exact ih j hj
      · obtain ⟨j, _, _, hj⟩ := hl2
        exact ih j hj
  have hEdgeAdj : ∀ e : Fin 42 × Fin 42, e ∈ E → e.1.val < 21 ∧ G.Adj e.1 e.2 := by
    intro e he
    have hr := (Finset.mem_filter.mp he).2
    have hne : e.1 ≠ e.2 := by
      intro h
      have h1 := hr.1
      have h2 := hr.2.1
      rw [h] at h1
      omega
    exact ⟨hr.1, (hAdj e.1 e.2).mpr ⟨hne, Or.inl hr⟩⟩
  have hCover : ∀ e : Fin 42 × Fin 42, e ∈ E → ∃ k : Fin C.size, bare k e := by
    intro e he
    have hadj := (hEdgeAdj e he).2
    have hev : C.eval {e.1, e.2} = true :=
      (hComp {e.1, e.2}).mpr ⟨e.1, Finset.mem_insert_self _ _, e.2, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hadj⟩
    have hevd : C.eval {e.1, e.2} =
        decide ((∃ v ∈ C.outVars, v ∈ ({e.1, e.2} : Finset (Fin 42))) ∨ ∃ j ∈ C.outGates, C.gateVal {e.1, e.2} j = true) := rfl
    rw [hevd, decide_eq_true_eq, hOut] at hev
    obtain hv | hj := hev
    · obtain ⟨v, hv0, _⟩ := hv
      exact False.elim (Finset.notMem_empty v hv0)
    · obtain ⟨j, _, hjT⟩ := hj
      obtain ⟨k, a, ha, b, hb, haU, hbU⟩ := hFuelBare {e.1, e.2} C.size j hjT
      have hab : a ≠ b := by
        intro h
        rw [h] at ha
        exact Finset.disjoint_left.mp (hDisj k) ha hb
      refine ⟨k, ?_⟩
      obtain ha1 | ha2 := Finset.mem_insert.mp haU
      · obtain hb1 | hb2 := Finset.mem_insert.mp hbU
        · exact False.elim (hab (ha1.trans hb1.symm))
        · have hb2' := Finset.mem_singleton.mp hb2
          rw [ha1] at ha
          rw [hb2'] at hb
          exact Or.inl ⟨ha, hb⟩
      · have ha2' := Finset.mem_singleton.mp ha2
        obtain hb1 | hb2 := Finset.mem_insert.mp hbU
        · rw [ha2'] at ha
          rw [hb1] at hb
          exact Or.inr ⟨ha, hb⟩
        · have hb2' := Finset.mem_singleton.mp hb2
          exact False.elim (hab (ha2'.trans hb2'.symm))
  have hSub5 : ∀ (S : Finset (Fin 42)), (∀ x ∈ S, ∀ y ∈ S, x = y) →
      ∀ (T : Finset (Fin 42 × Fin 42)), T ⊆ E → (∀ e ∈ T, e.1 ∈ S ∨ e.2 ∈ S) → T.card ≤ 5 := by
    intro S hS T hT hTS
    by_cases hb : ∃ b, b ∈ S
    · obtain ⟨b, hb⟩ := hb
      refine le_trans (Finset.card_le_card ?_) (hDeg b)
      intro e he
      refine Finset.mem_filter.mpr ⟨hT he, ?_⟩
      obtain h1 | h2 := hTS e he
      · exact Or.inl (hS _ h1 _ hb)
      · exact Or.inr (hS _ h2 _ hb)
    · have hem : T = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        obtain h1 | h2 := hTS e he
        · exact hb ⟨_, h1⟩
        · exact hb ⟨_, h2⟩
      rw [hem]
      exact Nat.zero_le 5
  have hClean5 : ∀ k : Fin C.size, isClean k → (E.filter fun e => bare k e).card ≤ 5 := by
    intro k hk
    by_cases hL : ∃ a ∈ C.leftVars k, ∃ a' ∈ C.leftVars k, a ≠ a'
    · obtain ⟨a, ha, a', ha', hne⟩ := hL
      have hR : ∀ x ∈ C.rightVars k, ∀ y ∈ C.rightVars k, x = y := by
        intro x hx y hy
        have hm : ∀ z ∈ C.rightVars k, z ∈ Finset.univ.filter (fun b : Fin 42 =>
            ((a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∨
             (b.val < 21 ∧ 21 ≤ a.val ∧ (a.val + 21 - b.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))) ∧
            ((a'.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a'.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∨
             (b.val < 21 ∧ 21 ≤ a'.val ∧ (a'.val + 21 - b.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)))) := by
          intro z hz
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((hAdj a z).mp (hk a ha z hz)).2, ((hAdj a' z).mp (hk a' ha' z hz)).2⟩
        exact Finset.card_le_one.mp (hNoC4 a a' hne) x (hm x hx) y (hm y hy)
      refine hSub5 (C.rightVars k) hR _ (Finset.filter_subset _ _) ?_
      intro e he
      obtain h1 | h2 := (Finset.mem_filter.mp he).2
      · exact Or.inr h1.2
      · exact Or.inl h2.2
    · have hL' : ∀ x ∈ C.leftVars k, ∀ y ∈ C.leftVars k, x = y := by
        intro x hx y hy
        by_contra h
        exact hL ⟨x, hx, y, hy, h⟩
      refine hSub5 (C.leftVars k) hL' _ (Finset.filter_subset _ _) ?_
      intro e he
      obtain h1 | h2 := (Finset.mem_filter.mp he).2
      · exact Or.inl h1.1
      · exact Or.inr h2.1
  let Clean : Finset (Fin C.size) := Finset.univ.filter fun k => isClean k
  let Dirty : Finset (Fin C.size) := Finset.univ.filter fun k => ¬ isClean k
  have hPart : Clean.card + Dirty.card = C.size := by
    have hdisj : Disjoint Clean Dirty := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      exact (Finset.mem_filter.mp hk2).2 (Finset.mem_filter.mp hk1).2
    have hunion : Clean ∪ Dirty = Finset.univ := by
      ext k
      simp only [Clean, Dirty, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact em (isClean k)
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  have hDirtyPos : 1 ≤ Dirty.card := by
    obtain ⟨i0, u0, hu0, v0, hv0, hna0⟩ := hHasDirty
    have hi0 : i0 ∈ Dirty := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hcl
      exact hna0 (hcl u0 hu0 v0 hv0)
    exact Finset.card_pos.mpr ⟨i0, hi0⟩
  let CovClean : Finset (Fin 42 × Fin 42) := Clean.biUnion fun k => E.filter fun e => bare k e
  have hCovCleanCard : CovClean.card ≤ Clean.card * 5 := by
    exact Finset.card_biUnion_le_card_mul Clean (fun k => E.filter fun e => bare k e) 5
      (fun k hk => hClean5 k (Finset.mem_filter.mp hk).2)
  let U : Finset (Fin 42 × Fin 42) := E \ CovClean
  have hCovSubE : CovClean ⊆ E := by
    intro e he
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_filter.mp hk).1
  have hUcard : 105 - Clean.card * 5 ≤ U.card := by
    have hsd : U.card + CovClean.card = E.card := Finset.card_sdiff_add_card_eq_card hCovSubE
    rw [hEcard] at hsd
    omega
  have hUCovDirty : U ⊆ Dirty.biUnion fun k => U.filter fun e => bare k e := by
    intro e he
    have heE := (Finset.mem_sdiff.mp he).1
    have heNotClean := (Finset.mem_sdiff.mp he).2
    obtain ⟨k, hk⟩ := hCover e heE
    have hkDirty : k ∈ Dirty := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hcl
      apply heNotClean
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcl⟩,
        Finset.mem_filter.mpr ⟨heE, hk⟩⟩
    exact Finset.mem_biUnion.mpr ⟨k, hkDirty, Finset.mem_filter.mpr ⟨he, hk⟩⟩
  have hUnotClean : ∀ e ∈ U, ∀ k : Fin C.size, isClean k → ¬ bare k e := by
    intro e he k hcl hbk
    have heE := (Finset.mem_sdiff.mp he).1
    have heNotClean := (Finset.mem_sdiff.mp he).2
    exact heNotClean (Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcl⟩,
      Finset.mem_filter.mpr ⟨heE, hbk⟩⟩)
  by_cases hOne : Dirty.card = 1
  · obtain ⟨i, hiEq⟩ := Finset.card_eq_one.mp hOne
    have hiMem : i ∈ Dirty := by rw [hiEq]; exact Finset.mem_singleton_self i
    have hiDirty : ¬ isClean i := (Finset.mem_filter.mp hiMem).2
    have hAllOtherClean : ∀ j : Fin C.size, j ≠ i → isClean j := by
      intro j hji
      by_contra hnd
      have hjMem : j ∈ Dirty := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnd⟩
      rw [hiEq] at hjMem
      exact hji (Finset.mem_singleton.mp hjMem)
    have hUcard10 : 10 ≤ U.card := by omega
    apply hOneDirty C hWF hComp hOut hSing hDisj hle20
    refine ⟨i, hDirtyNotOut i hiDirty, hiDirty, hAllOtherClean, U, hUcard10, ?_⟩
    intro e he
    have heE := (Finset.mem_sdiff.mp he).1
    have heAdj := hEdgeAdj e heE
    obtain ⟨k, hkD, hkF⟩ := Finset.mem_biUnion.mp (hUCovDirty he)
    rw [hiEq] at hkD
    have hki : k = i := Finset.mem_singleton.mp hkD
    rw [hki] at hkF
    have hbi : bare i e := (Finset.mem_filter.mp hkF).2
    refine ⟨heAdj.1, heAdj.2, hbi, ?_⟩
    intro j hji
    exact hUnotClean e he j (hAllOtherClean j hji)
  · have hTwo : 2 ≤ Dirty.card := by omega
    have hExists6 : ∃ i ∈ Dirty, 6 ≤ (U.filter fun e => bare i e).card := by
      by_contra hno
      have hall5 : ∀ i ∈ Dirty, (U.filter fun e => bare i e).card ≤ 5 := by
        intro i hi
        by_contra hgt
        exact hno ⟨i, hi, by omega⟩
      have hle := Finset.card_le_card hUCovDirty
      have hmul := Finset.card_biUnion_le_card_mul Dirty (fun k => U.filter fun e => bare k e) 5 hall5
      omega
    obtain ⟨i, hiD, hi6⟩ := hExists6
    have hiDirty : ¬ isClean i := (Finset.mem_filter.mp hiD).2
    have hErasePos : 0 < (Dirty.erase i).card := by
      rw [Finset.card_erase_of_mem hiD]
      omega
    obtain ⟨j, hjE⟩ := Finset.card_pos.mp hErasePos
    have hji : j ≠ i := (Finset.mem_erase.mp hjE).1
    have hjD : j ∈ Dirty := (Finset.mem_erase.mp hjE).2
    have hjDirty : ¬ isClean j := (Finset.mem_filter.mp hjD).2
    apply hMultiDirty C hWF hComp hOut hSing hDisj hle20
    refine ⟨i, j, hji.symm, hDirtyNotOut i hiDirty, hDirtyNotOut j hjDirty, hiDirty, hjDirty,
      U.filter fun e => bare i e, hi6, ?_⟩
    intro e he
    have heU := (Finset.mem_filter.mp he).1
    have hbi := (Finset.mem_filter.mp he).2
    have heE := (Finset.mem_sdiff.mp heU).1
    have heAdj := hEdgeAdj e heE
    exact ⟨heAdj.1, heAdj.2, hbi, hUnotClean e heU⟩
