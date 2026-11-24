import PEqualNP.Outside.L_meta_1024

namespace PEqualNP.Outside.L_meta_1024_aux.PositiveCertificate

open PEqualNP.CircuitLowerBounds

def andCount (gs : List Gate) : ℕ := (gs.filter OneAndCircuit.isAnd).length

lemma andCount_snoc_and (gs : List Gate) (g : Gate) (hg : g.op = GateOp.and) :
    andCount (gs ++ [g]) = andCount gs + 1 := by
  simp [andCount, List.filter_append, OneAndCircuit.isAnd, hg]

lemma andCount_snoc_or (gs : List Gate) (g : Gate) (hg : g.op = GateOp.or) :
    andCount (gs ++ [g]) = andCount gs := by
  simp [andCount, List.filter_append, OneAndCircuit.isAnd, hg]

lemma positive_components {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin n → Bool) :
    ∃ (label : Fin n → ℕ) (wire : ℕ → ℕ),
      (∀ S : Finset (Fin n), S.card ≤ (S.image label).card + andCount gs) ∧
      ∀ i, Cut.cutVal n ∅ gs x i = true → ∀ y : Fin n → Bool,
        (∀ t, label t = wire i → x t = true → y t = true) →
        Cut.cutVal n ∅ gs y i = true := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨Fin.val, id, ?_, ?_⟩
    · intro S
      simp [andCount, Finset.card_image_of_injective _ Fin.val_injective]
    · intro i hi y hy
      rw [Cut.cutVal_nil] at hi ⊢
      by_cases hin : i < n
      · simp only [ite_true, Cut.source_eq, hin, dite_true] at hi ⊢
        exact hy ⟨i, hin⟩ rfl hi
      · simp [hin] at hi
  | append_singleton gs g ih =>
    have hgg := hg g (by simp)
    obtain ⟨label, wire, hcount, htrue⟩ := ih (fun h hh => hg h (by simp [hh]))
    rcases hgg.1 with hand | hor
    · obtain ⟨a, b, hinputs⟩ := Cut.two_inputs g.inputs hgg.2
      let merge (k : ℕ) := if k = wire b then wire a else k
      have ha : merge (wire a) = wire a := by simp [merge]
      have hb : merge (wire b) = wire a := by simp [merge]
      refine ⟨merge ∘ label, fun i => if i = n + gs.length then wire a else merge (wire i), ?_, ?_⟩
      · intro S
        have hsub : S.image label ⊆ insert (wire b) (S.image (merge ∘ label)) := by
          intro v hv
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
          by_cases he : label t = wire b
          · simp [he]
          · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, ht, by simp [merge, he]⟩)
        have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
        have hs := hcount S
        rw [andCount_snoc_and gs g hand]
        omega
      · intro i hi y hy
        rw [Cut.cutVal_snoc] at hi ⊢
        by_cases hie : i = n + gs.length
        · simp only [hie, ite_true, Finset.notMem_empty, ite_false, hand, GateOp.eval,
            List.all_eq_true, List.mem_map, id_eq] at hi ⊢
          intro v hv
          obtain ⟨j, hj, rfl⟩ := hv
          apply htrue j (hi _ ⟨j, hj, rfl⟩) y
          intro t ht htx
          apply hy t
          · simp only [Function.comp_apply, hie, ite_true]
            rw [ht]
            rcases hinputs j hj with rfl | rfl
            · exact ha
            · exact hb
          · exact htx
        · simp only [hie, ite_false] at hi ⊢
          apply htrue i hi y
          intro t ht htx
          apply hy t
          · simp only [Function.comp_apply, hie, ite_false]
            rw [ht]
          · exact htx
    · by_cases hnew : g.op.eval (g.inputs.map fun j => Cut.cutVal n ∅ gs x j) = true
      · have hget : ∃ a ∈ g.inputs, Cut.cutVal n ∅ gs x a = true := by
          have he := hnew
          simp only [hor, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at he
          obtain ⟨v, ⟨a, ha, rfl⟩, ht⟩ := he
          exact ⟨a, ha, ht⟩
        obtain ⟨a, ha, hax⟩ := hget
        refine ⟨label, fun i => if i = n + gs.length then wire a else wire i, ?_, ?_⟩
        · intro S
          rw [andCount_snoc_or gs g hor]
          exact hcount S
        · intro i hi y hy
          rw [Cut.cutVal_snoc] at hi ⊢
          by_cases hie : i = n + gs.length
          · simp only [hie, ite_true, Finset.notMem_empty, ite_false, hor, GateOp.eval,
              List.any_eq_true, List.mem_map, id_eq]
            have hay := htrue a hax y (by
              intro t ht htx
              exact hy t (by simpa [hie] using ht) htx)
            exact ⟨true, ⟨a, ha, hay⟩, rfl⟩
          · simp only [hie, ite_false] at hi ⊢
            exact htrue i hi y (fun t ht htx => hy t (by simpa [hie] using ht) htx)
      · refine ⟨label, fun i => if i = n + gs.length then 0 else wire i, ?_, ?_⟩
        · intro S
          rw [andCount_snoc_or gs g hor]
          exact hcount S
        · intro i hi y hy
          rw [Cut.cutVal_snoc] at hi ⊢
          by_cases hie : i = n + gs.length
          · simp only [hie, ite_true, Finset.notMem_empty, ite_false] at hi
            exact (hnew hi).elim
          · simp only [hie, ite_false] at hi ⊢
            exact htrue i hi y (fun t ht htx => hy t (by simpa [hie] using ht) htx)

lemma small_positive_certificate {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin n → Bool) (o : ℕ) (hx : Global.val gs x o = true) :
    ∃ T : Finset (Fin n),
      (∀ p ∈ T, x p = true) ∧ T.card ≤ andCount gs + 1 ∧
      Global.val gs (fun p => decide (p ∈ T)) o = true := by
  classical
  obtain ⟨label, wire, hcount, htrue⟩ := positive_components gs hg x
  let T := Finset.univ.filter (fun p => label p = wire o ∧ x p = true)
  have hT : ∀ p ∈ T, label p = wire o ∧ x p = true := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hsmall : (T.image label).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    exact (hT p hp).1.trans (hT q hq).1.symm
  refine ⟨T, fun p hp => (hT p hp).2, ?_, ?_⟩
  · have hc := hcount T
    omega
  · change Circuit.eval ⟨gs, o⟩ (List.ofFn (fun p => decide (p ∈ T))) = true
    rw [← Cut.cut_empty]
    apply htrue o
    · change Circuit.eval ⟨gs, o⟩ (List.ofFn x) = true at hx
      simpa only [Cut.cut_empty] using hx
    · intro p hp hpx
      apply decide_eq_true
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp, hpx⟩

end PEqualNP.Outside.L_meta_1024_aux.PositiveCertificate

namespace PEqualNP.Outside.L_meta_1024_aux.PositiveCertificate

open PEqualNP.CircuitLowerBounds

lemma abnormal_and_lower (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ x, Support.Band x → Global.val gs x o = Support.target w x)
    (habnormal : Global.val gs (Global.Zof (Global.line w)) o = true) :
    8 ≤ andCount gs := by
  by_contra! hsmall
  obtain ⟨T, hT, hcard, htrue⟩ := small_positive_certificate gs hg
    (Global.Zof (Global.line w)) o habnormal
  have hTsub : T ⊆ Finset.univ \ Support.line w := by
    intro p hp
    have hn : p ∉ Support.line w := by
      have hpZ := hT p hp
      change decide (p ∉ Global.line w) = true at hpZ
      have hpnot : p ∉ Global.line w := of_decide_eq_true hpZ
      simpa only [Global.line, Support.line] using hpnot
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩
  obtain ⟨Y, hTY, hYsub, hYcard⟩ := Clamp.extend_eight w T hTsub (by omega)
  have hy := Bridge.val_mono gs (fun g hm => (hg g hm).1)
    (fun p => decide (p ∈ T)) (Clamp.fromTrue Y) (by
      intro p hp
      have hpT : p ∈ T := by simpa using hp
      exact decide_eq_true (hTY hpT)) o htrue
  rw [hcorrect _ (Clamp.fromTrue_band Y hYcard), Clamp.fromTrue_misses w Y hYsub] at hy
  cases hy

end PEqualNP.Outside.L_meta_1024_aux.PositiveCertificate
