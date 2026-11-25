namespace PEqualNP.Outside.L_meta_4675.FirstJunk

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.TwoColour
  PEqualNP.Outside.L_meta_4675.MaskingNext PEqualNP.Outside.L_meta_4675.OneJunk

lemma operand_pure (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C) (q : ℕ)
    (hq : q < C.gates.length) (hqand : (gateAt C q).op = GateOp.and)
    (hfirst : ∀ k < q, ¬ IsDirtyAnd n G C k) (b : Fin 2) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue C n x (opnd C q b) = true ↔
      ∃ i ∈ side (n := n) C q b, x i = true := by
  constructor
  · intro hv
    have hw := ((operands n C hAO q hq).2 b).2
    rcases true_wire_source n C hAO x _ (by omega) hv with hi | ⟨k, hk, hr, hkand, _⟩
    · exact hi
    · have hc := operand_reach_inCone n C hAO q hq b k hr
      have hkq := inCone_lt n C q k hc
      have hb : BelowF G C k := by
        intro y hy
        cases hf : graphFun G ∅ y with
        | false => exact False.elim (hfirst k hkq ⟨hkand, hk, y, hy, hf⟩)
        | true => rfl
      exact False.elim (hTop k hk q hq hkand hb hqand hc)
  · rintro ⟨i, hi, hxi⟩
    exact orIn_true n C hAO x _ i hi hxi

lemma semantics (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C) (q : ℕ)
    (hq : q < C.gates.length) (hqand : (gateAt C q).op = GateOp.and)
    (hfirst : ∀ k < q, ¬ IsDirtyAnd n G C k) (x : Fin n → Bool) :
    gateVal n C q x = true ↔
      (∃ i ∈ side (n := n) C q 0, x i = true) ∧
      (∃ i ∈ side (n := n) C q 1, x i = true) := by
  rw [and_value n C hAO q hq hqand x,
    operand_pure n G C hAO hTop q hq hqand hfirst 0 x,
    operand_pure n G C hAO hTop q hq hqand hfirst 1 x]

lemma sides_nonempty (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C) (q : ℕ)
    (hq : IsDirtyAnd n G C q) (hfirst : ∀ k < q, ¬ IsDirtyAnd n G C k) :
    (side (n := n) C q 0).Nonempty ∧ (side (n := n) C q 1).Nonempty := by
  obtain ⟨x, hx, _⟩ := hq.2.2
  obtain ⟨⟨i, hi, _⟩, ⟨j, hj, _⟩⟩ :=
    (semantics n G C hAO hTop q hq.2.1 hq.1 hfirst x).mp hx
  exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩

lemma wire_one_colour (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (colour : ℕ → Bool)
    (hz : tCount n C colour = 0) (w : ℕ) (hw : w < n + C.gates.length) :
    (∀ i ∈ orIn n C w, colour i = false) ∨
      (∀ i ∈ orIn n C w, colour i = true) := by
  by_cases hin : w < n
  · rw [PEqualNP.Outside.L_meta_4675.OrReachAPI.orIn_input n C w hin]
    cases hc : colour w
    · left
      intro i hi
      have he : i = ⟨w, hin⟩ := Finset.mem_singleton.mp hi
      subst i
      exact hc
    · right
      intro i hi
      have he : i = ⟨w, hin⟩ := Finset.mem_singleton.mp hi
      subst i
      exact hc
  · obtain ⟨g, rfl⟩ : ∃ g, w = n + g := ⟨w - n, by omega⟩
    have hg : g < C.gates.length := by omega
    have hm : gateAt C g ∈ C.gates := by
      rw [gateAt_eq_getElem C g hg]
      exact List.getElem_mem hg
    rcases hAO.1 _ hm with hop | hop
    · have he := PEqualNP.Outside.L_meta_4675.OrReachAPI.orIn_non_or n C g hg
        (by rw [hop]; intro he; cases he)
      rw [he]
      simp
    · exact orIn_one_colour n C colour hz g hg hop

lemma sides_one_colour (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (colour : ℕ → Bool)
    (hz : tCount n C colour = 0) (q : ℕ) (hq : q < C.gates.length) (b : Fin 2) :
    (∀ i ∈ side (n := n) C q b, colour i = false) ∨
      (∀ i ∈ side (n := n) C q b, colour i = true) := by
  have hw := ((operands n C hAO q hq).2 b).2
  exact wire_one_colour n C hAO colour hz _ (by omega)

end PEqualNP.Outside.L_meta_4675.FirstJunk
