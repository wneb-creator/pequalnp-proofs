namespace PEqualNP.Outside.L_meta_4675.JunkDrop

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_4675.Pruning PEqualNP.Outside.L_meta_4675.ConeTrace

lemma mem_junk (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k : ℕ) :
    k ∈ junk G C ↔ k < C.gates.length ∧ IsDirtyAnd n G C k := by
  simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range]

lemma pruned_gate_semantic_embedding (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ∃ o : ℕ → ℕ,
      (∀ k < (pruned n q C).gates.length, o k < C.gates.length) ∧
      (∀ a b, a < b → b < (pruned n q C).gates.length → o a < o b) ∧
      (∀ k < (pruned n q C).gates.length,
        (gateAt (pruned n q C) k).op = (gateAt C (o k)).op) ∧
      (∀ k < (pruned n q C).gates.length, o k ≠ q) ∧
      (∀ k < (pruned n q C).gates.length, ∀ x : Fin n → Bool,
        gateVal n (pruned n q C) k x = true → gateVal n C (o k) x = true) := by
  obtain ⟨o, ht⟩ := compiled_trace n q C hAO
  refine ⟨o, ht.1, ht.2.1, ht.2.2.1, ?_, ?_⟩
  · intro k hk he
    have hq : q < C.gates.length := he ▸ ht.1 k hk
    have hlookup := ht.2.2.2.1 k hk
    rw [he, killed_alias n q C.gates hq] at hlookup
    cases hlookup
  · intro k hk x hv
    have halias := (compiled_valid_related n q C hAO (List.ofFn x) (by simp)).2.2 (n + o k)
    rw [ht.2.2.2.1 k hk] at halias
    have he : gateVal n (pruned n q C) k x =
        (forcedValues n q C (List.ofFn x)).getD (n + o k) false := halias
    apply forcedValues_below n q C hAO (List.ofFn x) (n + o k)
    exact he.symm.trans hv

lemma pruned_junk_card_le_erase (n q : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) :
    (junk G (pruned n q C)).card ≤ ((junk G C).erase q).card := by
  obtain ⟨o, hb, hs, hop, hne, hv⟩ := pruned_gate_semantic_embedding n q C hAO
  apply Finset.card_le_card_of_injOn o
  · intro k hk
    have hk' := (mem_junk n G (pruned n q C) k).mp hk
    apply Finset.mem_erase.mpr
    refine ⟨hne k hk'.1, (mem_junk n G C (o k)).mpr ⟨hb k hk'.1, ?_⟩⟩
    obtain ⟨hand, _, x, hx, hfalse⟩ := hk'.2
    exact ⟨(hop k hk'.1).symm.trans hand, hb k hk'.1, x, hv k hk'.1 x hx, hfalse⟩
  · intro a ha b hb' he
    have ha' := ((mem_junk n G (pruned n q C) a).mp ha).1
    have hb'' := ((mem_junk n G (pruned n q C) b).mp hb').1
    rcases Nat.lt_trichotomy a b with h | h | h
    · have := hs a b h hb''; omega
    · exact h
    · have := hs b a h ha'; omega

lemma pruned_junk_card_lt (n q : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hq : IsDirtyAnd n G C q) :
    (junk G (pruned n q C)).card < (junk G C).card := by
  have hqm : q ∈ junk G C := (mem_junk n G C q).mpr ⟨hq.2.1, hq⟩
  have he := Finset.card_erase_of_mem hqm
  have hle := pruned_junk_card_le_erase n q G C hAO
  have hpos := Finset.card_pos.mpr ⟨q, hqm⟩
  omega

end PEqualNP.Outside.L_meta_4675.JunkDrop
