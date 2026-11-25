namespace PEqualNP.Outside.L_meta_4675.JunkDrop

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_4675.Pruning PEqualNP.Outside.L_meta_4675.StarAppend
  PEqualNP.Outside.L_meta_4675.StarAppendOptional

lemma gateVal_append_prefix (n : ℕ) (C D : Circuit) (gs : List Gate)
    (hg : D.gates = C.gates ++ gs) (k : ℕ) (hk : k < C.gates.length)
    (x : Fin n → Bool) : gateVal n D k x = gateVal n C k x := by
  change (vals D.gates (List.ofFn x)).getD (n + k) false =
    (vals C.gates (List.ofFn x)).getD (n + k) false
  rw [hg, vals_append]
  apply PEqualNP.Outside.L_meta_4675.MaskingNext.foldl_wireStep_prefix
  rw [vals_length]
  simp only [List.length_ofFn]
  omega

lemma restore_gate_old (n : ℕ) (C : Circuit) (a b k : ℕ) (hk : k < C.gates.length) :
    gateAt (restoreStar n C a b) k = gateAt C k := by
  unfold restoreStar
  split_ifs
  · exact gateAt_old n C a b k hk
  · exact PEqualNP.Outside.L_meta_4675.OrReachAPI.gateAt_append_old _ _ k hk

lemma restore_gateVal_old (n : ℕ) (C : Circuit) (a b k : ℕ)
    (hk : k < C.gates.length) (x : Fin n → Bool) :
    gateVal n (restoreStar n C a b) k x = gateVal n C k x := by
  unfold restoreStar
  split_ifs
  · exact gateVal_append_prefix n C _ _ rfl k hk x
  · exact gateVal_append_prefix n C _ _ rfl k hk x

lemma restore_new_and_index (n : ℕ) (C : Circuit) (a b k : ℕ)
    (hk : k < (restoreStar n C a b).gates.length) (hlo : C.gates.length ≤ k)
    (hand : (gateAt (restoreStar n C a b) k).op = GateOp.and) : k = C.gates.length := by
  by_cases ho : C.output < n + C.gates.length
  · simp only [restoreStar, if_pos ho] at hk hand
    have hk' : k < C.gates.length + 2 := by simpa [appendStar] using hk
    have he : k = C.gates.length ∨ k = C.gates.length + 1 := by omega
    rcases he with he | he
    · exact he
    · rw [he, gateAt_output] at hand
      cases hand
  · simp only [restoreStar, if_neg ho] at hk
    have hk' : k < C.gates.length + 1 := by simpa [appendAnd] using hk
    omega

lemma restore_junk_card_le (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (a b : ℕ)
    (hbelow : BelowF G (restoreStar n C a b) C.gates.length) :
    (junk G (restoreStar n C a b)).card ≤ (junk G C).card := by
  apply Finset.card_le_card
  intro k hk
  obtain ⟨hk, hand, _, x, hx, hf⟩ := (mem_junk n G (restoreStar n C a b) k).mp hk
  by_cases hko : k < C.gates.length
  · apply (mem_junk n G C k).mpr
    refine ⟨hko, ?_, hko, x, ?_, hf⟩
    · rwa [restore_gate_old n C a b k hko] at hand
    · exact (restore_gateVal_old n C a b k hko x).symm.trans hx
  · have he := restore_new_and_index n C a b k hk (by omega) hand
    subst k
    have hc := hbelow x hx
    rw [hf] at hc
    cases hc

lemma restore_and_reaches_output (n : ℕ) (C : Circuit) (a b : ℕ) :
    OrReaches n (restoreStar n C a b) (restoreStar n C a b).output C.gates.length := by
  unfold restoreStar
  split_ifs
  · let D := appendStar n C a b
    have h := PEqualNP.Outside.L_meta_4675.MaskingNext.orReaches_step n D
      (C.gates.length + 1) (n + C.gates.length) C.gates.length
      (by simp [D, appendStar]) (by rw [gateAt_output])
      (by rw [gateAt_output]; simp) (by omega)
      (PEqualNP.Outside.L_meta_4675.MaskingNext.orReaches_self n D C.gates.length
        (by simp [D, appendStar]))
    simpa [D, appendStar, Nat.add_assoc] using h
  · exact PEqualNP.Outside.L_meta_4675.MaskingNext.orReaches_self n
      (appendAnd n C a b) C.gates.length (by simp [appendAnd])

lemma restore_new_and_below (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (a b : ℕ) (hAO : IsAO2 n (restoreStar n C a b))
    (hfun : circuitFun n (restoreStar n C a b) = graphFun G ∅) :
    BelowF G (restoreStar n C a b) C.gates.length := by
  intro x hx
  have hv := PEqualNP.Outside.L_meta_4675.MaskingNext.orReaches_true n
    (restoreStar n C a b) hAO x C.gates.length hx _ (restore_and_reaches_output n C a b)
  exact (congrFun hfun x).symm.trans hv

lemma prune_restore_junk_card_lt (n q : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (a b : ℕ) (hAO : IsAO2 n C) (hq : IsDirtyAnd n G C q)
    (hD : IsAO2 n (restoreStar n (pruned n q C) a b))
    (hfun : circuitFun n (restoreStar n (pruned n q C) a b) = graphFun G ∅) :
    (junk G (restoreStar n (pruned n q C) a b)).card < (junk G C).card :=
  lt_of_le_of_lt (restore_junk_card_le n G (pruned n q C) a b
    (restore_new_and_below n G (pruned n q C) a b hD hfun))
    (pruned_junk_card_lt n q G C hAO hq)

end PEqualNP.Outside.L_meta_4675.JunkDrop
