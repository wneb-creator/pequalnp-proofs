import PEqualNP.Outside.L_meta_2584

namespace PEqualNP.Outside.L_meta_2584.UpwardErase
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2584.Sharing

lemma overwrite_val_ge {n : ℕ} {C : Circuit} (hAO : AndOrOnly C)
    (j : ℕ) (r : Gate) (x : Fin n → Bool)
    (hrep : val C (List.ofFn x) (n + j) = true → replacementVal n C j r x = true)
    (w : ℕ) : val C (List.ofFn x) w = true →
      val (overwriteCircuit C j r) (List.ofFn x) w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · rw [val_input (n := n) (by simp) hn, val_input (n := n) (by simp) hn]
      exact id
    by_cases hw : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hk' : k < (overwriteCircuit C j r).gates.length := by
        simpa only [overwriteCircuit_length] using hk
      by_cases hjk : j = k
      · subst k
        rw [overwriteCircuit_val_self C hk r x]
        exact hrep
      have he : gateAt (overwriteCircuit C j r) k = gateAt C k :=
        overwriteCircuit_gateAt_other C j k hjk r
      rcases hAO _ (gateAt_mem hk) with hand | hor
      · rw [val_and (n := n) (by simp) hk hand,
          val_and (n := n) (by simp) hk' (by rw [he]; exact hand), he]
        intro hv i hi
        exact ⟨(hv i hi).1, ih i (hv i hi).1 (hv i hi).2⟩
      · rw [val_or (n := n) (by simp) hk hor,
          val_or (n := n) (by simp) hk' (by rw [he]; exact hor), he]
        rintro ⟨i, hi, hlt, hv⟩
        exact ⟨i, hi, hlt, ih i hlt hv⟩
    · rw [val_ge (n := n) (by simp) (by omega)]
      simp

lemma upward_or_context_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (g e : ℕ) (r : Gate)
    (hrval : ∀ x : Fin n → Bool, replacementVal n C g r x = val C (List.ofFn x) e)
    (hfront : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ w ∈ (gateAt C j).inputs, OrReaches n C w g →
      ∃ v ∈ (gateAt C j).inputs, ¬ OrReaches n C v g ∧
        ∀ x : Fin n → Bool, val C (List.ofFn x) e = true →
          val C (List.ofFn x) v = true → graphFun G ∅ x = true)
    (x : Fin n → Bool) (hfalse : graphFun G ∅ x = false) (w : ℕ) :
    val (overwriteCircuit C g r) (List.ofFn x) w = true →
      val C (List.ofFn x) w = true ∨
        (OrReaches n C w g ∧ val C (List.ofFn x) e = true) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · rw [val_input (n := n) (by simp) hn, val_input (n := n) (by simp) hn]
      exact Or.inl
    by_cases hw : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hk' : k < (overwriteCircuit C g r).gates.length := by
        simpa only [overwriteCircuit_length] using hk
      by_cases hgk : g = k
      · subst k
        rw [overwriteCircuit_val_self C hk r x, hrval]
        intro hv
        exact Or.inr ⟨(orReaches_iff n C g g).mpr ⟨hk, Or.inl rfl⟩, hv⟩
      have he : gateAt (overwriteCircuit C g r) k = gateAt C k :=
        overwriteCircuit_gateAt_other C g k hgk r
      rcases hAO.1 _ (gateAt_mem hk) with hand | hor
      · rw [val_and (n := n) (by simp) hk' (by rw [he]; exact hand), he]
        intro hv
        left
        apply (val_and (n := n) (by simp) hk hand).mpr
        intro i hi
        have hilt := hAO.2.1 k hk i hi
        refine ⟨hilt, ?_⟩
        rcases ih i hilt (hv i hi).2 with hold | ⟨hr, hetrue⟩
        · exact hold
        · obtain ⟨v, hvin, hvnot, hsound⟩ := hfront k hk hand i hi hr
          have hvlt := hAO.2.1 k hk v hvin
          have hvold : val C (List.ofFn x) v = true := by
            rcases ih v hvlt (hv v hvin).2 with hvold | ⟨hvr, _⟩
            · exact hvold
            · exact False.elim (hvnot hvr)
          have hyes := hsound x hetrue hvold
          rw [hfalse] at hyes
          cases hyes
      · rw [val_or (n := n) (by simp) hk' (by rw [he]; exact hor), he]
        rintro ⟨i, hi, hilt, hiv⟩
        rcases ih i hilt hiv with hold | ⟨hr, hetrue⟩
        · exact Or.inl ((val_or (n := n) (by simp) hk hor).mpr ⟨i, hi, hilt, hold⟩)
        · exact Or.inr ⟨(orReaches_iff n C k g).mpr
            ⟨hk, Or.inr ⟨hor, i, hi, hilt, hr⟩⟩, hetrue⟩
    · rw [val_ge (n := n) (by simp) (by rw [overwriteCircuit_length]; omega)]
      simp

lemma erase_and_with_frontier_guard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hf : circuitFun n C = graphFun G ∅)
    (g e : ℕ) (hg : g < C.gates.length) (hgand : (gateAt C g).op = GateOp.and)
    (he : e ∈ (gateAt C g).inputs)
    (hout : ¬ OrReaches n C C.output g)
    (hfront : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ w ∈ (gateAt C j).inputs, OrReaches n C w g →
      ∃ v ∈ (gateAt C j).inputs, ¬ OrReaches n C v g ∧
        ∀ x : Fin n → Bool, val C (List.ofFn x) e = true →
          val C (List.ofFn x) v = true → graphFun G ∅ x = true) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  let r : Gate := ⟨GateOp.or, [e, e]⟩
  let E := overwriteCircuit C g r
  have helt : e < n + g := hAO.2.1 g hg e he
  have hrback : ∀ i ∈ r.inputs, i < n + g := by
    intro i hi
    simp only [r, List.mem_cons, List.not_mem_nil, or_false, or_self] at hi
    simpa [hi] using helt
  have hrval (x : Fin n → Bool) : replacementVal n C g r x = val C (List.ofFn x) e := by
    rw [replacementVal_of_readsBack C g r x hrback]
    simp [r, GateOp.eval]
  have hE : IsAO2 n E := overwriteCircuit_isAO2 hAO g r (Or.inr rfl) hrback rfl
  have hge (x : Fin n → Bool) (w : ℕ) : val C (List.ofFn x) w = true →
      val E (List.ofFn x) w = true := by
    apply overwrite_val_ge hAO.1 g r x _ w
    rw [hrval]
    intro hv
    exact ((val_and (n := n) (by simp) hg hgand).mp hv e he).2
  have hEf : circuitFun n E = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      cases hF : graphFun G ∅ x with
      | true => rfl
      | false =>
        have hv := upward_or_context_bound G C hAO g e r hrval hfront x hF C.output hx
        rcases hv with hold | ⟨hr, _⟩
        · change circuitFun n C x = true at hold
          rw [hf, hF] at hold
          cases hold
        · exact False.elim (hout hr)
    · intro hx
      apply hge x C.output
      change circuitFun n C x = true
      rw [hf]
      exact hx
  have hgate (x : Fin n → Bool) : gateVal n E g x = val E (List.ofFn x) e := by
    change val (overwriteCircuit C g r) (List.ofFn x) (n + g) = _
    rw [overwriteCircuit_val_self C hg r x, hrval,
      overwriteCircuit_val_before C g r x e helt]
  obtain ⟨D, hD, hsize, hDf⟩ := MinimumPure.erase_equivalent_wire E hE
    (by simpa only [E, overwriteCircuit_length] using hg) helt hgate
  refine ⟨D, hD, ?_, hDf.trans hEf⟩
  simpa only [E, overwriteCircuit_size] using hsize

end PEqualNP.Outside.L_meta_2584.UpwardErase
