namespace PEqualNP.Outside.L_meta_997.LowDegree

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.light

lemma exclusive_or_degree {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S U : Finset (Fin n)) (o k : ℕ)
    (hcorrect : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < k →
      value C x o = decide (∃ p ∈ S, x p = true))
    (B : Finset ℕ)
    (hcap : ∀ w ∈ B, (singleSupp C w ∩ S).card ≤ 1)
    (hcut : ∀ p ∈ S, ∀ z : Fin n → Bool,
      (∀ w ∈ B, p ∈ singleSupp C w → value C z w = true) → value C z o = true)
    (p : Fin n) (hpS : p ∈ S) :
    (∃ w ∈ B, p ∈ singleSupp C w ∧
      ∀ q ∈ U, q ∈ singleSupp C w → q = p) ∨
      k ≤ (B.filter (fun w => p ∈ singleSupp C w)).card := by
  classical
  by_cases hpure : ∃ w ∈ B, p ∈ singleSupp C w ∧
      ∀ q ∈ U, q ∈ singleSupp C w → q = p
  · exact Or.inl hpure
  · right
    by_contra! hsmall
    let N := B.filter (fun w => p ∈ singleSupp C w)
    have hout (w : {w // w ∈ N}) : ∃ q : Fin n,
        q ∈ U ∧ q ∈ singleSupp C w.val ∧ q ∉ S := by
      have hw := Finset.mem_filter.mp w.property
      have hother : ∃ q ∈ U, q ∈ singleSupp C w.val ∧ q ≠ p := by
        by_contra! hnone
        exact hpure ⟨w.val, hw.1, hw.2, hnone⟩
      obtain ⟨q, hqU, hqw, hqp⟩ := hother
      refine ⟨q, hqU, hqw, ?_⟩
      intro hqS
      have heq : q = p := Finset.card_le_one.mp (hcap w.val hw.1)
        q (Finset.mem_inter.mpr ⟨hqw, hqS⟩) p (Finset.mem_inter.mpr ⟨hw.2, hpS⟩)
      exact hqp heq
    choose qs hqs using hout
    let V : Finset (Fin n) := N.attach.image qs
    let z : Fin n → Bool := fun v => decide (v ∈ V)
    have hVcard : V.card < k := by
      have h := Finset.card_image_le (s := N.attach) (f := qs)
      simp only [Finset.card_attach] at h
      change V.card ≤ N.card at h
      change N.card < k at hsmall
      omega
    have hweight : (Finset.univ.filter (fun v => z v = true)).card < k := by
      simpa [z] using hVcard
    have hVS : ∀ q ∈ V, q ∉ S := by
      intro q hq
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hq
      exact (hqs w).2.2
    have hzfalse : value C z o = false := by
      rw [hcorrect z hweight]
      simp only [decide_eq_false_iff_not, not_exists]
      intro q hq
      exact hVS q (by simpa [z] using hq.2) hq.1
    have hztrue : value C z o = true := by
      apply hcut p hpS z
      intro w hw hpw
      let d : {w // w ∈ N} := ⟨w, Finset.mem_filter.mpr ⟨hw, hpw⟩⟩
      apply value_mono C hG (fun v => decide (v = qs d)) z _ w
        ((mem_singleSupp C w (qs d)).mp (hqs d).2.1)
      intro v hv
      have hv' : v = qs d := by simpa using hv
      subst v
      simp only [z, decide_eq_true_eq]
      exact Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩
    rw [hzfalse] at hztrue
    exact Bool.false_ne_true hztrue

end PEqualNP.Outside.L_meta_997.LowDegree
