namespace PEqualNP.Outside.L_meta_997.UnionBudget

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.light

lemma union_boundary_bound {n : ℕ} {ι : Type*} [DecidableEq ι]
    (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (I : Finset ι) (S : ι → Finset (Fin n)) (o : ι → ℕ) (k : ℕ)
    (hk : 0 < k) (hIk : I.card ≤ k)
    (hcorrect : ∀ i ∈ I, ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < k →
      value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (B : Finset ℕ)
    (hcap : ∀ w ∈ B, ∀ i ∈ I, (singleSupp C w ∩ S i).card ≤ 1)
    (hcut : ∀ i ∈ I, ∀ p ∈ S i, ∀ z : Fin n → Bool,
      (∀ w ∈ B, p ∈ singleSupp C w → value C z w = true) → value C z (o i) = true) :
    (I.biUnion S).card ≤ B.card := by
  classical
  let P := I.biUnion S
  let R : Fin n → ℕ → Prop := fun p w => p ∈ singleSupp C w
  have hrow : ∀ p ∈ P,
      (∃ w ∈ B, R p w ∧ ∀ q ∈ P, R q w → q = p) ∨
        k ≤ (B.filter (R p)).card := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
    exact LowDegree.exclusive_or_degree C hG (S i) P (o i) k (hcorrect i hi) B
      (fun w hw => hcap w hw i hi) (hcut i hi) p hpi
  apply Incidence.bounded_source_count P B R k hk
  · intro p hp
    rcases hrow p hp with ⟨w, hw, hpw, _⟩ | hd
    · exact ⟨w, hw, hpw⟩
    · have hpos : 0 < (B.filter (R p)).card := by omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
      exact ⟨w, (Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩
  · intro w hw
    have heq : P.filter (fun p => R p w) =
        I.biUnion (fun i => (S i).filter (fun p => R p w)) := by
      ext p
      simp only [P, Finset.mem_filter, Finset.mem_biUnion]
      constructor
      · rintro ⟨⟨i, hi, hpi⟩, hr⟩
        exact ⟨i, hi, hpi, hr⟩
      · rintro ⟨i, hi, hpi, hr⟩
        exact ⟨⟨i, hi, hpi⟩, hr⟩
    rw [heq]
    have hcol : ∀ i ∈ I, ((S i).filter (fun p => R p w)).card ≤ 1 := by
      intro i hi
      have he : (S i).filter (fun p => R p w) = singleSupp C w ∩ S i := by
        ext p
        simp [R, and_comm]
      rw [he]
      exact hcap w hw i hi
    have hh := Finset.card_biUnion_le_card_mul I
      (fun i => (S i).filter (fun p => R p w)) 1 hcol
    simp only [mul_one] at hh
    exact hh.trans hIk
  · intro p hp hd
    rcases hrow p hp with h | h
    · exact h
    · omega

lemma union_output_budget {n : ℕ} {ι : Type*} [DecidableEq ι]
    (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (I : Finset ι) (S : ι → Finset (Fin n)) (o : ι → ℕ) (k : ℕ)
    (hk : 1 < k) (hIk : I.card ≤ k)
    (hcorrect : ∀ i ∈ I, ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < k →
      value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (M : Finset ℕ)
    (hMcap : ∀ w ∈ M, ∀ i ∈ I, (singleSupp C w ∩ S i).card ≤ 1) :
    (I.biUnion S).card ≤ ((Finset.Ico n (n + C.size)) \ M).card + I.card := by
  classical
  let H := (Finset.Ico n (n + C.size)) \ M
  have hH : ∀ w ∈ H, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_sdiff.mp hw).1
  obtain ⟨B, hd, hB, hcut⟩ := cut C hG H hH (n + C.size) (I.image o)
    (fun w _ hw => (hH w hw).2)
  have hsize : B.card ≤ H.card + I.card := by
    have hf := Finset.card_filter_le H (fun w => w < n + C.size)
    have hi := Finset.card_image_le (s := I) (f := o)
    omega
  have hcap : ∀ w ∈ B, ∀ i ∈ I, (singleSupp C w ∩ S i).card ≤ 1 := by
    intro w hw i hi
    by_cases hm : w ∈ M
    · exact hMcap w hm i hi
    · by_contra! hc
      have hs : singleSupp C w ∩ S i ⊆ singleSupp C w := Finset.inter_subset_left
      have hr := singleSupp_gate C w (by have := Finset.card_le_card hs; omega)
      exact Finset.disjoint_left.mp hd hw
        (Finset.mem_sdiff.mpr ⟨Finset.mem_Ico.mpr hr, hm⟩)
  have hu : (I.biUnion S).card ≤ B.card := by
    apply union_boundary_bound C hG I S o k (by omega) hIk hcorrect B hcap
    intro i hi p hp z hz
    have hfire : value C (fun v => decide (v = p)) (o i) = true := by
      rw [hcorrect i hi]
      · simp [hp]
      · have he : Finset.univ.filter (fun v : Fin n => decide (v = p) = true) = {p} := by
          ext v
          simp
        rw [he, Finset.card_singleton]
        exact hk
    exact hcut (fun v => decide (v = p)) z
      (fun w hw hwp => hz w hw ((mem_singleSupp C w p).mpr hwp))
      (o i) (Finset.mem_image_of_mem o hi) hfire
  exact hu.trans hsize

end PEqualNP.Outside.L_meta_997.UnionBudget
