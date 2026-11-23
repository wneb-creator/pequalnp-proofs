namespace PEqualNP.Outside.L_meta_997.UnionBudget

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.light

lemma union_output_budget_free {n : ℕ} {ι : Type*} [DecidableEq ι]
    (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (I : Finset ι) (S : ι → Finset (Fin n)) (o : ι → ℕ) (k : ℕ)
    (hk : 1 < k) (hIk : I.card ≤ k)
    (hcorrect : ∀ i ∈ I, ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < k →
      value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (M F : Finset ℕ)
    (hMcap : ∀ w ∈ M, ∀ i ∈ I, (singleSupp C w ∩ S i).card ≤ 1)
    (hfree : ∀ w ∈ F, ∀ (p : Fin n) (z : Fin n → Bool),
      value C (fun v => decide (v = p)) w = true → value C z w = true) :
    (I.biUnion S).card ≤ ((Finset.Ico n (n + C.size)) \ (M ∪ F)).card + I.card := by
  classical
  let H := (Finset.Ico n (n + C.size)) \ (M ∪ F)
  have hH : ∀ w ∈ H, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_sdiff.mp hw).1
  obtain ⟨B, hd, hB, hcut⟩ := cut C hG H hH (n + C.size) (I.image o)
    (fun w _ hw => (hH w hw).2)
  let D := B \ F
  have hsize : D.card ≤ H.card + I.card := by
    have hf := Finset.card_filter_le H (fun w => w < n + C.size)
    have hi := Finset.card_image_le (s := I) (f := o)
    have hD : D.card ≤ B.card := Finset.card_le_card Finset.sdiff_subset
    omega
  have hcap : ∀ w ∈ D, ∀ i ∈ I, (singleSupp C w ∩ S i).card ≤ 1 := by
    intro w hw i hi
    have hwB := (Finset.mem_sdiff.mp hw).1
    have hwF := (Finset.mem_sdiff.mp hw).2
    by_cases hm : w ∈ M
    · exact hMcap w hm i hi
    · by_contra! hc
      have hs : singleSupp C w ∩ S i ⊆ singleSupp C w := Finset.inter_subset_left
      have hr := singleSupp_gate C w (by have := Finset.card_le_card hs; omega)
      have hnot : w ∉ M ∪ F := by simp [hm, hwF]
      exact Finset.disjoint_left.mp hd hwB
        (Finset.mem_sdiff.mpr ⟨Finset.mem_Ico.mpr hr, hnot⟩)
  have hu : (I.biUnion S).card ≤ D.card := by
    apply union_boundary_bound C hG I S o k (by omega) hIk hcorrect D hcap
    intro i hi p hp z hz
    have hfire : value C (fun v => decide (v = p)) (o i) = true := by
      rw [hcorrect i hi]
      · simp [hp]
      · have he : Finset.univ.filter (fun v : Fin n => decide (v = p) = true) = {p} := by
          ext v
          simp
        rw [he, Finset.card_singleton]
        exact hk
    apply hcut (fun v => decide (v = p)) z _ (o i) (Finset.mem_image_of_mem o hi) hfire
    intro w hw hwp
    by_cases hwF : w ∈ F
    · exact hfree w hwF p z hwp
    · exact hz w (Finset.mem_sdiff.mpr ⟨hw, hwF⟩) ((mem_singleSupp C w p).mpr hwp)
  exact hu.trans hsize

end PEqualNP.Outside.L_meta_997.UnionBudget
