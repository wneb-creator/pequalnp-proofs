import PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

lemma raUnfactoredContradiction (n : ℕ) (C P : Circuit) (hm : Monotone2 P) (hr : ReadsBack n P)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (R A : Finset ℕ) (hR : R.Nonempty)
    (term : ℕ → Fin (n + P.size) ⊕ (Fin (n + P.size) × Fin (n + P.size)))
    (hsem : ∀ z : Fin n → Bool,
      circuitFun n C z = (R.toList.map term).any
        (fun t => taTerm t (fun i => (P.wires (List.ofFn z)).getD i false)))
    (hcost : ∀ w ∈ R, taTermCost (term w) ≤ if w ∈ A then 1 else 0)
    (hbudget : P.size + R.card + A.card ≤ C.size) : False := by
  classical
  obtain ⟨t, ts, ht⟩ : ∃ t ts, R.toList.map term = t :: ts := by
    cases hl : R.toList.map term with
    | nil =>
      have hh := congrArg List.length hl
      simp only [List.length_map, Finset.length_toList, List.length_nil] at hh
      exact (Finset.card_ne_zero.mpr hR hh).elim
    | cons t ts => exact ⟨t, ts, rfl⟩
  have hlen : ts.length + 1 = R.card := by
    have hh := congrArg List.length ht
    simpa only [List.length_map, Finset.length_toList, List.length_cons] using hh.symm
  have hsum : taTermCost t + (ts.map taTermCost).sum ≤ A.card := by
    have he : ((R.toList.map term).map taTermCost).sum = ∑ w ∈ R, taTermCost (term w) := by
      simp [List.map_map]
    rw [ht] at he
    simp only [List.map_cons, List.sum_cons] at he
    rw [he]
    calc
      _ ≤ ∑ w ∈ R, if w ∈ A then 1 else 0 := Finset.sum_le_sum hcost
      _ = (R ∩ A).card := by simp
      _ ≤ A.card := Finset.card_le_card Finset.inter_subset_right
  have hb := taAttach ts (taTerm t) (taTermCost t) (taTermBld t)
  obtain ⟨D, hdm, hdr, hds, hdf⟩ := taAppend n P hm hr _ _ hb
  have heq : circuitFun n D = circuitFun n C := by
    funext z
    rw [hdf z, hsem z, ht]
    rfl
  have hle := hmin D hdm hdr heq
  omega

lemma raMinimumReaderOne (n : ℕ) (C : Circuit) (hm : Monotone2 C) (hr : ReadsBack n C)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length)
    (hd : frDirty n (fun z => circuitFun n C z = false) C j)
    (hlast : ∀ k < C.gates.length,
      frDirty n (fun z => circuitFun n C z = false) C k → k ≤ j) :
    (raReaderRoots n C j).card = 1 := by
  classical
  have hout := saMinimumOutputValid n C hmin j hj
  have hle := raMinimumReaderCard n C hm hr hmin j hj hout hd hlast
  by_contra hnot
  have hz : (raReaderRoots n C j).card = 0 := by omega
  have hK : raReaderRoots n C j = ∅ := Finset.card_eq_zero.mp hz
  let R := otFrontier n C (j + 1)
  let A := raTailAnd n C (j + 1)
  have hp : j + 1 ≤ C.gates.length := hj
  have hR : R.Nonempty := by
    by_contra hn
    have hRE : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    let D : Circuit := ⟨[], n⟩
    have hfun : circuitFun n D = circuitFun n C := by
      funext z
      have hc : circuitFun n C z = false := by
        rw [otFrontier_semantics n C hr (j + 1) hp z]
        change ofAny _ R = false
        rw [hRE]
        simp [ofAny]
      have hd' : circuitFun n D z = false := by
        change (List.ofFn z).getD n false = false
        apply List.getD_eq_default
        simp
      exact hd'.trans hc.symm
    have hdm : Monotone2 D := by intro g hg; simp [D] at hg
    have hdr : ReadsBack n D := by intro k hk; simp [D] at hk
    have hs := hmin D hdm hdr hfun
    change C.gates.length ≤ 0 at hs
    omega
  have hU : n + j ∉ R := by
    intro hw
    obtain ⟨z, hf, ht⟩ := hd
    have hc := otFrontier_safe n C hr (j + 1) hp (n + j) hw z ht
    rw [hf] at hc
    cases hc
  let P := raPrefix C j
  have hPs : P.size = j := raPrefix_size C j hj.le
  have hterms : ∀ w ∈ R,
      ∃ t : Fin (n + P.size) ⊕ (Fin (n + P.size) × Fin (n + P.size)),
        (∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD w false =
          taTerm t (fun i => (P.wires (List.ofFn z)).getD i false)) ∧
        taTermCost t ≤ if w ∈ A then 1 else 0 := by
    intro w hw
    rcases otFrontier_roots n C hm hr (j + 1) hp hout w hw with hlow | htail
    · have hne : w ≠ n + j := by intro he; subst w; exact hU hw
      have hlt : w < n + j := by omega
      let v : Fin (n + P.size) := ⟨w, by rw [hPs]; exact hlt⟩
      refine ⟨.inl v, ?_, ?_⟩
      · intro z
        exact (raPrefix_wire n C j hj.le z w hlt).symm
      · simp [taTermCost]
    · obtain ⟨k, hkp, hk, hop, hwk⟩ := htail
      have hnotread : n + j ∉ (gateAt C k).inputs := by
        intro hread
        have hwK : w ∈ raReaderRoots n C j := by
          apply Finset.mem_filter.mpr
          refine ⟨hw, (raTailAnd_mem n C (j + 1) w).mpr ⟨k, hkp, hk, hop, hwk⟩, ?_⟩
          simpa only [hwk, Nat.add_sub_cancel_left] using hread
        rw [hK] at hwK
        simp at hwK
      obtain ⟨a, b, hins, _, ha, hb⟩ :=
        frAndAfterLatest n C hm hr hmin j hd hlast k (by omega) hk hop
      have hane : a ≠ n + j := by intro he; apply hnotread; simp [hins, he]
      have hbne : b ≠ n + j := by intro he; apply hnotread; simp [hins, he]
      have halt : a < n + j := by omega
      have hblt : b < n + j := by omega
      let va : Fin (n + P.size) := ⟨a, by rw [hPs]; exact halt⟩
      let vb : Fin (n + P.size) := ⟨b, by rw [hPs]; exact hblt⟩
      refine ⟨.inr (va, vb), ?_, ?_⟩
      · intro z
        subst w
        change (C.wires (List.ofFn z)).getD (n + k) false =
          (((raPrefix C j).wires (List.ofFn z)).getD a false &&
            ((raPrefix C j).wires (List.ofFn z)).getD b false)
        rw [raPrefix_wire n C j hj.le z a halt, raPrefix_wire n C j hj.le z b hblt,
          frGateEval n C hr k hk z, hop, hins]
        simp [GateOp.eval]
      · have hwA : w ∈ A := (raTailAnd_mem n C (j + 1) w).mpr ⟨k, hkp, hk, hop, hwk⟩
        simp [taTermCost, hwA]
  obtain ⟨w0, hw0⟩ := hR
  obtain ⟨t0, _⟩ := hterms w0 hw0
  have hchoose : ∀ w : ℕ, ∃ t : Fin (n + P.size) ⊕ (Fin (n + P.size) × Fin (n + P.size)),
      w ∈ R →
        (∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD w false =
          taTerm t (fun i => (P.wires (List.ofFn z)).getD i false)) ∧
        taTermCost t ≤ if w ∈ A then 1 else 0 := by
    intro w
    by_cases hw : w ∈ R
    · obtain ⟨t, ht⟩ := hterms w hw
      exact ⟨t, fun _ => ht⟩
    · exact ⟨t0, fun h => (hw h).elim⟩
  choose term hterm using hchoose
  apply raUnfactoredContradiction n C P (raPrefix_mono C j hm) (raPrefix_reads n C j hr)
    hmin R A ⟨w0, hw0⟩ term
  · intro z
    rw [otFrontier_semantics n C hr (j + 1) hp z, Bool.eq_iff_iff, ofAny_true]
    simp only [List.any_map, List.any_eq_true, Finset.mem_toList]
    constructor
    · rintro ⟨w, hw, ht⟩
      exact ⟨w, hw, ((hterm w hw).1 z).symm.trans ht⟩
    · rintro ⟨w, hw, ht⟩
      exact ⟨w, hw, ((hterm w hw).1 z).trans ht⟩
  · intro w hw
    exact (hterm w hw).2
  · have hb := raTailAnd_budget n C hm (j + 1) hp
    rw [raPrefix_size C (j + 1) hp] at hb
    rw [hPs]
    change j + R.card + A.card ≤ C.size
    change j + 1 + R.card + A.card ≤ C.size + 1 at hb
    omega

end PEqualNP.Outside.L_meta_3451
