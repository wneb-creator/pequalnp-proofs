import PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

lemma raUnfactoredLower (n : ℕ) (C P : Circuit) (hm : Monotone2 P) (hr : ReadsBack n P)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (R A : Finset ℕ) (hR : R.Nonempty)
    (term : ℕ → Fin (n + P.size) ⊕ (Fin (n + P.size) × Fin (n + P.size)))
    (hsem : ∀ z : Fin n → Bool,
      circuitFun n C z = (R.toList.map term).any
        (fun t => taTerm t (fun i => (P.wires (List.ofFn z)).getD i false)))
    (hcost : ∀ w ∈ R, taTermCost (term w) ≤ if w ∈ A then 1 else 0) :
    C.size + 1 ≤ P.size + R.card + A.card := by
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

lemma raAllTailAndRoots (n : ℕ) (C : Circuit) (hm : Monotone2 C) (hr : ReadsBack n C)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length)
    (hd : frDirty n (fun z => circuitFun n C z = false) C j)
    (hlast : ∀ k < C.gates.length,
      frDirty n (fun z => circuitFun n C z = false) C k → k ≤ j) :
    raTailAnd n C (j + 1) ⊆ otFrontier n C (j + 1) := by
  classical
  let p := j + 1
  have hp : p ≤ C.gates.length := hj
  let P := raPrefix C p
  have hPs : P.size = p := raPrefix_size C p hp
  let R := otFrontier n C p
  let A := raTailAnd n C p
  have hKR : raReaderRoots n C j ⊆ R := Finset.filter_subset _ _
  have hcard := raMinimumReaderOne n C hm hr hmin j hj hd hlast
  have hR : R.Nonempty :=
    Finset.Nonempty.mono hKR (Finset.card_pos.mp (by rw [hcard]; omega))
  let u : Fin (n + P.size) := ⟨n + j, by rw [hPs]; dsimp [p]; omega⟩
  have hout := saMinimumOutputValid n C hmin j hj
  have hterms : ∀ w : ℕ,
      ∃ t : Fin (n + P.size) ⊕ (Fin (n + P.size) × Fin (n + P.size)),
        w ∈ R →
          (∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD w false =
            taTerm t (fun i => (P.wires (List.ofFn z)).getD i false)) ∧
          taTermCost t ≤ if w ∈ A ∩ R then 1 else 0 := by
    intro w
    by_cases hw : w ∈ R
    · rcases otFrontier_roots n C hm hr p hp hout w hw with hlow | htail
      · let v : Fin (n + P.size) := ⟨w, by rw [hPs]; exact hlow⟩
        refine ⟨.inl v, fun _ => ⟨?_, ?_⟩⟩
        · intro z
          exact (raPrefix_wire n C p hp z w hlow).symm
        · simp [taTermCost]
      · obtain ⟨k, hkp, hk, hop, hwk⟩ := htail
        obtain ⟨a, b, hins, _, ha, hb⟩ :=
          frAndAfterLatest n C hm hr hmin j hd hlast k (by dsimp [p] at hkp; omega) hk hop
        let va : Fin (n + P.size) := ⟨a, by rw [hPs]; dsimp [p]; omega⟩
        let vb : Fin (n + P.size) := ⟨b, by rw [hPs]; dsimp [p]; omega⟩
        refine ⟨.inr (va, vb), fun _ => ⟨?_, ?_⟩⟩
        · intro z
          subst w
          change (C.wires (List.ofFn z)).getD (n + k) false =
            (((raPrefix C p).wires (List.ofFn z)).getD a false &&
              ((raPrefix C p).wires (List.ofFn z)).getD b false)
          rw [raPrefix_wire n C p hp z a (by dsimp [p]; omega),
            raPrefix_wire n C p hp z b (by dsimp [p]; omega), frGateEval n C hr k hk z, hop, hins]
          simp [GateOp.eval]
        · have hwA : w ∈ A := (raTailAnd_mem n C p w).mpr ⟨k, hkp, hk, hop, hwk⟩
          simp [taTermCost, hwA, hw]
    · exact ⟨.inl u, fun h => (hw h).elim⟩
  choose term hterm using hterms
  have hlower : C.size + 1 ≤ P.size + R.card + (A ∩ R).card := by
    apply raUnfactoredLower n C P (raPrefix_mono C p hm) (raPrefix_reads n C p hr)
      hmin R (A ∩ R) hR term
    · intro z
      rw [otFrontier_semantics n C hr p hp z, Bool.eq_iff_iff, ofAny_true]
      simp only [List.any_map, List.any_eq_true, Finset.mem_toList]
      constructor
      · rintro ⟨w, hw, ht⟩
        exact ⟨w, hw, ((hterm w hw).1 z).symm.trans ht⟩
      · rintro ⟨w, hw, ht⟩
        exact ⟨w, hw, ((hterm w hw).1 z).trans ht⟩
    · intro w hw
      exact (hterm w hw).2
  have hupper := raTailAnd_budget n C hm p hp
  change P.size + R.card + A.card ≤ C.size + 1 at hupper
  have hcardle : A.card ≤ (A ∩ R).card := by omega
  have heq : A ∩ R = A := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hcardle
  intro w hw
  have hw' : w ∈ A ∩ R := by rw [heq]; exact hw
  exact (Finset.mem_inter.mp hw').2

lemma raMinimumUniqueReader (n : ℕ) (C : Circuit) (hm : Monotone2 C) (hr : ReadsBack n C)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length)
    (hd : frDirty n (fun z => circuitFun n C z = false) C j)
    (hlast : ∀ k < C.gates.length,
      frDirty n (fun z => circuitFun n C z = false) C k → k ≤ j) :
    ∃ k, k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs ∧
      ∀ l < C.gates.length, n + j ∈ (gateAt C l).inputs → l = k := by
  classical
  have hcard := raMinimumReaderOne n C hm hr hmin j hj hd hlast
  obtain ⟨w, hsingleton⟩ := Finset.card_eq_one.mp hcard
  have hwK : w ∈ raReaderRoots n C j := by rw [hsingleton]; simp
  have hwA := (Finset.mem_filter.mp hwK).2.1
  obtain ⟨k, hkp, hk, hop, hwk⟩ := (raTailAnd_mem n C (j + 1) w).mp hwA
  have hkread : n + j ∈ (gateAt C k).inputs := by
    simpa only [hwk, Nat.add_sub_cancel_left] using (Finset.mem_filter.mp hwK).2.2
  refine ⟨k, hk, hkread, ?_⟩
  intro l hl hread
  have hjl : j < l := by
    have hh := hr l hl (n + j) hread
    omega
  obtain ⟨_, _, hol, _⟩ := frMinimumLatestReaders n C hm hr hmin j hd hlast l hl hread
  have hlA : n + l ∈ raTailAnd n C (j + 1) :=
    (raTailAnd_mem n C (j + 1) (n + l)).mpr ⟨l, by omega, hl, hol, rfl⟩
  have hlR := raAllTailAndRoots n C hm hr hmin j hj hd hlast hlA
  have hlK : n + l ∈ raReaderRoots n C j := by
    apply Finset.mem_filter.mpr
    refine ⟨hlR, hlA, ?_⟩
    simpa using hread
  rw [hsingleton, Finset.mem_singleton] at hlK
  omega

end PEqualNP.Outside.L_meta_3451
