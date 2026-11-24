import PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

lemma raFiniteFactor (n : ℕ) (C P : Circuit) (hm : Monotone2 P) (hr : ReadsBack n P)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (R A K : Finset ℕ) (hKR : K ⊆ R) (hKA : K ⊆ A)
    (u : Fin (n + P.size)) (partner : ℕ → Fin (n + P.size))
    (term : ℕ → Fin (n + P.size) ⊕ (Fin (n + P.size) × Fin (n + P.size)))
    (hsem : ∀ z : Fin n → Bool,
      let x : Fin (n + P.size) → Bool := fun i => (P.wires (List.ofFn z)).getD i false
      circuitFun n C z =
        ((K.toList.map partner).any (fun w => x u && x w) ||
          ((R \ K).toList.map term).any (fun t => taTerm t x)))
    (hcost : ∀ w ∈ R \ K, taTermCost (term w) ≤ if w ∈ A then 1 else 0)
    (hbudget : P.size + R.card + A.card ≤ C.size + 1) : K.card ≤ 1 := by
  classical
  by_contra hlarge
  have hk : 2 ≤ K.card := by omega
  obtain ⟨v, vs, hv⟩ : ∃ v vs, K.toList.map partner = v :: vs := by
    cases hl : K.toList.map partner with
    | nil =>
      have hh := congrArg List.length hl
      simp only [List.length_map, Finset.length_toList, List.length_nil] at hh
      omega
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hlen : vs.length + 1 = K.card := by
    have hh := congrArg List.length hv
    simpa only [List.length_map, Finset.length_toList, List.length_cons] using hh.symm
  let ts := (R \ K).toList.map term
  have htlen : ts.length + K.card = R.card := by
    simpa only [ts, List.length_map, Finset.length_toList] using Finset.card_sdiff_add_card_eq_card hKR
  have hsum : (ts.map taTermCost).sum ≤ (A \ K).card := by
    have he : (ts.map taTermCost).sum = ∑ w ∈ R \ K, taTermCost (term w) := by
      simp [ts, List.map_map]
    rw [he]
    calc
      _ ≤ ∑ w ∈ R \ K, if w ∈ A then 1 else 0 := Finset.sum_le_sum hcost
      _ = ((R \ K).filter (fun w => w ∈ A)).card := by
        simp
        congr 1
      _ ≤ (A \ K).card := Finset.card_le_card (by
        intro w hw
        obtain ⟨hw, ha⟩ := Finset.mem_filter.mp hw
        exact Finset.mem_sdiff.mpr ⟨ha, (Finset.mem_sdiff.mp hw).2⟩)
  have hacard : (A \ K).card + K.card = A.card := Finset.card_sdiff_add_card_eq_card hKA
  obtain ⟨D, hdm, hdr, hds, hdf⟩ := taFactorCircuit n P hm hr u v vs ts
  have heq : circuitFun n D = circuitFun n C := by
    funext z
    rw [hdf z, hsem z, hv]
  have hle := hmin D hdm hdr heq
  omega

def raPrefix (C : Circuit) (p : ℕ) : Circuit := ⟨C.gates.take p, C.output⟩

lemma raPrefix_size (C : Circuit) (p : ℕ) (hp : p ≤ C.gates.length) :
    (raPrefix C p).size = p := List.length_take_of_le hp

lemma raPrefix_mono (C : Circuit) (p : ℕ) (hm : Monotone2 C) : Monotone2 (raPrefix C p) := by
  intro g hg
  exact hm g (List.mem_of_mem_take hg)

lemma raPrefix_reads (n : ℕ) (C : Circuit) (p : ℕ) (hr : ReadsBack n C) :
    ReadsBack n (raPrefix C p) := by
  intro k hk a ha
  change k < (C.gates.take p).length at hk
  have hks : k < min p C.gates.length := by simpa [raPrefix] using hk
  have hkp := (lt_min_iff.mp hks).1
  have hkc := (lt_min_iff.mp hks).2
  have he : gateAt (raPrefix C p) k = gateAt C k := by
    change (C.gates.take p).getD k _ = C.gates.getD k _
    rw [List.getD_eq_getElem (C.gates.take p) _ hk, List.getD_eq_getElem C.gates _ hkc]
    simp

  exact hr k hkc a (he ▸ ha)

lemma raPrefix_wire (n : ℕ) (C : Circuit) (p : ℕ) (hp : p ≤ C.gates.length)
    (z : Fin n → Bool) (w : ℕ) (hw : w < n + p) :
    ((raPrefix C p).wires (List.ofFn z)).getD w false =
      (C.wires (List.ofFn z)).getD w false := by
  have hs : C.gates = C.gates.take p ++ C.gates.drop p := (List.take_append_drop p C.gates).symm
  change ((C.gates.take p).foldl decStep (List.ofFn z)).getD w false =
    (C.gates.foldl decStep (List.ofFn z)).getD w false
  conv_rhs => rw [hs, List.foldl_append]
  symm
  apply lcRead
  simpa only [lcLength, List.length_ofFn, List.length_take_of_le hp] using hw

noncomputable def raTailAnd (n : ℕ) (C : Circuit) (p : ℕ) : Finset ℕ := by
  classical
  exact (((Finset.range (C.gates.length - p)).filter
    (fun i => (gateAt C (p + i)).op = GateOp.and)).image (fun i => n + (p + i)))

lemma raTailAnd_mem (n : ℕ) (C : Circuit) (p w : ℕ) :
    w ∈ raTailAnd n C p ↔ ∃ k, p ≤ k ∧ k < C.gates.length ∧
      (gateAt C k).op = GateOp.and ∧ w = n + k := by
  classical
  constructor
  · intro hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hi, hop⟩ := Finset.mem_filter.mp hi
    have hi' := Finset.mem_range.mp hi
    exact ⟨p + i, by omega, by omega, hop, rfl⟩
  · rintro ⟨k, hkp, hk, hop, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨k - p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, ?_⟩
    · simpa only [Nat.add_sub_of_le hkp] using hop
    · omega

lemma raTailAnd_budget (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (p : ℕ) (hp : p ≤ C.gates.length) :
    (raPrefix C p).size + (otFrontier n C p).card + (raTailAnd n C p).card ≤ C.size + 1 := by
  classical
  let S := Finset.range (C.gates.length - p)
  let A := S.filter (fun i => (gateAt C (p + i)).op = GateOp.and)
  let O := S.filter (fun i => (gateAt C (p + i)).op = GateOp.or)
  have hdis : Disjoint A O := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have ha := (Finset.mem_filter.mp hi).2
    have ho := (Finset.mem_filter.mp hj).2
    rw [ha] at ho
    cases ho
  have hunion : A ∪ O = S := by
    ext i
    simp only [A, O, Finset.mem_union, Finset.mem_filter]
    constructor
    · tauto
    · intro hi
      have hk : p + i < C.gates.length := by
        have hh := Finset.mem_range.mp hi
        omega
      have hg : gateAt C (p + i) ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ hk]
        exact List.getElem_mem hk
      rcases (hm _ hg).1 with ha | ho
      · exact Or.inl ⟨hi, ha⟩
      · exact Or.inr ⟨hi, ho⟩
  have hsum : A.card + O.card = C.gates.length - p := by
    rw [← Finset.card_union_of_disjoint hdis, hunion]
    exact Finset.card_range _
  have ha : (raTailAnd n C p).card = A.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    change n + (p + a) = n + (p + b) at hab
    omega
  have hr := otFrontier_card n C hm p hp
  change (otFrontier n C p).card ≤ O.card + 1 at hr
  rw [raPrefix_size C p hp, ha]
  change p + (otFrontier n C p).card + A.card ≤ C.gates.length + 1
  omega

noncomputable def raReaderRoots (n : ℕ) (C : Circuit) (j : ℕ) : Finset ℕ := by
  classical
  exact (otFrontier n C (j + 1)).filter (fun w =>
    w ∈ raTailAnd n C (j + 1) ∧ n + j ∈ (gateAt C (w - n)).inputs)

lemma raMinimumReaderCard (n : ℕ) (C : Circuit) (hm : Monotone2 C) (hr : ReadsBack n C)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length)
    (hout : C.output < n + C.gates.length)
    (hd : frDirty n (fun z => circuitFun n C z = false) C j)
    (hlast : ∀ k < C.gates.length,
      frDirty n (fun z => circuitFun n C z = false) C k → k ≤ j) :
    (raReaderRoots n C j).card ≤ 1 := by
  classical
  let p := j + 1
  have hp : p ≤ C.gates.length := hj
  let P := raPrefix C p
  have hPs : P.size = p := raPrefix_size C p hp
  let R := otFrontier n C p
  let A := raTailAnd n C p
  let K := raReaderRoots n C j
  have hKR : K ⊆ R := Finset.filter_subset _ _
  have hKA : K ⊆ A := by
    intro w hw
    exact (Finset.mem_filter.mp hw).2.1
  let u : Fin (n + P.size) := ⟨n + j, by rw [hPs]; dsimp [p]; omega⟩
  have hpartners : ∀ w : ℕ, ∃ v : Fin (n + P.size), w ∈ K →
      ∀ z : Fin n → Bool,
        (C.wires (List.ofFn z)).getD w false =
          ((P.wires (List.ofFn z)).getD u false && (P.wires (List.ofFn z)).getD v false) := by
    intro w
    by_cases hw : w ∈ K
    · obtain ⟨k, hkp, hk, hop, hwk⟩ := (raTailAnd_mem n C p w).mp (hKA hw)
      subst w
      have hread : n + j ∈ (gateAt C k).inputs := by
        simpa using (Finset.mem_filter.mp hw).2.2
      obtain ⟨a, ha, _, hin⟩ := frMinimumLatestReaders n C hm hr hmin j hd hlast k hk hread
      let v : Fin (n + P.size) := ⟨a, by rw [hPs]; dsimp [p]; omega⟩
      refine ⟨v, fun _ z => ?_⟩
      change (C.wires (List.ofFn z)).getD (n + k) false =
        (((raPrefix C p).wires (List.ofFn z)).getD (n + j) false &&
          ((raPrefix C p).wires (List.ofFn z)).getD a false)
      rw [raPrefix_wire n C p hp z (n + j) (by dsimp [p]; omega),
        raPrefix_wire n C p hp z a (by dsimp [p]; omega), frGateEval n C hr k hk z, hop]
      rcases hin with hin | hin <;> simp [hin, GateOp.eval, Bool.and_comm]
    · exact ⟨u, fun h => (hw h).elim⟩
  choose partner hpartner using hpartners
  have hterms : ∀ w : ℕ,
      ∃ t : Fin (n + P.size) ⊕ (Fin (n + P.size) × Fin (n + P.size)),
        w ∈ R →
          (∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD w false =
            taTerm t (fun i => (P.wires (List.ofFn z)).getD i false)) ∧
          taTermCost t ≤ if w ∈ A then 1 else 0 := by
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
          simp [taTermCost, hwA]
    · exact ⟨.inl u, fun h => (hw h).elim⟩
  choose term hterm using hterms
  apply raFiniteFactor n C P (raPrefix_mono C p hm) (raPrefix_reads n C p hr)
    hmin R A K hKR hKA u partner term
  · intro z
    rw [otFrontier_semantics n C hr p hp z]
    rw [Bool.eq_iff_iff, ofAny_true, Bool.or_eq_true]
    simp only [List.any_map, List.any_eq_true, Finset.mem_toList]
    constructor
    · rintro ⟨w, hw, ht⟩
      by_cases hk : w ∈ K
      · exact Or.inl ⟨w, hk, (hpartner w hk z).symm.trans ht⟩
      · exact Or.inr ⟨w, Finset.mem_sdiff.mpr ⟨hw, hk⟩, ((hterm w hw).1 z).symm.trans ht⟩
    · rintro (⟨w, hw, ht⟩ | ⟨w, hw, ht⟩)
      · exact ⟨w, hKR hw, (hpartner w hw z).trans ht⟩
      · exact ⟨w, (Finset.mem_sdiff.mp hw).1,
          ((hterm w (Finset.mem_sdiff.mp hw).1).1 z).trans ht⟩
  · intro w hw
    exact (hterm w (Finset.mem_sdiff.mp hw).1).2
  · exact raTailAnd_budget n C hm p hp

end PEqualNP.Outside.L_meta_3451
