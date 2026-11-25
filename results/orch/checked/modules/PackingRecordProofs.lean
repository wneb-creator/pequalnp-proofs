import PackingFamilyProofs
import PackingMaskProofs
import PackingTraceProofs

namespace PEqualNP.Outside.L_meta_1896_aux.PackingRecords

open PackingThree

variable {V R I : Type*} [DecidableEq V] [DecidableEq I]

lemma list_pairwise_from_family (relation : I → I → Prop) (indices : List I)
    (hn : indices.Nodup)
    (hrel : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j → relation i j) :
    indices.Pairwise relation := by
  induction indices with
  | nil => exact List.Pairwise.nil
  | cons i tail ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
    apply List.pairwise_cons.mpr
    constructor
    · intro j hj
      apply hrel i (by simp) j (by simp [hj])
      intro he
      subst j
      exact hnot hj
    · apply ih htail
      intro j hj k hk hne
      exact hrel j (by simp [hj]) k (by simp [hk]) hne

lemma touchCount_map (data : I → Block) (indices : List I) (k : Nat) :
    touchCount (indices.map data) k =
      (indices.filter fun i => (data i).active.testBit k).length := by
  induction indices with
  | nil => rfl
  | cons i tail ih =>
    simp only [List.map_cons, touchCount_cons]
    cases h : (data i).active.testBit k <;> simp [h, ih, Nat.add_comm]

lemma filtered_length_eq_card (indices : List I) (hn : indices.Nodup) (p : I → Bool) :
    (indices.filter p).length = (indices.toFinset.filter fun i => p i = true).card := by
  rw [← List.toFinset_card_of_nodup (hn.filter _)]
  congr 1
  ext i
  simp

lemma validTrace_of_family (vertices : I → Finset V) (rows : R → V → Bool)
    (data : I → Block) (vcode : V → Nat) (rcode : R → Nat)
    (hvinj : Function.Injective vcode) (hrinj : Function.Injective rcode)
    (hvbits : ∀ i k, (data i).vertices.testBit k = true ↔ ∃ v ∈ vertices i, vcode v = k)
    (hrbits : ∀ i k, (data i).active.testBit k = true ↔
      ∃ r : R, rcode r = k ∧ ∃ v ∈ vertices i, rows r v = true)
    (indices : List I) (hn : indices.Nodup)
    (hvalid : PackingFamilies.Valid vertices rows 3 indices.toFinset) :
    PackingPrunedDFS.validTrace ok step emptyState (indices.map data) = true := by
  classical
  apply validTrace_of_packing
  · rw [List.pairwise_map]
    apply list_pairwise_from_family _ indices hn
    intro i hi j hj hij
    apply trace_and_zero
    intro k hk
    obtain ⟨v, hv, hvk⟩ := (hvbits i k).mp hk.1
    obtain ⟨w, hw, hwk⟩ := (hvbits j k).mp hk.2
    have hvw : v = w := hvinj (hvk.trans hwk.symm)
    subst w
    have hd := hvalid.1 (List.mem_toFinset.mpr hi) (List.mem_toFinset.mpr hj) hij
    exact Finset.disjoint_left.mp hd hv hw
  · intro k
    rw [touchCount_map, filtered_length_eq_card indices hn]
    by_cases hex : ∃ r : R, rcode r = k
    · obtain ⟨r, hr⟩ := hex
      have heq (i : I) : (data i).active.testBit k = true ↔
          ∃ v ∈ vertices i, rows r v = true := by
        rw [hrbits]
        constructor
        · rintro ⟨r', hr', hv⟩
          have he : r' = r := hrinj (hr'.trans hr.symm)
          exact he ▸ hv
        · intro hv
          exact ⟨r, hr, hv⟩
      simpa only [heq] using hvalid.2 r
    · have hf (i : I) : (data i).active.testBit k ≠ true := by
        intro ht
        obtain ⟨r, hr, hv⟩ := (hrbits i k).mp ht
        exact hex ⟨r, hr⟩
      simp [hf]

lemma covered_eq_removed (vertices : I → Finset V) (flags : Fin 52 → V → Bool)
    (data : I → Block)
    (hebits : ∀ i a, (data i).edges.testBit a.val = true ↔
      ∃ v ∈ vertices i, flags a v = true)
    (indices : List I) :
    flagCount (traceState (indices.map data)).covered =
      (PackingFamilies.removed vertices flags indices.toFinset).card := by
  classical
  unfold flagCount PackingFamilies.removed
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (indices.map data |>.foldl step emptyState).covered.testBit a.val = true ↔ _
  rw [fold_covered, upperEdges_testBit]
  simp only [emptyState, Nat.zero_testBit, Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨b, hb, hbit⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    obtain ⟨v, hv, hflag⟩ := (hebits i a).mp hbit
    exact ⟨v, Finset.mem_biUnion.mpr ⟨i, List.mem_toFinset.mpr hi, hv⟩, hflag⟩
  · rintro ⟨v, hv, hflag⟩
    obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
    refine ⟨data i, List.mem_map.mpr ⟨i, List.mem_toFinset.mp hi, rfl⟩, ?_⟩
    exact (hebits i a).mpr ⟨v, hvi, hflag⟩

lemma good_iff_removed_bound (vertices : I → Finset V) (flags : Fin 52 → V → Bool)
    (data : I → Block)
    (hebits : ∀ i a, (data i).edges.testBit a.val = true ↔
      ∃ v ∈ vertices i, flags a v = true)
    (indices : List I) (hn : indices.Nodup) :
    good (traceState (indices.map data)) = true ↔
      (PackingFamilies.removed vertices flags indices.toFinset).card ≤ 29 + indices.toFinset.card := by
  rw [good, decide_eq_true_eq, trace_count, List.length_map,
    covered_eq_removed vertices flags data hebits indices, List.toFinset_card_of_nodup hn]

end PEqualNP.Outside.L_meta_1896_aux.PackingRecords
